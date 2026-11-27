#!/usr/bin/env python3
"""The task list and its dependency graph (the plan), and the GitHub issues that track progress.

    python3 scripts/tasks.py generate           write docs/tasks/tasks.yaml, docs/tasks/README.md, Tasks.lean
                                                and the task counts in ROADMAP.md and README.md
    python3 scripts/tasks.py check              fail if a task file breaks the rules or a generated file is stale
    python3 scripts/tasks.py status             counts by area, kind, size and difficulty
    python3 scripts/tasks.py lock T-QU1-P5 ...  record locked statement hashes (after review)
    python3 scripts/tasks.py deps [--check]     write the header of each proof task's file
    python3 scripts/tasks.py drafts             the issue body of every task, in task-drafts/
    python3 scripts/tasks.py sync [--apply]     bring the task issues up to date (.github/workflows/tasks.yml)

Inputs: the milestone tables of docs/tasks/milestones.md (its three groups of areas) and
docs/tasks/decomposition.yaml. There are three kinds of task:
  T-<M>       one per milestone: its definitions, its theorems and their proofs. Its trust checks
              and a non-vacuity example are part of its definition of done.
  T-<M>-P<k>  proof tasks (decomposition.yaml): one lemma each, stated in its own file in Tasks/.
  upstream    results to contribute to Mathlib or Physlib (decomposition.yaml).

The repository holds the plan only; nothing in it records who works on what or what is finished.
Progress lives on GitHub: each task has an issue, found by the task ID in its title. A task is done
when its issue is closed as completed; a proof task is also done once its declaration has no sorry
on main, and `sync` then closes its issue. A task is ready when every task it needs is done; a
proof task counts once its statement is locked, and a milestone listed under `stated` in
decomposition.yaml (all its statements are proof tasks) once all its proof tasks are locked, so
work may build on a result whose proof is still open. `sync` reads the issues, their comments
(`claiming`, `attempting`, `stopping`) and the pull requests that name a task (`Task: T-...`), and
sets the labels ready, blocked, claimed, attempting and in review, assigns claimants, lets claims
lapse, and opens the issue of each proof task that becomes ready. On a milestone's issue it writes
only the claim labels (claimed, attempting) and the assignees: scripts/sync_github.py opens the
milestone issues, writes their status, area and size labels, and closes a milestone's issue once
its checklist is fully ticked. It prints what it would do unless given `--apply`."""
import argparse, datetime, importlib.util, json, pathlib, re, subprocess, sys, tempfile, textwrap, time
from collections import Counter, OrderedDict

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import leansrc  # noqa: E402
import proof_task_check as ptc  # noqa: E402

DECOMP, OUT_YAML, OUT_MD, OUT_LEAN = ("docs/tasks/decomposition.yaml", "docs/tasks/tasks.yaml",
                                      "docs/tasks/README.md", "Tasks.lean")
CHECKLISTS = "docs/tasks/checklists.yaml"  # per milestone: issue, ranking, checklist (v1.0)
BOARD = "docs/tasks/board.yaml"  # the repository whose issues track the tasks, and label colours
DEPS_HEAD = "## What the statement uses"  # section of each proof task's header, written by `deps`
LEMMAS_SHOWN = 8
TEMPLATE = "scripts/templates/proof-task-issue.md"
SECTIONS = ("Gravity and cosmology", "Mathematical and QFT foundations", "Approaches to quantum gravity")
TIER = dict(zip(SECTIONS, ("established", "established", "frontier")))  # by group of areas
# milestones whose tier differs from their group: textbook material inside a frontier area
TIER_OVERRIDE = {"ST1": "established", "SF3": "established"}
ROADMAP_COUNT = "- **Milestones:**"  # ROADMAP.md lines whose count `generate` keeps current
DONE_LINK = " · [done]("  # and the link to their closed issues that it appends to those lines
README_KINDS = "The plan has "  # README.md paragraph whose counts `generate` keeps current
SIZES = ["XS", "S", "M", "L", "R"]
DIFFICULTIES = ["good first issue", "intermediate", "advanced", "research-level"]
TARGETS = ["Mathlib", "Physlib"]  # libraries that upstream tasks contribute to
KINDS = ["milestone", "proof", "upstream"]
KIND_LABEL = {"milestone": "milestone", "proof": "proof-task", "upstream": "upstream"}
UNLOCKED = "the statement awaits review and locking"
# Labels that `sync` sets from the state of each task; it adds and removes only these.
LIVE = ["ready", "blocked", "claimed", "attempting", "in review"]
# On a milestone's issue `sync` writes only the claim labels: scripts/sync_github.py opens and edits
# those issues and writes their status, area and size labels (owner, 25 Nov 2026: one writer per
# label family). Neither touches the other's labels, and neither closes a milestone's issue.
CLAIM_LABELS = ["claimed", "attempting"]
MARK = "<!-- tasks.py sync: {} -->"  # hidden marker of each comment `sync` posts, so it posts once
CONVENTIONS = "docs/CONVENTIONS.md"
CLAIM_HOURS = 48  # a claim lasts this long, or while a pull request naming the task is open
MAX_CLAIMS = 3  # open claims per person
SOURCES = "docs/tasks/sources.yaml"  # literature sources per milestone (scripts/sources.py)
VERIFIED = "docs/tasks/sources-verified.json"
STRUCTURAL = ("upstream",)  # kinds that need no literature source
SOURCE_CLASSES = ["sourced", "structural", "exploratory"]
# Priority within an area, in this order: milestones citing one of the area's canonical sources,
# then highly cited sources, then milestones that many others need, then recent sources.
BASES = ["canonical", "highly cited", "unlocks many", "recent", "other"]
CITED, UNLOCKS, RECENT = 300, 5, 2015  # citation count, milestones transitively unlocked, year

BULLET = re.compile(r"^- \*\*(?P<id>[^*]+?),? done when:?\*\*\s*(?:\((?P<note>[^)]*)\))?:?\s*(?P<text>.*)$")
TRUST = re.compile(r"[Tt]rust checks?(?: \([^)]*\))?:\s*(?P<t>.*)$", re.S)
RANGE = re.compile(r"([A-Za-z]+)(\d+)\s*[–-]\s*\1?(\d+)")
MILESTONE_ID = re.compile(r"[A-Za-z][A-Za-z0-9]*")
LOOKS_LIKE_ID = re.compile(r"[A-Z]{1,4}\d+[a-z]?")
TASK_ID = r"T-[A-Za-z0-9]+(?:-[A-Za-z0-9]+)?"  # T-GE1, T-SF5a, T-QU1-P5, T-UP-1
TASK_LINE_ANY = re.compile(rf"^\s*Task:\s*({TASK_ID})\b", re.M)
# `/claim` and `/unclaim` are the commands; the words `claiming`, `attempting` and `stopping` are aliases.
CLAIM = re.compile(r"^\s*(?:/claim|claiming|attempting)\b", re.I | re.M)
RELEASE = re.compile(r"^\s*(?:/unclaim|stopping|releasing|unclaiming|no longer attempting)\b", re.I | re.M)


def natural(s):
    return [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", s)]


def yaml_load(text):
    import yaml
    return yaml.safe_load(text)


# --- Milestones ----------------------------------------------------------------------------------

def cells(line):
    parts = re.split(r"(?<!\\)\|", line.strip())
    if len(parts) < 3:
        return None
    return [p.strip().replace("\\|", "|") for p in parts[1:-1]]


def split_top(text, seps):
    """Split at separators outside brackets and backticks."""
    out, cur, depth, tick = [], [], 0, False
    for ch in text:
        if ch == "`":
            tick = not tick
        elif not tick and ch in leansrc.OPEN:
            depth += 1
        elif not tick and ch in leansrc.CLOSE:
            depth -= 1
        if ch in seps and depth == 0 and not tick:
            out.append("".join(cur))
            cur = []
            continue
        cur.append(ch)
    out.append("".join(cur))
    return [s.strip().rstrip(".").strip() for s in out if s.strip().rstrip(".").strip()]


def first_sentence(text):
    depth, tick = 0, False
    for i, ch in enumerate(text):
        if ch == "`":
            tick = not tick
        elif not tick and ch in leansrc.OPEN:
            depth += 1
        elif not tick and ch in leansrc.CLOSE:
            depth -= 1
        elif ch == "." and not depth and not tick and re.match(r"\s+[A-Z]", text[i + 1:i + 3]):
            return text[:i]
    return text


def parse_needs(cell, known, aliases):
    """(milestone dependencies, other prerequisites) of a Needs cell."""
    deps, ext = [], []
    for tok in split_top(cell, ","):
        tok = aliases.get(tok, tok)
        if tok == "-":
            continue
        alts = [aliases.get(a, a) for a in re.split(r"\s+or\s+", tok)]
        if len(alts) > 1:
            if all(a in known for a in alts):
                deps.append(alts[0])
            else:
                ext.append(tok)  # an alternative outside the milestones: recorded, not a dependency
            continue
        r = RANGE.fullmatch(tok)
        ids = [f"{r[1]}{i}" for i in range(int(r[2]), int(r[3]) + 1)] if r else [tok]
        for i in ids:
            (deps if i in known else ext).append(i)
    return deps, ext


def parse_roadmap(text, cfg):
    """The milestones of the area tables, in order, as an OrderedDict id -> milestone."""
    areas, aliases = cfg.get("areas") or {}, cfg.get("aliases") or {}
    rows, bullets = [], {}
    h2 = h3 = header = bullet = None
    for no, line in enumerate(text.split("\n"), 1):
        if bullet is not None:
            if line.startswith("  ") and line.strip():
                bullets[bullet] += " " + line.strip()
                continue
            bullet = None
        if line.startswith("## "):
            h2, h3, header = line[3:].strip(), None, None
            continue
        if line.startswith("### "):
            h3, header = line[4:].strip(), None
            continue
        m = BULLET.match(line)
        if m:
            bullet = aliases.get(m["id"].strip(), m["id"].strip())
            bullets[bullet] = m["text"].strip()
            continue
        c = cells(line) if line.startswith("|") else None
        if c is None:
            header = None
            continue
        if header is None:
            if c[0] in ("ID", "Milestone") and "Size" in c:
                header = c
            continue
        if all(set(x) <= set("-: ") for x in c) or h2 not in SECTIONS:
            continue
        if len(c) != len(header):
            raise ValueError(f"milestones.md:{no}: {len(c)} cells, its header has {len(header)}")
        rows.append(dict(zip(header, c), _id=c[0], _hdr=header[0], _line=no, _h2=h2, _h3=h3))
    ms = OrderedDict()
    for r in rows:
        mid = aliases.get(r["_id"], r["_id"])
        if r["_h3"] not in areas:
            raise ValueError(f"milestones.md:{r['_line']}: section {r['_h3']!r} has no area in {DECOMP}")
        if not MILESTONE_ID.fullmatch(mid):
            raise ValueError(f"milestones.md:{r['_line']}: milestone {mid!r} needs an alias in {DECOMP}")
        sizes = re.findall(r"\b(XS|S|M|L|R)\b", r.get("Size", ""))
        ms[mid] = dict(id=mid, title=r["Milestone"] if r["_hdr"] == "ID" else r.get("Content", ""),
                       area=areas[r["_h3"]], section=r["_h3"], group=r["_h2"], line=r["_line"],
                       size=max(sizes, key=SIZES.index) if sizes else "M",
                       needs_raw=r.get("Needs"), done_when=r.get("Done when", ""),
                       trust_raw=r.get("Trust checks", ""))
    known = set(ms)
    for m in ms.values():
        b = bullets.get(m["id"], "")
        raw = m.pop("needs_raw")
        if raw is None:
            m["needs"], m["external"] = list((cfg.get("needs") or {}).get(m["id"], [])), []
        else:
            m["needs"], m["external"] = parse_needs(raw, known, aliases)
        if not m["done_when"] or m["done_when"] == "below":
            m["done_when"] = first_sentence(TRUST.split(b)[0].rstrip("; ")) if b else ""
        m["trust"] = trust_checks(m.pop("trust_raw"), b)
    return ms


def trust_checks(cell, bullet):
    raw, from_bullet = cell, False
    if raw.strip().lower() in ("", "below", "-", "none"):
        t = TRUST.search(bullet)
        raw, from_bullet = (first_sentence(t["t"]) if t else ""), True
    parts = split_top(raw, ";")
    if from_bullet and len(parts) == 1 and ", and " in raw:
        parts = [p[4:] if p.startswith("and ") else p for p in split_top(raw, ",")]
    return parts


# --- Decomposition ----------------------------------------------------------------------------

def decompose(ms, cfg):
    hand_by = OrderedDict()
    for h in cfg.get("tasks") or []:
        if h["milestone"] not in ms:
            raise ValueError(f"{DECOMP}: {h['id']}: milestone {h['milestone']} is not a milestone")
        hand_by.setdefault(h["milestone"], []).append(h)
    tasks = []
    for m in ms.values():
        mid = m["id"]
        base = dict(milestone=mid, area=m["area"], msize=m["size"])
        tasks.append(dict(base, id=f"T-{mid}", kind="milestone", size=m["size"], title=m["title"],
                          deps=[f"T-{n}" for n in m["needs"]],
                          checks=list(m["trust"])))
        for h in hand_by.get(mid, []):
            t = dict(base, **{k: v for k, v in h.items() if k != "milestone"})
            t.setdefault("deps", [])
            tasks.append(t)
    areas = set((cfg.get("areas") or {}).values())
    for u in cfg.get("upstream") or []:
        miss = [k for k in ("id", "title", "target", "area", "size", "results", "rework") if not u.get(k)]
        if miss or u["area"] not in areas or u["target"] not in TARGETS:
            raise ValueError(f"{DECOMP}: upstream task {u.get('id')}: missing {', '.join(miss) or 'nothing'}; "
                             f"area must be one of the areas, target one of {', '.join(TARGETS)}")
        tasks.append(dict(u, kind="upstream", milestone=None, msize=u["size"], deps=list(u.get("deps") or [])))
    for t in tasks:
        t["difficulty"] = t.get("difficulty") or difficulty_for(t)
        t["mode"] = "non-exclusive" if t["kind"] == "proof" else "exclusive"
    return tasks


def difficulty_for(t):
    k, s, msz = t["kind"], t["size"], t["msize"]
    if msz == "R" and k in ("milestone", "proof"):
        return "research-level"
    if s == "XS":
        return "good first issue"
    return "intermediate" if s in ("S", "M") else "advanced"


def proven(text, decl):
    parts = ptc.split_block(text, decl.split(".")[-1]) if text is not None else None
    if parts is None:
        return False
    code = "".join(ch if c else " " for ch, c in zip(parts[2], leansrc.code_mask(parts[2])))
    return re.search(r"\bsorry\b", code) is None


def statement_key(header):
    """A theorem's statement with its keyword, name, docstring and whitespace removed: two
    theorems with the same key state the same thing (same binders, same type, same text)."""
    mask = leansrc.code_mask(header)
    code = "".join(ch if c else " " for ch, c in zip(header, mask))
    m = re.search(r"\b(?:theorem|lemma)\s+[\w.'«»]+", code)
    return re.sub(r"\s+", "", header[m.end():]) if m else None


def library_duplicates(tasks, root=ROOT):
    """{task ID: [(file, line, name)]}: open proof tasks whose statement is already a theorem of the
    library (Lightlike/), proven there. A task for it would duplicate work that exists. A task whose
    own `sorry` is filled is done, not a duplicate, and is skipped."""
    keys = {}
    for f in sorted((root / "Lightlike").rglob("*.lean")):
        lines = f.read_text().split("\n")
        for i, l in enumerate(lines):
            m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\s+([\w.'«»]+)", l)
            if not m:
                continue
            j = i + 1
            while j < len(lines) and not leansrc.COMMAND.match(lines[j]):
                j += 1
            parts = leansrc.split_header("\n".join(lines[i:j]))
            key = statement_key(parts[0]) if parts else None
            if key and parts and not re.search(r"\bsorry\b", parts[1]):
                keys.setdefault(key, []).append((str(f.relative_to(root)), i + 1, m.group(1)))
    found = {}
    for t in tasks:
        if t.get("kind") != "proof" or not t.get("file") or not (root / t["file"]).exists():
            continue
        text = (root / t["file"]).read_text()
        if proven(text, t["decl"]):
            continue
        parts = ptc.split_block(text, t["decl"].split(".")[-1])
        hits = keys.get(statement_key(parts[1])) if parts else None
        if hits:
            found[t["id"]] = hits
    return found


def duplicate_problems(tasks, root=ROOT):
    return [f"{tid}: its statement is already proven in {h[0][0]}:{h[0][1]} ({h[0][2]}); close the task as "
            f"proven instead of opening it" for tid, h in sorted(library_duplicates(tasks, root).items())]


def compute(tasks, ms, cfg, read):
    """Fill in lock and proven, and check the graph. `read(path)` returns a task file's text or None."""
    by = OrderedDict((t["id"], t) for t in tasks)
    if len(by) != len(tasks):
        dup = [i for i, n in Counter(t["id"] for t in tasks).items() if n > 1]
        raise ValueError(f"duplicate task IDs: {', '.join(dup)}")
    locked = cfg.get("locked") or {}
    for t in tasks:
        if t["id"] in locked:
            t["lock"] = str(locked[t["id"]])
        t["proven"] = bool(t.get("file")) and proven(read(t["file"]), t["decl"])
        for d in t["deps"]:
            if d not in by:
                raise ValueError(f"{t['id']} depends on {d}, which is not a task")
    for m in cfg.get("stated") or []:
        if not any(t["kind"] == "proof" and t["milestone"] == m for t in tasks):
            raise ValueError(f"{DECOMP}: stated milestone {m} has no proof tasks")
    cycle = find_cycle(by)
    if cycle:
        raise ValueError("dependency cycle: " + " -> ".join(cycle))
    return tasks


def progress(tasks, cfg, closed=()):
    """State of each task: {id: (state, blocked_by)}, state done, ready or blocked. `closed` holds
    the IDs of the tasks whose issue is closed as completed."""
    closed = set(closed)
    proofs = OrderedDict()
    for t in tasks:
        if t["kind"] == "proof":
            proofs.setdefault(t["milestone"], []).append(t)
    stated = set(cfg.get("stated") or [])

    def done(t):
        if t["id"] in closed or t["proven"]:
            return True
        return t["kind"] == "milestone" and t["milestone"] in stated and all(p["proven"] for p in proofs[t["milestone"]])

    by = {t["id"]: t for t in tasks}

    def met(d):
        x = by[d]
        if done(x) or (x["kind"] == "proof" and x.get("lock")):
            return True
        return (x["kind"] == "milestone" and x["milestone"] in stated
                and all(p.get("lock") or p["proven"] for p in proofs[x["milestone"]]))

    out = OrderedDict()
    for t in tasks:
        if done(t):
            out[t["id"]] = ("done", [])
            continue
        b = [UNLOCKED] if t["kind"] == "proof" and t.get("file") and not t.get("lock") else []
        b += [f"needs {d}" for d in t["deps"] if not met(d)]
        out[t["id"]] = ("blocked" if b else "ready", b)
    return out


def find_cycle(by):
    state, stack = {}, []

    def visit(i):
        state[i] = 1
        stack.append(i)
        for d in by[i]["deps"]:
            if state.get(d) == 1:
                return stack[stack.index(d):] + [d]
            if d not in state:
                c = visit(d)
                if c:
                    return c
        state[i] = 2
        stack.pop()
        return None

    for i in by:
        if i not in state:
            c = visit(i)
            if c:
                return c
    return None


def labels_for(t):
    out = [KIND_LABEL[t["kind"]]] + ([t["role"]] if t.get("role") else [])
    out += [f"area: {t['area']}", f"size: {t['size']}", t["difficulty"]]
    if t.get("target"):
        out.append(f"upstream: {t['target']}")
    return out


def ref_year(key):
    m = re.search(r"-((?:19|20)\d{2})[a-z]?$", key)
    return int(m.group(1)) if m else None


def short_location(loc):
    """A source location as cited: without its link, and none for an abstract."""
    loc = loc.split("|")[0].strip()
    if loc.startswith("Chapter: Chapter"):
        loc = loc[len("Chapter: "):]
    return "" if loc.lower() == "abstract" else loc


def add_sources(tasks, ms, root):
    """Source class, source and priority within the area for each task, from docs/tasks/sources.yaml."""
    f, v = root / SOURCES, root / VERIFIED
    src = yaml_load(f.read_text()) if f.exists() else {}
    ver = json.loads(v.read_text()) if v.exists() else {}
    canon, per = src.get("canonical") or {}, src.get("milestones") or {}
    needed_by = {}
    for m in ms.values():
        for n in m["needs"]:
            needed_by.setdefault(n, set()).add(m["id"])

    def unlocks(mid):
        seen, stack = set(), [mid]
        while stack:
            for x in needed_by.get(stack.pop(), ()):
                if x not in seen:
                    seen.add(x)
                    stack.append(x)
        return len(seen)

    info = {}
    for mid, m in ms.items():
        e = per.get(mid) or {}
        refs = e.get("refs") or []
        keys = [r["ref"] for r in refs]
        cites = max([(ver.get(k) or {}).get("citations") or 0 for k in keys], default=0)
        years = [y for y in map(ref_year, keys) if y]
        u = unlocks(mid)
        basis = ("canonical" if set(keys) & set(canon.get(m["area"]) or []) else "highly cited" if cites >= CITED
                 else "unlocks many" if u >= UNLOCKS else "recent" if years and min(years) >= RECENT else "other")
        info[mid] = dict(cls=e.get("class"), reason=e.get("reason"), refs=refs, basis=basis, cites=cites, unlocks=u,
                         year=min(years, default=0),
                         source="; ".join(", ".join(filter(None, (r["ref"], short_location(r["location"]))))
                                         for r in refs))
    for area in {m["area"] for m in ms.values()}:
        ids = sorted((i for i in ms if ms[i]["area"] == area), key=lambda i: (
            BASES.index(info[i]["basis"]), -info[i]["unlocks"], -info[i]["cites"], info[i]["year"], natural(i)))
        for k, i in enumerate(ids, 1):
            info[i]["rank"] = k
    for mid, m in ms.items():
        m["src"] = info[mid]
    for t in tasks:
        i = info.get(t["milestone"])
        if t["kind"] in STRUCTURAL:
            t["source_class"] = "structural"
            t["source"] = ("serves " + (t["milestone"] or ", ".join(t.get("results") or [])
                                        or "the library")).rstrip()
        elif i and i["cls"] in ("sourced", "exploratory"):
            t["source_class"] = i["cls"]
            t["source"] = i["source"] if i["cls"] == "sourced" else f"exploratory: {i['reason']}"
        else:
            t["source_class"], t["source"] = None, None
        if i:
            t["priority"], t["priority_basis"] = i["rank"], i["basis"]
    return info


def build(root=ROOT):
    cfg = yaml_load((root / DECOMP).read_text())
    ms = parse_roadmap((root / "docs/tasks/milestones.md").read_text(), cfg)
    tasks = decompose(ms, cfg)

    def read(p):
        f = root / p
        return f.read_text() if f.exists() else None

    compute(tasks, ms, cfg, read)
    add_sources(tasks, ms, root)
    group = {m["area"]: m["group"] for m in ms.values() if m.get("group") in TIER}
    for t in tasks:
        t["tier"] = TIER_OVERRIDE.get(t.get("milestone"), TIER[group[t["area"]]])
        t["labels"] = labels_for(t)
    add_checklists(tasks, ms, root)
    return cfg, ms, tasks


def in_v1(m, v1):
    """Whether milestone `m` is part of v1.0: its area and size are listed under `v1.0:` of
    docs/tasks/checklists.yaml (`v1`) and its ID is not under `later:` (scheduled after v1.0)."""
    return (m["area"] in (v1.get("areas") or []) and m["size"] in (v1.get("sizes") or [])
            and m["id"] not in (v1.get("later") or []))


def add_checklists(tasks, ms, root=ROOT):
    """From docs/tasks/checklists.yaml, onto each milestone task: `release` (v1.0 or not-scheduled),
    and the `issue`, `ranking` and `checklist` given there (scripts/milestone_status.py checks the
    format and computes the status)."""
    f = root / CHECKLISTS
    if not f.exists():
        return
    data = yaml_load(f.read_text()) or {}
    v1 = data.get("v1.0") or {}
    entries = data.get("milestones") or {}
    for t in tasks:
        if t["kind"] != "milestone":
            continue
        m, e = ms[t["milestone"]], entries.get(t["milestone"]) or {}
        t["release"] = "v1.0" if in_v1(m, v1) else "not-scheduled"
        for k, f2 in (("issue", "issue"), ("ranking", "ranking"), ("items", "checklist")):
            if e.get(k) not in (None, [], ""):
                t[f2] = e[k]


# --- Outputs ----------------------------------------------------------------------------------

FIELDS = ["id", "kind", "role", "target", "results", "rework", "title", "milestone", "area", "tier", "source_class", "source",
          "priority", "priority_basis", "size", "difficulty",
          "mode", "deps", "checks", "file", "decl", "routes", "lock", "release", "issue", "ranking", "labels",
          "checklist"]


def summary(tasks):
    return OrderedDict([
        ("tasks", len(tasks)),
        ("by_kind", dict(Counter(t["kind"] for t in tasks))),
        ("by_size", {s: n for s in SIZES for k, n in Counter(t["size"] for t in tasks).items() if k == s}),
        ("by_difficulty", {d: n for d in DIFFICULTIES
                           for k, n in Counter(t["difficulty"] for t in tasks).items() if k == d}),
        ("by_area", dict(Counter(t["area"] for t in tasks))),
        ("by_source_class", {c: n for c in SOURCE_CLASSES
                             for k, n in Counter(t["source_class"] for t in tasks).items() if k == c}),
        ("by_priority_basis", {b: n for b in BASES
                               for k, n in Counter(t.get("priority_basis") for t in tasks).items() if k == b}),
    ])


def to_yaml(tasks):
    j = lambda v: json.dumps(v, ensure_ascii=False)  # noqa: E731  (JSON scalars are valid YAML)
    out = ["# Generated by scripts/tasks.py from docs/tasks/milestones.md, decomposition.yaml and checklists.yaml.",
           "# Do not edit by hand.",
           "# The plan only: who works on a task, and whether it is done, is on its GitHub issue.",
           "summary:"]
    for k, v in summary(tasks).items():
        out.append(f"  {k}: {j(v)}")
    out.append("tasks:")
    for t in tasks:
        first = True
        for f in FIELDS:
            if f not in t or t[f] in (None, "") or (f == "routes" and not t[f]):
                continue
            if f == "checklist":  # one item per line
                out.append(("  - " if first else "    ") + f"{f}:")
                out.extend(f"      - {j(i)}" for i in t[f])
            else:
                out.append(("  - " if first else "    ") + f"{f}: {j(t[f])}")
            first = False
    return "\n".join(out) + "\n"


def tasks_lean(tasks):
    mods = sorted({t["file"][:-5].replace("/", ".") for t in tasks if t.get("file")}, key=natural)
    return ("".join(f"import {m}\n" for m in mods) +
            "\n/-! Task library: one file per open task (see `docs/tasks/README.md`). Not a default build\n"
            "target; build it with `lake build Tasks`. Generated by `scripts/tasks.py generate`. -/\n")


def md_cell(s, limit=None):
    s = s.replace("|", "\\|").replace("\n", " ")
    if limit and len(s) > limit:
        cut = s[:limit].rsplit(" ", 1)[0]
        if cut.count("`") % 2:
            cut = cut[:cut.rfind("`")].rstrip()
        s = cut + " …"
    return s


def md_table(head, rows):
    return "\n".join(["| " + " | ".join(head) + " |", "|" + "---|" * len(head)] +
                     ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]) + "\n"


def source_cell(t):
    src = t.get("source") or ""
    if t.get("source_class") == "sourced":
        return md_cell(", ".join(dict.fromkeys(r.split(",")[0] for r in src.split("; "))), 60)
    return "exploratory" if t.get("source_class") == "exploratory" else ""


def search(repo, q):
    """Link to a GitHub issue search of `repo`."""
    from urllib.parse import quote_plus
    return f"https://github.com/{repo}/issues?q=" + quote_plus("is:issue " + q)


def task_link(t, repo):
    """The task ID, linked to the search for its issue (the issue title starts with the ID)."""
    return f"[`{t['id']}`]({search(repo, 'in:title ' + chr(34) + t['id'] + chr(34))})"


def readme(tasks, ms, repo):
    sec = OrderedDict()
    for m in ms.values():
        sec.setdefault(m["area"], m["section"])
    order = lambda t: t.get("priority") or 10**6  # noqa: E731  (stable: keeps the roadmap order)
    miles = [t for t in tasks if t["kind"] == "milestone"]
    by_area = OrderedDict((a, sorted([t for t in miles if t["area"] == a], key=order)) for a in sec)
    by_area = OrderedDict((a, ts) for a, ts in by_area.items() if ts)
    proofs = [t for t in tasks if t["kind"] == "proof"]
    ups = sorted((t for t in tasks if t["kind"] == "upstream"), key=lambda t: natural(t["id"]))
    fill = lambda s, first="", rest="": textwrap.fill(  # noqa: E731
        s, 100, initial_indent=first, subsequent_indent=rest, break_on_hyphens=False,
        break_long_words=False)
    board = (f"- [Project board](https://github.com/orgs/{repo.split('/')[0]}/projects) \"Lightlike\": the plan, "
             "one issue per milestone in the columns Ready, In progress, Done and Not scheduled; "
             "the v1.0 milestones are taken in the order of its Rank")
    live = board + "\n" + "\n".join(f"- [{name}]({search(repo, q)}){': ' + what if what else ''}" for name, q, what in [
        ("Ready v1.0 milestones", 'is:open milestone:v1.0 label:"status: ready"', "nobody has claimed them"),
        ("Not scheduled", "is:open label:milestone no:milestone", "milestones outside v1.0, open to outside contributors"),
        ("Ready proof tasks", "is:open label:ready label:proof-task", "Lean only, no physics"),
        ("Ready good first issues", 'is:open label:ready label:"good first issue"', ""),
        ("Claimed", "is:open label:claimed", "the claimant is the assignee"),
        ("In review", 'is:open label:"in review"', "a pull request names the task"),
        ("Done", "is:closed reason:completed", "")])
    bullets = "\n".join(fill(b, "- ", "  ") for b in [
        "**[Proof tasks](#proof-tasks)** need Lean but no physics. Each is one lemma with a fixed "
        "statement, in its own file in `Tasks/`: replace the `sorry` with a proof.",
        "**[Milestones](#milestones-by-area)** are the steps of each area of the [roadmap](../../ROADMAP.md): "
        "definitions, statements and proofs that follow the cited literature. They need knowledge of the "
        "area.",
        "**[Upstream](#upstream)** tasks rework a result of Lightlike for Mathlib or Physlib."])
    where = fill(
        "Every milestone has one GitHub issue, and a proof task's issue is opened when the task becomes "
        "ready; the task's ID starts the issue's title, and the ID in the tables below links to it. The "
        "issue is where a task is claimed and discussed. A milestone's issue holds its checklist, ticked "
        "from `main` by `scripts/milestone_status.py` and written with its status label and board column "
        "by `scripts/sync_github.py` after every merge, which closes it once every item is ticked. "
        "The labels of a proof task's issue are set by a workflow (`.github/workflows/tasks.yml`) from "
        "the issue's comments and the pull requests that name the task, and it closes when the proof is "
        "on `main`. How to take a task, and how several people work on the same one, is in "
        "[CONTRIBUTING.md](../../CONTRIBUTING.md#working-on-the-same-problem).")
    ready_def = fill(
        "A proof task is **ready** when the tasks it needs are done; a needed proof task counts once its "
        "statement is locked, so a proof may use a lemma whose own proof is still open. A v1.0 milestone is ready "
        "when nobody holds it; the milestones it needs do not have to be closed first. What a finished "
        "milestone must "
        "satisfy is in "
        "[milestones.md](milestones.md#definition-of-done-every-milestone); the dependencies, sources and "
        "labels of every task are in [tasks.yaml](tasks.yaml).")
    order_text = fill(
        "The v1.0 milestones are taken in the order of their ranking (`ranking:` in "
        "[checklists.yaml](checklists.yaml), the Rank on the Project board): those that unblock other "
        "milestones first, each after the milestones it needs. Within an area, "
        "the milestones are listed in a suggested order, by their sources "
        "([sources.yaml](sources.yaml)): first those that follow the area's standard references, then those "
        f"with a source cited at least {CITED} times, then those that at least {UNLOCKS} other milestones "
        f"need, then those with sources from {RECENT} on, then the rest. The order suggests where to start; "
        "it does not rank the approaches.")
    parts = [f"""<!-- Generated by scripts/tasks.py from docs/tasks/milestones.md and decomposition.yaml. Do not edit by hand. -->
# Task board

Every task of Lightlike and what it needs. This page changes only when the plan changes; who is
working on what, and what is done, is on the Project board and the issues:

{live}

{bullets}

{where}

{ready_def}

## Order within an area

{order_text}

"""]
    if proofs:
        parts.append("## Proof tasks\n\n" + md_table(
            ["Task", "Statement", "File", "Milestone", "Size", "Difficulty"],
            [[task_link(t, repo), md_cell(t["title"], 110),
              f"[{t['file'].rsplit('/', 1)[-1]}](../../{t['file']})" if t.get("file") else "",
              t["milestone"], t["size"], t["difficulty"]] for t in proofs]) + "\n")
    if ups:
        parts.append("## Upstream\n\nResults to contribute to Mathlib or Physlib, with the rework "
                     "each needs ([tasks.yaml](tasks.yaml)).\n\n"
                     + md_table(["Task", "Target", "Results", "Title", "Size", "Needs"],
                                [[task_link(t, repo), t["target"], ", ".join(t["results"]), md_cell(t["title"], 110),
                                  t["size"], ", ".join(t["deps"])] for t in ups]) + "\n")
    parts.append("## Milestones by area\n\n" + " · ".join(f"[{sec[a]}](#{anchor(sec[a])})" for a in by_area)
                 + "\n\n")
    for a, ts in by_area.items():
        road = f"milestones.md#{anchor(sec[a])}"
        parts.append(f"### {sec[a]}\n\nDone-when texts and trust checks: [milestones.md]({road}).\n\n" + md_table(
            ["Task", "Title", "Source", "Size", "Difficulty", "Needs"],
            [[task_link(t, repo), md_cell(t["title"], 110), source_cell(t), t["size"], t["difficulty"],
              ", ".join(d[2:] for d in t["deps"])] for t in ts]) + "\n")
    return "".join(parts).rstrip("\n") + "\n"


def anchor(title):
    return re.sub(r"[^\w\- ]", "", title.lower()).replace(" ", "-")


def roadmap_counts(text, ms, repo="LightlikeProject/lightlike"):
    """ROADMAP.md with the milestone count of each area section brought up to date, and a link to
    the area's done milestones. A milestone is done when its issue is closed as completed; the link
    is that issue search, so ROADMAP.md shows what is done without a status column to keep."""
    out, title = [], None
    for line in text.split("\n"):
        if line.startswith("## "):
            title = None
        elif line.startswith("### "):
            title = line[4:].strip()
        elif line.startswith(ROADMAP_COUNT) and title:
            mine = [m for m in ms.values() if m["section"] == title]
            links = line.split(" ·", 1)[1].split(DONE_LINK, 1)[0]
            line = f"{ROADMAP_COUNT} {len(mine)} ·{links}"
            areas = {m["area"] for m in mine}
            if len(areas) == 1:
                q = f'is:closed reason:completed label:milestone label:"area: {areas.pop()}"'
                line += f"{DONE_LINK}{search(repo, q)})"
        out.append(line)
    return "\n".join(out)


def kinds_paragraph(tasks):
    """The README.md paragraph on the kinds of task: how many the plan has, and what each needs."""
    n = Counter(t["kind"] for t in tasks)
    return textwrap.fill(
        f"{README_KINDS}{len(tasks)} tasks, on the [task board](docs/tasks/README.md): {n['proof']} "
        "**proof tasks**, which need Lean but no physics, because the statement is fixed and only its proof "
        f"is open; {n['milestone']} **milestones**, which add definitions and statements from the literature "
        f"and need knowledge of their area; and {n['upstream']} **upstream** tasks, which rework a result of "
        "Lightlike for Mathlib or Physlib.", 100, break_on_hyphens=False, break_long_words=False)


def readme_kinds(text, tasks):
    """README.md with the paragraph that starts with README_KINDS brought up to date."""
    lines = text.split("\n")
    for i, line in enumerate(lines):
        if line.startswith(README_KINDS):
            j = i
            while j < len(lines) and lines[j].strip():
                j += 1
            return "\n".join(lines[:i] + [kinds_paragraph(tasks)] + lines[j:])
    return text


def changelog_counts(text, tasks, ms):
    """CHANGELOG.md with the counts of areas and tasks in its newest version brought up to date.
    Older versions keep the counts they were released with."""
    heads = [m.start() for m in re.finditer(r"^## \[", text, re.M)]
    if not heads:
        return text
    a, b = heads[0], heads[1] if len(heads) > 1 else len(text)
    sec = re.sub(r"^- \d+ areas in \[ROADMAP", f"- {len({m['area'] for m in ms.values()})} areas in [ROADMAP",
                 text[a:b], flags=re.M)
    sec = re.sub(r"^- \d+ tasks on the \[task board\]", f"- {len(tasks)} tasks on the [task board]", sec, flags=re.M)
    return text[:a] + sec + text[b:]


def outputs(tasks, ms, root=ROOT):
    repo = yaml_load((root / BOARD).read_text())["repo"] if (root / BOARD).exists() else "LightlikeProject/lightlike"
    road = {"ROADMAP.md": roadmap_counts((root / "ROADMAP.md").read_text(), ms, repo)} \
        if (root / "ROADMAP.md").exists() else {}
    if (root / "README.md").exists():
        road["README.md"] = readme_kinds((root / "README.md").read_text(), tasks)
    if (root / "CHANGELOG.md").exists():
        road["CHANGELOG.md"] = changelog_counts((root / "CHANGELOG.md").read_text(), tasks, ms)
    return {OUT_YAML: to_yaml(tasks), OUT_MD: readme(tasks, ms, repo), OUT_LEAN: tasks_lean(tasks), **road}


# --- Checks -----------------------------------------------------------------------------------

FORBIDDEN_TASK = re.compile(r"\b(sorry|admit|native_decide|axiom|implemented_by|extern)\b")


def namespaced(text, short):
    """Full name of the declaration `short`, from the namespaces open at its line."""
    loc = leansrc.find_decl(text, short)
    if loc is None:
        return None
    stack = []
    for line in text.split("\n")[:loc[0] + 1]:
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            stack.append(m[1])
        elif re.match(r"^end\s+\S+", line) and stack:
            stack.pop()
    m = re.search(rf"(?:theorem|lemma|def|abbrev)\s+([\w.'«»]*{re.escape(short)})(?![\w'.])",
                  "\n".join(text.split("\n")[loc[0]:loc[1]]))
    return ".".join(stack + [m[1] if m else short])


def check_task_files(files, tasks):
    """Problems in the Tasks/ files: `files` maps path -> text."""
    problems = []
    reg = {t["file"]: t for t in tasks if t.get("file")}
    for path in sorted(files, key=natural):
        if path not in reg:
            problems.append(f"{path}: not registered as a task in {DECOMP}")
            continue
        t, text = reg[path], files[path]
        if not re.search(r"-P\d+$", t["id"]):
            problems.append(f"{t['id']}: a proof task with a file needs an ID ending in -P<n>")
        parts = ptc.split_block(text, t["decl"].split(".")[-1])
        if parts is None:
            problems.append(f"{path}: declaration {t['decl']} not found exactly once")
            continue
        if namespaced(text, t["decl"].split(".")[-1]) != t["decl"]:
            problems.append(f"{path}: the declaration is {namespaced(text, t['decl'].split('.')[-1])}, "
                            f"not {t['decl']}")
        if not re.search(r"^(Source|Structural|Exploratory):", parts[0], re.M):
            problems.append(f"{path}: the header needs a `Source:` line (reference and location, from "
                            f"{SOURCES}) or a `Structural:` or `Exploratory:` line")
        outside = parts[0] + "\n" + parts[1] + "\n" + parts[3]
        code = "".join(ch if c else " " for ch, c in zip(outside, leansrc.code_mask(outside)))
        m = FORBIDDEN_TASK.search(code)
        if m:
            problems.append(f"{path}: `{m[1]}` outside the proof of {t['decl']}")
        proof = "".join(ch if c else " " for ch, c in zip(parts[2], leansrc.code_mask(parts[2])))
        m = re.search(r"\b(admit|native_decide|axiom|implemented_by|extern)\b", proof)
        if m:
            problems.append(f"{path}: the proof uses `{m[1]}`")
        if t.get("lock") and ptc.statement_hash(parts[1]) != t["lock"]:
            problems.append(f"{path}: the statement of {t['id']} does not match its lock {t['lock']}")
    for path in sorted(set(reg) - set(files)):
        problems.append(f"{path}: registered for {reg[path]['id']} but missing")
    return problems


def cmd_check(root=ROOT):
    problems = []
    cfg, ms, tasks = build(root)
    for path, text in outputs(tasks, ms, root).items():
        f = root / path
        if not f.exists() or f.read_text() != text:
            problems.append(f"{path} is stale (expected on a branch: the maintainers regenerate it after "
                            "merging; see scripts/generated.py)")
    files = {str(p.relative_to(root)): p.read_text() for p in sorted((root / "Tasks").rglob("*.lean"))}
    problems += check_task_files(files, tasks)
    lib = [root / "Lightlike.lean", *sorted((root / "Lightlike").rglob("*.lean"))]
    for f in lib:
        if f.exists() and re.search(r"^import Tasks\b", f.read_text(), re.M):
            problems.append(f"{f.relative_to(root)} imports the task library (only Tasks/ may)")
    problems += duplicate_problems(tasks, root)
    nosrc = [t["id"] for t in tasks if not t.get("source_class")]
    if nosrc:
        problems.append(f"{len(nosrc)} tasks have no source: give their milestone a `class: sourced` entry with "
                        f"refs, or `class: exploratory` with a reason, in {SOURCES} ({', '.join(nosrc[:5])}, ...)")
    unknown = sorted({e for m in ms.values() for e in m["external"] if LOOKS_LIKE_ID.fullmatch(e)})
    if unknown:
        problems.append("Needs entries that look like milestone IDs but match none: " + ", ".join(unknown))
    yaml_load((root / OUT_YAML).read_text()) if (root / OUT_YAML).exists() else None
    for p in problems:
        print("  - " + p)
    print(f"tasks check: {'OK' if not problems else 'FAILED'} ({len(tasks)} tasks)")
    return 1 if problems else 0


# --- Lock -------------------------------------------------------------------------------------

def cmd_lock(ids, root=ROOT):
    text = (root / DECOMP).read_text()
    cfg = yaml_load(text)
    hand = {t["id"]: t for t in cfg.get("tasks") or []}
    locked = dict(cfg.get("locked") or {})
    for i in ids:
        t = hand.get(i)
        if t is None or t.get("kind") != "proof" or not t.get("file"):
            print(f"tasks lock: {i} is not a hand-written proof task with a file")
            return 2
        parts = ptc.split_block((root / t["file"]).read_text(), t["decl"].split(".")[-1])
        if parts is None:
            print(f"tasks lock: {t['decl']} not found in {t['file']}")
            return 2
        locked[i] = ptc.statement_hash(parts[1])
        print(f"locked {i}: {locked[i]}")
    m = re.search(r"^locked:.*\Z", text, re.M | re.S)
    if m is None:
        print(f"tasks lock: no `locked:` section at the end of {DECOMP}")
        return 2
    body = "".join(f'  {k}: "{locked[k]}"\n' for k in sorted(locked, key=natural))
    (root / DECOMP).write_text(text[:m.start()] + ("locked:\n" + body if body else "locked: {}\n"))
    return cmd_generate(root)


def cmd_generate(root=ROOT):
    cfg, ms, tasks = build(root)
    out = outputs(tasks, ms, root)
    for path, text in out.items():
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_text(text)
    print(f"tasks: wrote {', '.join(out)} ({len(tasks)} tasks)")
    return 0


def cmd_status(root=ROOT):
    cfg, ms, tasks = build(root)
    print(json.dumps(summary(tasks), indent=1, ensure_ascii=False))
    return 0


# --- Issue drafts -----------------------------------------------------------------------------

def context_pack_module():
    import importlib.machinery
    loader = importlib.machinery.SourceFileLoader("context_pack", str(ROOT / "scripts" / "context-pack"))
    spec = importlib.util.spec_from_loader("context_pack", loader)
    mod = importlib.util.module_from_spec(spec)
    loader.exec_module(mod)
    return mod


def pack_sections(cp, p, budget):
    """(definitions, lemmas) text of a context pack, within `budget` characters, with a note
    listing what was left out."""
    items = [("d", cp.entry(d), d) for d in cp.dedupe(p["deps"])]
    items += [("l", cp.lemma_entry(l), l) for l in p["lemmas"]]
    out, used, omitted = {"d": [], "l": []}, 0, []
    for k, text, d in items:
        if used + len(text) + 1 > budget - 600:
            omitted.append(d)
            continue
        out[k].append(text)
        used += len(text) + 1
    lem = "\n".join(out["l"]) or "(none found)\n"
    if omitted:
        names = ", ".join(f"{d['name']} ({d['file']}:{d['line']})" for d in omitted)
        note = f"\n-- Truncated: {len(omitted)} entries left out to keep this prompt short: {names}\n"
        lem += note[:600]
    return "\n".join(out["d"]) or "(none: the statement uses only Mathlib and Physlib)\n", lem


def proof_card(t, by, ms, p, cp, template):
    text = (ROOT / t["file"]).read_text()
    front, body = template.split("---\n", 2)[1:]
    title = re.search(r'^title:\s*"(.*)"', front, re.M)[1]
    imports = " ".join(l[7:] for l in text.split("\n") if l.startswith("import "))
    m = ms[t["milestone"]]
    vals = {"id": t["id"], "title": t["title"], "size": t["size"], "difficulty": t["difficulty"],
            "area": t["area"],
            "file": t["file"], "decl": t["decl"], "module": t["file"][:-5].replace("/", "."),
            "milestone": f"{m['id']} ({m['section']})" + milestone_issue(by, m["id"]),
            "deps": ", ".join(t["deps"]) or "none",
            "routes": "\n".join(f"{i}. {r}" for i, r in enumerate(t.get("routes") or [], 1))
                      or "No route documented yet; share yours in this thread.",
            "imports": imports, "statement": text.rstrip(),
            "lock": f"locked (hash `{t['lock']}`)" if t.get("lock") else "not locked yet"}
    vals["lean"], vals["mathlib"], vals["physlib"] = [x.split(" ", 1)[1] for x in cp.versions().split(", ")]
    rest = body
    for k, v in vals.items():
        rest = rest.replace("{{" + k + "}}", v)
    budget = cp.DEFAULT_MAX - len(rest)
    defs, lems = pack_sections(cp, p, budget) if p else (
        f"(not included: `scripts/context-pack {t['decl']}` prints them)\n",) * 2
    rest = rest.replace("{{definitions}}", defs.rstrip()).replace("{{lemmas}}", lems.rstrip())
    for k, v in vals.items():
        title = title.replace("{{" + k + "}}", v)
    left = re.findall(r"\{\{\w+\}\}", rest)
    if left:
        raise ValueError(f"{t['id']}: unfilled placeholders {left}")
    return title, rest


WHAT = {
    "milestone": "Formalize the milestone: its definitions, with their basic API, its theorems and their "
                 "proofs. A large proof may be split into proof tasks, one lemma per file under `Tasks/`, "
                 "whose statements are reviewed and locked before they are proven.",
    "proof": "Prove the locked statement in the task's file without changing it.",
    "upstream": "Contribute the results below to the target library: rework them to its conventions and "
                "review standards, open a pull request there, and once it is merged replace the project's "
                "copy by the library's version.",
}
# What a pull request for the task must satisfy, beyond the CI hard rules (CONTRIBUTING.md).
ACCEPT = {
    "milestone": ["each definition's docstring cites its source (author, year, arXiv ID or DOI) and "
                  "follows the project's conventions or states where it departs from them",
                  "each theorem says the same as its cited source, with the same conventions, and no "
                  "hypothesis or definition relies on a junk value (division by zero, truncated "
                  "subtraction, empty sums)",
                  "an example satisfies every hypothesis of the main theorems, proven in Lean (non-vacuity)",
                  "each trust check below holds: the Lean result reproduces the value or result it names, "
                  "quoted with its source; a deliberately wrong model or input fails it (recommended)"],
    "proof": ["the locked statements are unchanged"],
    "upstream": ["the target library has merged the result and this project uses its version"],
}

CITE = re.compile(r"\b([A-Z][\w'’]+(?:[–-][A-Z][\w'’]+)*(?: et al\.)?),? \(?((?:19|20)\d{2})\b")


def slug(heading):
    """GitHub's anchor for a Markdown heading."""
    return re.sub(r"[^\w\- ]", "", heading.strip().lower()).replace(" ", "-")


def background(t, m, root=ROOT):
    """Card lines that make a task self-contained: background, conventions, references."""
    out = []
    if m:
        out.append(f"- Background: docs/tasks/milestones.md#{slug(m['section'])} (section \"{m['section']}\")")
    out.append(f"- Conventions: {CONVENTIONS}")
    text = " ".join([m["title"], m["done_when"], *m["trust"]]) if m else t.get("rework", "")
    refs = list(OrderedDict.fromkeys(f"{a} ({y})" for a, y in CITE.findall(text)))
    if refs:
        out.append("- Literature named by the milestone: " + "; ".join(refs))
    return out


def milestone_issue(by, mid):
    """`, issue #N` when milestone `mid` has a GitHub issue (docs/tasks/checklists.yaml), else ``."""
    n = (by.get(f"T-{mid}") or {}).get("issue")
    return f", issue #{n}" if n else ""


def generic_card(t, ms, by=None):
    m = ms[t["milestone"]] if t["milestone"] else None
    where = (f"**Milestone** {m['id']}: {m['title']} (docs/tasks/milestones.md, section \"{m['section']}\""
             f"{milestone_issue(by or {}, m['id'])})" if m else
             f"**Upstream to** {t['target']} · **results** {', '.join(t['results'])} (docs/RESULTS.md)")
    lines = [f"**Task** {t['id']} · {t['kind']} · size {t['size']} · {t['difficulty']} · area {t['area']} · {t['mode']}",
             where,
             f"**Depends on** {', '.join(t['deps']) or 'nothing'}", "",
             WHAT[t["kind"]], ""]
    if not m:
        lines += [f"Rework needed: {t['rework']}", ""]
    elif m["done_when"]:
        lines += [f"Milestone done when: {m['done_when']}.", ""]
    if m:
        lines += ["Trust checks of the milestone:", *([f"- {c}" for c in m["trust"]] or [
            "- none listed in the roadmap yet: choose one against a published value or known result"]), ""]
    lines += ["Context:", *background(t, m), ""]
    lines += ["It must satisfy: the CI hard rules (CONTRIBUTING.md#hard-rules: build, no sorry, standard "
              "axioms only, nothing imports Exploratory/, docstrings), and",
              *[f"- {a}" for a in ACCEPT[t["kind"]]], ""]
    if t["mode"] == "exclusive":
        lines += [f"To take it, comment `/claim`: you are assigned and others see the task is taken. A claim "
                  f"lasts {CLAIM_HOURS} hours, or as long as a pull request naming the task is open; a person holds "
                  f"at most {MAX_CLAIMS} claims, and `/unclaim` releases one. "
                  f"A pull request for it has the line `Task: {t['id']}`"
                  + ("; none says `Closes #<this issue>`: the maintainer closes the issue after a passing "
                     "review of the milestone. See CONTRIBUTING.md." if t["kind"] == "milestone" else
                     "; the one that finishes it says `Closes #<this issue>`. See CONTRIBUTING.md.")]
    else:
        lines += ["Comment `/claim` to take it (see CONTRIBUTING.md, \"Working on the same problem\")."]
    return f"{t['id']}: {t['title']}", "\n".join(lines) + "\n"


def cards(tasks, ms, packs=None, root=ROOT):
    """{task id: (issue title, issue body)}. `packs`: context packs by declaration, for proof tasks."""
    by = {t["id"]: t for t in tasks}
    cp, template, out = context_pack_module(), (root / TEMPLATE).read_text(), OrderedDict()
    for t in tasks:
        if t["kind"] == "proof" and t.get("file"):
            title, body = proof_card(t, by, ms, (packs or {}).get(t["decl"]), cp, template)
        else:
            title, body = generic_card(t, ms, by)
        out[t["id"]] = (short_title(title), body)
    return out


def short_title(title):
    """An issue title of at most about 120 characters; the body has the full title."""
    if len(title) > 120:
        title = title[:120].rsplit(" ", 1)[0].rstrip(",;:") + " …"
    return title


def extract_packs(tasks):
    by = {t["id"]: t for t in tasks}
    reqs = [(t["decl"], [by[d]["decl"] for d in t["deps"] if by[d].get("decl")])
            for t in tasks if t["kind"] == "proof" and t.get("file")]
    return {p["decl"]: p for p in context_pack_module().extract(reqs)} if reqs else {}


def cmd_drafts(out_dir, packs_json=None, no_packs=False, root=ROOT):
    """Write the issue body of every task to `out_dir`, to read before `sync` opens the issues."""
    cfg, ms, tasks = build(root)
    if packs_json:
        packs = {p["decl"]: p for p in json.loads(pathlib.Path(packs_json).read_text())}
    else:
        packs = {} if no_packs else extract_packs(tasks)
    out = pathlib.Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    index, all_cards = [], cards(tasks, ms, packs, root)
    for t in tasks:
        title, body = all_cards[t["id"]]
        (out / f"{t['id']}.md").write_text(body)
        index.append(dict(id=t["id"], title=title, labels=t["labels"], body=f"{t['id']}.md"))
    (out / "index.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")
    print(f"tasks drafts: {len(index)} issue bodies in {out}")
    return 0


# --- Dependencies in the task files ------------------------------------------------------------

def short_name(n):
    return n[len("Lightlike."):] if n.startswith("Lightlike.") else n


def deps_section(t, p):
    """The section of a proof task's header that lists what its statement uses, from its context
    pack `p` (`context-pack --json`): the definitions the statement names, by file, and lemmas about
    them."""
    files = OrderedDict()
    for d in p["deps"]:
        last = d["name"].split(".")[-1]
        if (d["kind"] == "constructor" or last.startswith("inst") or last in ("mk", "rec")
                or not d.get("statement", True)):
            continue
        files.setdefault(d["file"], []).append(f"`{short_name(d['name'])}`")
    out = [DEPS_HEAD, ""]
    if files:
        out += ["Definitions the statement names (without the `Lightlike.` prefix), by file:", ""]
        for f, names in files.items():
            out += textwrap.wrap(f"* `{f}`: " + ", ".join(names), 100, subsequent_indent="  ",
                                 break_on_hyphens=False)
    else:
        out += ["The statement names no definition of Lightlike, only Mathlib and Physlib."]
    lem = p["lemmas"][:LEMMAS_SHOWN]
    if lem:
        out += ["", "Lemmas about them, which a proof may use:", ""]
        out += [f"* `{short_name(l['name'])}` (`{l['file']}`)" for l in lem]
    # No count of the further lemmas: it changed with every lemma added to the library, so the
    # header went stale without any task changing. The command prints the current list.
    out += ["", "Everything they depend on, and the further lemmas about them, in one block:", "",
            f"    scripts/context-pack {t['decl']}"]
    return "\n".join(out)


def source_line(m, root=ROOT):
    """The `Source:` line of a proof task's header: the milestone's references, from SOURCES."""
    src = m.get("src") or {}
    if src.get("cls") == "exploratory":
        return f"Exploratory: {src.get('reason')}."
    refs = src.get("refs") or []
    if not refs:
        return f"Structural: serves milestone {m['id']}."
    cites = (yaml_load((root / SOURCES).read_text()).get("references") or {})
    parts = []
    for r in refs:
        loc = short_location(r.get("location") or "")
        parts.append(((cites.get(r["ref"]) or {}).get("cite") or r["ref"]) + (f", {loc}" if loc else ""))
    keys = ", ".join(f"`{r['ref']}`" for r in refs)
    return f"Source: {'; '.join(parts)} ({keys} in {SOURCES})."


def task_header(t, by, ms, p, root=ROOT):
    """The module docstring of a proof task's file: the statement and what to do, a hint, what the
    statement uses, then the references."""
    def para(text):
        return textwrap.wrap(text, 100, break_on_hyphens=False, break_long_words=False)
    m = ms[t["milestone"]]
    out = [f"# Task {t['id']}", ""] + para(t["title"].rstrip(".") + ".") + [""]
    what = (f"The statement is `{t['decl']}`, at the end of this file. Replace its `sorry` by a proof "
            "and change nothing else in the file: the proof-task check rejects any other change "
            "(CONTRIBUTING.md).")
    if t["deps"]:
        uses = [f"{d} (`{short_name(by[d]['decl'])}`)" for d in t["deps"]]
        what += (" It builds on " + (", ".join(uses[:-1]) + " and " if len(uses) > 1 else "") + uses[-1]
                 + ": a proof may use their statements.")
    out += para(what) + [""]
    routes = t.get("routes") or []
    if len(routes) == 1:
        out += para(f"Hint. {routes[0]}")
    else:
        out += ["Routes, each welcome as a separate attempt:", ""]
        for i, r in enumerate(routes, 1):
            out += textwrap.wrap(f"{i}. {r}", 100, subsequent_indent="   ", break_on_hyphens=False)
    if t["difficulty"] == "research-level":
        out += [""] + para("Partial results, as helper lemmas in separate pull requests, are welcome.")
    out += ["", deps_section(t, p), "", "## References", ""]
    out += para(f"Milestone {m['id']} ({m['title'].split(':')[0]}), ROADMAP section \"{m['section']}\".")
    out += para(source_line(m, root))
    out += para("Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by "
                "`scripts/tasks.py deps` from the plan, the sources and the library.")
    return "\n".join(out)


def with_header(text, header):
    """`text` (a task file) with `header` as its module docstring."""
    a = text.index("/-!")
    b = text.index("-/", a)
    return text[:a] + "/-!\n" + header + "\n" + text[b:]


def cmd_deps(check=False, packs_json=None, root=ROOT):
    cfg, ms, tasks = build(root)
    by = {t["id"]: t for t in tasks}
    cards = [t for t in tasks if t["kind"] == "proof" and t.get("file")]
    if packs_json:
        data = json.loads(pathlib.Path(packs_json).read_text())
    else:
        reqs = [(t["decl"], [by[d]["decl"] for d in t["deps"] if by[d].get("decl")]) for t in cards]
        data = context_pack_module().extract(reqs)
    packs = {p["decl"]: p for p in data}
    stale = []
    for t in cards:
        f = root / t["file"]
        text = f.read_text()
        new = with_header(text, task_header(t, by, ms, packs[t["decl"]], root))
        if new != text:
            stale.append(t["file"])
            if not check:
                f.write_text(new)
    if check:
        for s in stale:
            print(f"  - {s}: the header is out of date: run `python3 scripts/tasks.py deps`")
        print(f"tasks deps: {'OK' if not stale else 'FAILED'} ({len(cards)} task files)")
        return 1 if stale else 0
    print(f"tasks deps: wrote {len(stale)} of {len(cards)} task files")
    return 0


# --- Sync: the task issues --------------------------------------------------------------------

ISSUE_TITLE = re.compile(rf"^\s*(?:\[proof task\]\s*)?({TASK_ID})\s*:")
LAPSED = re.compile(r"<!-- tasks\.py sync: lapse (\S+) ")
REFUSED = re.compile(r"<!-- tasks\.py sync: (?:refused|taken) (\S+) ")
LAPSE_TEXT = ("The claim of @{} expired after " + str(CLAIM_HOURS) + " hours without an open pull request that "
              "names the task, so the task is open to others. Comment `/claim` to take it again.")
TAKEN_TEXT = ("@{} The task is claimed by @{}; that claim {}. A task has one holder at a time, so your `/claim` "
              "is not recorded. Comment `/claim` again once it is released or has expired.")
REFUSE_TEXT = ("@{} already holds {} open claims ({}). A person can hold at most " + str(MAX_CLAIMS) +
               " at a time: finish or release one with `/unclaim`, then comment `/claim` here again.")


def gh(args, fatal=True):
    """Run `gh`; JSON output is parsed. On failure: exit, or (fatal=False) warn and return None."""
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode:
        msg = f"tasks sync: gh {' '.join(args[:3])} failed: {r.stderr.strip()[:300]}"
        if fatal:
            sys.exit(msg)
        print(msg, file=sys.stderr)
        return None
    out = r.stdout.strip()
    if not out:
        return ""
    try:
        return json.loads(out)
    except ValueError:
        return out


def parse_time(s):
    return datetime.datetime.fromisoformat(s.replace("Z", "+00:00"))


def stamp(when):
    return when.astimezone(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def live_data(repo):
    """The issues (with their comments), pull requests and labels of `repo`, shaped like a fixture."""
    iss = gh(["issue", "list", "--repo", repo, "--state", "all", "--limit", "5000", "--json",
              "number,title,state,stateReason,labels,assignees,comments"])
    prs = gh(["pr", "list", "--repo", repo, "--state", "all", "--limit", "2000", "--json",
              "number,body,author,state,updatedAt"])
    labels = gh(["label", "list", "--repo", repo, "--limit", "1000", "--json", "name"])

    def login(u):
        return (u or {}).get("login") or "ghost"

    return {
        "issues": [{"number": i["number"], "title": i["title"], "state": i["state"].lower(),
                    "reason": (i.get("stateReason") or "").lower(),
                    "labels": [x["name"] for x in i["labels"]], "assignees": [x["login"] for x in i["assignees"]],
                    "comments": [{"author": login(c.get("author")), "body": c.get("body") or "",
                                  "createdAt": c["createdAt"]} for c in i["comments"]]} for i in iss or []],
        "pulls": [{"number": p["number"], "body": p.get("body") or "", "author": login(p.get("author")),
                   "state": p["state"].lower(), "updatedAt": p["updatedAt"]} for p in prs or []],
        "labels": [x["name"] for x in labels or []]}


def task_issues(tasks, issues):
    """{task id: issue}: the lowest-numbered issue whose title starts with the task ID, leaving out
    issues closed as not planned or as duplicates."""
    ids, out = {t["id"] for t in tasks}, {}
    for i in sorted(issues, key=lambda i: i["number"]):
        m = ISSUE_TITLE.match(i["title"])
        if not m or m.group(1) not in ids or m.group(1) in out:
            continue
        if i["state"] == "closed" and i.get("reason", "") not in ("completed", ""):
            continue
        out[m.group(1)] = i
    return out


def activity(iss, prs, now):
    """Who works on the task of issue `iss`: (live, lapsed, ever). `live`: those who commented
    `/claim` (or `claiming`, `attempting`) and have not released, in the order they started (the first holds the task, the others are told it is taken), whose claim
    is at most CLAIM_HOURS old or who have an open pull request (`prs`, those that name the task);
    `lapsed`: [(login, claim time)] of the others; `ever`: everyone who claimed it. A lapse or refusal
    notice of `sync` ends that claim. A comment after the claim does not extend it."""
    active, ever = claim_log(iss)
    with_pr = {p["author"] for p in prs if p["state"] == "open"}
    window = datetime.timedelta(hours=CLAIM_HOURS)
    live = [a for a in active if now - active[a] <= window or a in with_pr]
    return live, [(a, active[a]) for a in active if a not in live], ever


def claim_log(iss):
    """({login: time of the claim} in the order claimed, {everyone who claimed}) from the comments of `iss`:
    a release, and a lapse or refusal notice of `sync`, end a claim."""
    active, ever = OrderedDict(), set()
    for c in sorted(iss.get("comments") or [], key=lambda c: c["createdAt"]):
        a, body, when = c["author"], c.get("body") or "", parse_time(c["createdAt"])
        m = LAPSED.search(body) or REFUSED.search(body)
        if m:
            active.pop(m.group(1), None)
            continue
        if "<!-- tasks.py sync:" in body or a.endswith("[bot]"):
            continue
        if RELEASE.search(body):
            active.pop(a, None)
        elif CLAIM.search(body):
            active.setdefault(a, when)
            ever.add(a)
    return active, ever


def live_labels(t, state, live, open_prs):
    """The labels of LIVE that the issue of task `t` carries in state `state`."""
    if state == "done":
        return []
    out = []  # every task is exclusive: a claim blocks the others
    if state == "blocked":
        out.append("blocked")
    elif not (live or open_prs):
        out.append("ready")
    if live:
        out.append("claimed")
    if open_prs:
        out.append("in review")
    return out


def sync_plan(tasks, cfg, data, card, seed=None, now=None):
    """What `sync` changes: (states, actions). `data`: issues, pulls and labels (live_data or a
    fixture); `card(id)`: (title, body) of a task's issue; `seed`: {closed: {milestone: note}, notes:
    {milestone: note}}, the state of the work from before the issues tracked it (run once)."""
    if isinstance(now, str):
        now = parse_time(now)
    now = now or datetime.datetime.now(datetime.timezone.utc)
    by = OrderedDict((t["id"], t) for t in tasks)
    seeded = {}
    for key in ("closed", "notes"):
        seeded[key] = {}
        for m, note in ((seed or {}).get(key) or {}).items():
            tid = str(m) if str(m).startswith("T-") else f"T-{m}"
            if tid not in by:
                raise ValueError(f"seed {key}: {m} is not a task")
            seeded[key][tid] = str(note)
    prs = {}
    for p in data.get("pulls") or []:
        body = re.sub(r"<!--.*?-->", "", p.get("body") or "", flags=re.S)
        for tid in sorted(set(TASK_LINE_ANY.findall(body))):
            prs.setdefault(tid, []).append(p)
    issues = task_issues(tasks, data.get("issues") or [])
    closed = {tid for tid, i in issues.items() if i["state"] == "closed"} | set(seeded["closed"])
    states = progress(tasks, cfg, closed)
    have = set(data.get("labels") or [])
    acts = [dict(op="label", name=n) for n in LIVE + sorted({x for t in tasks for x in t["labels"]} - set(LIVE))
            if n not in have]
    seed_mark, proven_mark = MARK.format("seed"), MARK.format("proven")
    # A person holds at most MAX_CLAIMS open claims (the first claimant of a task holds it); the later
    # claims are refused and the claimant is told once.
    holds = OrderedDict()
    for tid, t in by.items():
        iss = issues.get(tid)
        if iss is None or iss["state"] == "closed" or states[tid][0] == "done":
            continue
        live = activity(iss, prs.get(tid, []), now)[0]
        started = claim_log(iss)[0]
        for a in live[:1]:
            holds.setdefault(a, []).append((started[a], tid))
    refused = {}
    for a, hs in holds.items():
        for when, tid in sorted(hs)[MAX_CLAIMS:]:
            refused.setdefault(tid, []).append((a, when, [x for _, x in sorted(hs)[:MAX_CLAIMS]]))
    for tid, t in by.items():
        state, mine = states[tid][0], prs.get(tid, [])
        open_prs = [p for p in mine if p["state"] == "open"]
        iss = issues.get(tid)
        ours = CLAIM_LABELS if t["kind"] == "milestone" else LIVE
        if iss is None:
            if t["kind"] == "milestone":
                continue  # scripts/sync_github.py opens it
            if state != "ready" and tid not in seeded["closed"] and tid not in seeded["notes"]:
                continue
            title, body = card(tid)
            labels = t["labels"] + live_labels(t, state, [], open_prs)
            acts.append(dict(op="create", task=tid, issue=None, title=title, body=body, labels=labels))
            iss = dict(number=None, state="open", labels=labels, assignees=[], comments=[])
        num = iss["number"]
        if iss["state"] == "closed":
            stale = [x for x in iss["labels"] if x in ours]
            if stale:
                acts.append(dict(op="edit", task=tid, issue=num, add=[], remove=stale, assign=[], unassign=[]))
            continue
        posted = "\n".join(c.get("body") or "" for c in iss.get("comments") or [])
        live, lapsed, ever = activity(iss, mine, now)
        no = {a for a, _, _ in refused.get(tid, [])}
        live = [a for a in live if a not in no]
        started = claim_log(iss)[0]
        taken = [(a, started[a]) for a in live[1:]]  # later claimants of a held task
        live = live[:1]
        want = [x for x in live_labels(t, state, live, open_prs) if x in ours]
        add = [x for x in want if x not in iss["labels"]]
        remove = [x for x in iss["labels"] if x in ours and x not in want]
        assign, unassign = [], []
        if state != "done":
            assign = [a for a in live if a not in iss["assignees"]]
            unassign = [a for a in iss["assignees"] if a in ever and a not in live]
        if add or remove or assign or unassign:
            acts.append(dict(op="edit", task=tid, issue=num, add=add, remove=remove, assign=assign,
                             unassign=unassign))
        if state != "done":
            acts += [dict(op="comment", task=tid, issue=num,
                          body=LAPSE_TEXT.format(a) + "\n\n" + MARK.format(f"lapse {a} {stamp(when)}"))
                     for a, when in lapsed]
            acts += [dict(op="comment", task=tid, issue=num,
                          body=REFUSE_TEXT.format(a, MAX_CLAIMS, ", ".join(keep)) + "\n\n"
                          + MARK.format(f"refused {a} {stamp(when)}"))
                     for a, when, keep in refused.get(tid, [])]
            if live:
                until = (f"expires {stamp(started[live[0]] + datetime.timedelta(hours=CLAIM_HOURS))} unless a pull "
                         "request naming the task is open")
                acts += [dict(op="comment", task=tid, issue=num,
                              body=TAKEN_TEXT.format(a, live[0], until) + "\n\n" + MARK.format(f"taken {a} {stamp(when)}"))
                         for a, when in taken]
        if t["kind"] == "milestone":
            continue  # closed by scripts/sync_github.py once fully ticked, never here
        if tid in seeded["closed"]:
            if seed_mark not in posted:
                more = re.sub(r"^done\b\s*", "", seeded["closed"][tid]).strip()
                acts.append(dict(op="close", task=tid, issue=num, body="Done before the issues of this repository "
                                 f"tracked the tasks{' ' + more if more else ''}.\n\n{seed_mark}"))
        elif state == "done":
            if proven_mark not in posted:  # closed once; an issue reopened by hand afterwards stays open
                why = (f"`{t['decl']}` has no `sorry` on `main`" if t["kind"] == "proof"
                       else "every proof task of this milestone is proven on `main`")
                acts.append(dict(op="close", task=tid, issue=num, body=f"Done: {why}.\n\n{proven_mark}"))
        elif tid in seeded["notes"] and seed_mark not in posted:
            acts.append(dict(op="comment", task=tid, issue=num, body="State when the issues of this repository "
                             f"started to track the tasks: {seeded['notes'][tid]}.\n\n{seed_mark}"))
    return states, acts


def describe(a):
    """One line of the dry-run output."""
    if a["op"] == "label":
        return f"label: create \"{a['name']}\""
    where = f"#{a['issue']}" if a.get("issue") else "(new issue)"
    if a["op"] == "create":
        return f"{a['task']}: open issue \"{a['title']}\" [{', '.join(a['labels'])}]"
    if a["op"] == "edit":
        parts = ([f"+{x}" for x in a["add"]] + [f"-{x}" for x in a["remove"]]
                 + [f"assign @{u}" for u in a["assign"]] + [f"unassign @{u}" for u in a["unassign"]])
        return f"{a['task']} {where}: {', '.join(parts)}"
    return f"{a['task']} {where}: {a['op']}: {a['body'].splitlines()[0]}"


def label_spec(specs, name):
    return specs.get(name) or specs.get(name.split(":")[0] + ":") or {}


def apply_actions(acts, repo, specs):
    """Make the changes with gh, one per second; returns the number that failed."""
    created, failures = {}, 0
    for a in acts:
        if a["op"] == "label":
            s = label_spec(specs, a["name"])
            args = ["label", "create", a["name"], "--repo", repo]
            args += ["--color", str(s["color"])] if s.get("color") else []
            args += ["--description", s["description"]] if s.get("description") else []
            ok = gh(args, fatal=False) is not None
        elif a["op"] == "create":
            with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as f:
                f.write(a["body"])
            r = gh(["issue", "create", "--repo", repo, "--title", a["title"], "--body-file", f.name,
                    *[x for lab in a["labels"] for x in ("--label", lab)]], fatal=False)
            pathlib.Path(f.name).unlink()
            m = re.search(r"/issues/(\d+)", r) if isinstance(r, str) else None
            if m:
                created[a["task"]] = int(m.group(1))
            ok = bool(m)
        else:
            num = a.get("issue") or created.get(a["task"])
            if not num:
                print(f"tasks sync: skipped ({describe(a)}): its issue was not opened", file=sys.stderr)
                failures += 1
                continue
            if a["op"] == "edit":
                args = ["issue", "edit", str(num), "--repo", repo]
                for flag, key in (("--add-label", "add"), ("--remove-label", "remove"),
                                  ("--add-assignee", "assign"), ("--remove-assignee", "unassign")):
                    args += [flag, ",".join(a[key])] if a[key] else []
            elif a["op"] == "close":
                args = ["issue", "close", str(num), "--repo", repo, "--reason", "completed", "--comment", a["body"]]
            else:
                args = ["issue", "comment", str(num), "--repo", repo, "--body", a["body"]]
            ok = gh(args, fatal=False) is not None
        failures += not ok
        time.sleep(1)
    return failures


def cmd_sync(fixture, apply, seed_file=None, with_packs=False, root=ROOT):
    if apply and fixture:
        sys.exit("tasks sync: --apply changes the live issues; it does not take --fixture")
    conf = yaml_load((root / BOARD).read_text())
    cfg, ms, tasks = build(root)
    data = json.loads(pathlib.Path(fixture).read_text()) if fixture else live_data(conf["repo"])
    seed = yaml_load(pathlib.Path(seed_file).read_text()) if seed_file else None
    memo = {}

    def card(tid):
        if not memo:
            memo.update(cards(tasks, ms, extract_packs(tasks) if with_packs else {}, root))
        return memo[tid]

    dup = duplicate_problems(tasks, root)
    if dup:
        sys.exit("tasks sync: no issue is opened for a statement the library already proves:\n  - " + "\n  - ".join(dup))
    states, acts = sync_plan(tasks, cfg, data, card, seed, data.get("now"))
    for a in acts:
        print(describe(a))
    n = Counter(s for s, _ in states.values())
    print(f"tasks sync: {len(acts)} changes; {n['done']} tasks done, {n['ready']} ready, {n['blocked']} blocked"
          + ("" if apply else " (dry run; --apply makes them)"))
    if not apply or not acts:
        return 0
    failures = apply_actions(acts, conf["repo"], conf.get("labels") or {})
    if failures:
        print(f"tasks sync: {failures} of {len(acts)} changes failed", file=sys.stderr)
    return 1 if failures else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for c in ("generate", "check", "status"):
        sub.add_parser(c)
    p = sub.add_parser("lock")
    p.add_argument("ids", nargs="+")
    p = sub.add_parser("drafts")
    p.add_argument("--out-dir", default=str(ROOT / "task-drafts"))
    p.add_argument("--packs-json", help="context packs already extracted (`context-pack --json`)")
    p.add_argument("--no-packs", action="store_true")
    p = sub.add_parser("deps")
    p.add_argument("--check", action="store_true")
    p.add_argument("--packs-json", help="context packs already extracted (`context-pack --json`)")
    p = sub.add_parser("sync")
    p.add_argument("--apply", action="store_true", help="make the changes (needs gh with write access to issues)")
    p.add_argument("--fixture", help="read issues and pull requests from a JSON file instead of GitHub")
    p.add_argument("--seed", help="YAML with the state of the work from before the issues tracked it")
    p.add_argument("--with-packs", action="store_true", help="put context packs in new proof task issues (runs Lean)")
    a = ap.parse_args(argv)
    if a.cmd == "generate":
        return cmd_generate()
    if a.cmd == "check":
        return cmd_check()
    if a.cmd == "status":
        return cmd_status()
    if a.cmd == "lock":
        return cmd_lock(a.ids)
    if a.cmd == "drafts":
        return cmd_drafts(a.out_dir, a.packs_json, a.no_packs)
    if a.cmd == "deps":
        return cmd_deps(a.check, a.packs_json)
    return cmd_sync(a.fixture, a.apply, a.seed, a.with_packs)


if __name__ == "__main__":
    sys.exit(main())
