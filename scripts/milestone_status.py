#!/usr/bin/env python3
"""The status of every milestone, computed from `main` (status is computed, never typed).

The plan is read from this checkout: the milestone tables of docs/tasks/milestones.md and the
checklists of docs/tasks/checklists.yaml. The library, docs/results.yaml and the API maps are read
from a checkout of `main` with the library built.

An item of a checklist is ticked when every declaration it names exists in the library, has no
`sorry` and uses only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. This
is the search of scripts/AxiomAudit.lean, in its per-declaration mode, not a text search. A
catalogue item also needs each declaration in an entry of docs/results.yaml with `status: proven`
and cited in an API map. A review item (a comparison with a source) is ticked when its
`review_evidence` in docs/tasks/checklists.yaml holds the evidence, written by whoever did the
work: what was compared with what, and the result.

A milestone is done when every item of its checklist is ticked; scripts/sync_github.py then closes
its issue. There is no separate review step (owner, 25 Nov 2026): a review happens only when the
owner asks for one.

Usage, from the repository root:

    python3 scripts/milestone_status.py schema
        check docs/tasks/checklists.yaml against the milestone tables (offline, seconds)
    python3 scripts/milestone_status.py compute --main DIR [--streams DIR] [--out DIR]
                                                [--lake CMD] [--decls FILE] [--only ID,ID]
        DIR is a checkout of main with the library built. Runs the audit there (about 3 minutes
        and 11 GB), then writes OUT/status.json and OUT/bodies/<ID>.md, the body of each
        milestone's issue. --streams: the folder of the stream status files <name>.json, for who
        has claimed a milestone and its last step. --decls: reuse the audit output of an earlier run.
    python3 scripts/milestone_status.py rank [--status OUT/status.json] [--md FILE] [--write]
        the order in which the streams take the v1.0 milestones (unblockers first, a milestone below
        the ones it needs), from a computed status. --md: write the ranking page. --write: set
        `ranking:` in docs/tasks/checklists.yaml to it.
    python3 scripts/milestone_status.py --selftest
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import tasks as T  # noqa: E402

CHECKLISTS = "docs/tasks/checklists.yaml"
MIN_EVIDENCE = 30  # characters: the evidence of a review item, not a word like "ok"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
KINDS = {"main": "m", "piece": "p", "trust": "t", "catalogue": "c", "review": "r"}
KIND_TITLE = {"main": "Main theorem", "piece": "Piece", "trust": "Trust check", "catalogue": "Catalogue",
              "review": "Review"}
ITEM_KEYS = {"id", "kind", "text", "decls", "hint", "review_evidence"}
FULL_NAME = re.compile(r"^Lightlike\.[^\s.][^\s]*$")
MARK = "<!-- milestone-status"
FRESH_HOURS = 24  # a stream's claim counts while its status file is at most this old


# --- The plan -----------------------------------------------------------------------------------

def load_plan(root=ROOT):
    """(milestones of milestones.md, tasks, checklists.yaml as a dict, set of v1.0 IDs)."""
    _, ms, tasks = T.build(root)
    data = T.yaml_load((root / CHECKLISTS).read_text()) or {}
    v1 = data.get("v1.0") or {}
    ids = {m["id"] for m in ms.values() if T.in_v1(m, v1)}
    return ms, tasks, data, ids


def schema_problems(ms, data, v1):
    probs = []
    for k in data:
        if k not in ("v1.0", "milestones"):
            probs.append(f"unknown top-level key {k!r}")
    want = (data.get("v1.0") or {}).get("count")
    if want is not None and len(v1) != want:
        probs.append(f"v1.0: the areas and sizes give {len(v1)} milestones, not {want}")
    entries = data.get("milestones") or {}
    rankings, issues = {}, {}
    for mid, e in entries.items():
        where = f"{CHECKLISTS}: {mid}"
        if mid not in ms:
            probs.append(f"{where}: not a milestone of milestones.md")
            continue
        e = e or {}
        allowed = {"issue", "ranking", "items"} if mid in v1 else {"issue"}
        for k in e:
            if k not in allowed:
                probs.append(f"{where}: key {k!r} is not allowed" + ("" if mid in v1 else " (not a v1.0 milestone)"))
        if e.get("issue") is not None and not (isinstance(e["issue"], int) and e["issue"] > 0):
            probs.append(f"{where}: issue must be a positive number")
        elif e.get("issue") is not None:
            if e["issue"] in issues:
                probs.append(f"{where}: issue #{e['issue']} is also that of {issues[e['issue']]}")
            issues[e["issue"]] = mid
        r = e.get("ranking")
        if r is not None:
            if not isinstance(r, int) or r < 1:
                probs.append(f"{where}: ranking must be a positive number or null")
            elif r in rankings:
                probs.append(f"{where}: ranking {r} is also that of {rankings[r]}")
            else:
                rankings[r] = mid
        if mid in v1:
            probs += item_problems(where, e.get("items"))
    for mid in sorted(v1, key=T.natural):
        if mid not in entries or not (entries[mid] or {}).get("items"):
            probs.append(f"{CHECKLISTS}: v1.0 milestone {mid} has no checklist")
    return probs


def item_problems(where, items):
    probs, seen = [], set()
    if items is None:
        return []  # no checklist yet: reported once, as "has no checklist"
    if not isinstance(items, list):
        return [f"{where}: items must be a list"]
    kinds = set()
    for it in items:
        if not isinstance(it, dict):
            probs.append(f"{where}: an item is not a mapping")
            continue
        iid, kind = it.get("id"), it.get("kind")
        w = f"{where}/{iid}"
        for k in it:
            if k not in ITEM_KEYS:
                probs.append(f"{w}: unknown key {k!r}")
        if kind not in KINDS:
            probs.append(f"{w}: kind must be one of {', '.join(KINDS)}")
        elif not (isinstance(iid, str) and re.fullmatch(KINDS[kind] + r"\d+", iid)):
            probs.append(f"{w}: the id of a {kind} item is {KINDS[kind]}<n>")
        if iid in seen:
            probs.append(f"{w}: id used twice")
        seen.add(iid)
        kinds.add(kind)
        if not (isinstance(it.get("text"), str) and it["text"].strip()):
            probs.append(f"{w}: text is missing")
        decls = it.get("decls")
        if kind == "review":
            if "review_evidence" not in it:
                probs.append(f"{w}: a review item has review_evidence (null until the evidence is written)")
            if decls:
                probs.append(f"{w}: a review item names no declarations")
        else:
            if "review_evidence" in it:
                probs.append(f"{w}: review_evidence is for review items only")
            if not isinstance(decls, list):
                probs.append(f"{w}: decls must be a list (empty while none is written)")
            else:
                for d in decls:
                    if not (isinstance(d, str) and FULL_NAME.match(d)):
                        probs.append(f"{w}: {d!r} is not a full name starting with Lightlike.")
        ev = it.get("review_evidence")
        if ev is not None and not (isinstance(ev, str) and len(ev.strip()) >= MIN_EVIDENCE):
            probs.append(f"{w}: review_evidence is null or the evidence itself (what was compared with "
                         f"what, and the result; at least {MIN_EVIDENCE} characters)")
    for k in ("main", "catalogue"):
        if k not in kinds:
            probs.append(f"{where}: the checklist has no {k} item")
    return probs


# --- The library ----------------------------------------------------------------------------------

def audit(main, names, lake, cache=None):
    """{name: audit line} for `names`, from the per-declaration mode of AxiomAudit.lean in `main`."""
    if cache:
        lines = pathlib.Path(cache).read_text().splitlines()
    else:
        with tempfile.TemporaryDirectory() as tmp:
            q, out = pathlib.Path(tmp, "decls.txt"), pathlib.Path(tmp, "decls.jsonl")
            q.write_text("".join(n + "\n" for n in sorted(names)))
            env = dict(os.environ, LL_DECLS=str(q), LL_DECLS_OUT=str(out))
            r = subprocess.run([*lake.split(), "env", "lean", str(ROOT / "scripts/AxiomAudit.lean")],
                               cwd=main, env=env, capture_output=True, text=True)
            if not out.exists():
                sys.exit(f"milestone_status: the audit wrote nothing (exit {r.returncode}):\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
            lines = out.read_text().splitlines()
    res = {}
    for line in lines:
        if line.strip():
            j = json.loads(line)
            res[j["q"]] = j
    return res


def decl_state(name, aud):
    """('ok' | 'missing' | 'outside' | 'sorry' | 'axioms', detail)."""
    a = aud.get(name)
    if a is None or not a.get("found"):
        c = (a or {}).get("candidates") or []
        return "missing", ("not in the library" + (f"; did you mean {', '.join(c[:3])}?" if c else ""))
    if not a.get("module", "").startswith("Lightlike"):
        return "outside", f"declared in {a.get('module') or 'an unknown module'}, not in the library"
    bad = sorted(set(a.get("axioms") or []) - STANDARD)
    if "sorryAx" in bad:
        return "sorry", "depends on a sorry"
    if bad:
        return "axioms", "uses the axioms " + ", ".join(bad)
    return "ok", a["module"]


def catalogue_index(main):
    import api_map
    proven, other = {}, {}
    for e in api_map.load(main):
        for d in e.get("decls") or []:
            (proven if e.get("status") == "proven" else other).setdefault(d, []).append(e.get("id"))
    cited = set()
    for p in api_map.maps(main):
        for _, d in api_map.lint_map(main, p)[1]:
            cited.add(d if d.startswith("Lightlike.") else "Lightlike." + d)
    return proven, other, cited


def read_streams(folder):
    out = []
    for p in sorted(pathlib.Path(folder).glob("*.json")) if folder else []:
        try:
            j = json.loads(p.read_text())
        except (OSError, ValueError):
            continue
        if isinstance(j, dict) and j.get("milestone") and j.get("state") not in ("handed-back", "done"):
            out.append(dict(stream=j.get("stream") or p.stem, milestone=j["milestone"], step=j.get("step"),
                            item=j.get("item"), branch=j.get("branch"), last_commit=j.get("last_commit"),
                            gate=j.get("gate"), updated_at=j.get("updated_at"), state=j.get("state")))
    return out


# --- Status --------------------------------------------------------------------------------------

def compute(ms, tasks, data, v1, aud, cat, main_sha, main, streams, now):
    proven, other, cited = cat
    entries = data.get("milestones") or {}
    out = {}
    for mid, m in ms.items():
        e = entries.get(mid) or {}
        st = dict(id=mid, title=m["title"], area=m["area"], size=m["size"], v1=mid in v1,
                  ranking=e.get("ranking"), issue=e.get("issue"), done_when=m["done_when"],
                  trust=m["trust"], needs=m["needs"],
                  proof_tasks=[t["id"] for t in tasks if t.get("kind") == "proof" and t.get("milestone") == mid],
                  claimed_by=[s["stream"] for s in streams if s["milestone"] == mid and fresh(s, now)],
                  stale_claims=[s["stream"] for s in streams if s["milestone"] == mid and not fresh(s, now)],
                  last_step=max((s for s in streams if s["milestone"] == mid),
                                key=lambda s: s.get("updated_at") or "", default=None))
        items = []
        if mid in v1:
            # A catalogue item without decls covers the theorems of the main and piece items
            # (definitions are documented, but they are not entries of the catalogue).
            core = [d for it in e.get("items") or [] if it.get("kind") in ("main", "piece")
                    for d in it.get("decls") or [] if (aud.get(d) or {}).get("kind", "theorem") == "theorem"]
            for it in e.get("items") or []:
                items.append(item_status(it, aud, proven, other, cited, core))
        st["items"] = items
        st["ticked"] = sum(i["ticked"] for i in items)
        st["total"] = len(items)
        # done: every item is ticked (review items by their written evidence); the issue is then closed.
        st["done"] = bool(items) and st["ticked"] == st["total"]
        out[mid] = st
    return dict(main=main_sha, computed_at=now, milestones=out)


def fresh(s, now):
    """Whether the status file of stream `s` was updated at most FRESH_HOURS before `now`."""
    try:
        t, n = (datetime.datetime.fromisoformat(str(x).replace("Z", "+00:00")) for x in (s.get("updated_at"), now))
    except (TypeError, ValueError):
        return False
    if t.tzinfo is None:
        t = t.replace(tzinfo=datetime.timezone.utc)
    return n - t <= datetime.timedelta(hours=FRESH_HOURS)


def item_status(it, aud, proven, other, cited, core):
    kind = it.get("kind")
    r = dict(id=it.get("id"), kind=kind, text=it.get("text", ""), hint=it.get("hint"), decls=[], ticked=False, why="")
    if kind == "review":
        ev = it.get("review_evidence")
        r["review_evidence"] = ev
        r["ticked"] = isinstance(ev, str) and len(ev.strip()) >= MIN_EVIDENCE
        r["why"] = "" if r["ticked"] else "no evidence written yet"
        return r
    names = list(it.get("decls") or []) or (core if kind == "catalogue" else [])
    for d in names:
        s, detail = decl_state(d, aud)
        if s == "ok" and kind == "catalogue":
            if d not in proven:
                s, detail = "uncatalogued", ("its entries " + ", ".join(other[d]) + " are not proven"
                                             if d in other else "no entry of docs/results.yaml names it")
            elif d not in cited:
                s, detail = "uncatalogued", "no API map cites it"
        r["decls"].append(dict(name=d, state=s, detail=detail))
    r["ticked"] = bool(names) and all(x["state"] == "ok" for x in r["decls"])
    if not names:
        r["why"] = "no declaration is named yet"
    return r


# --- The issue body ------------------------------------------------------------------------------

def body(st, repo_sha, date, outside=None, issue_of=None):
    """The issue body of milestone `st` (an entry of status.json). `outside`: the logins that hold
    the claim label on the issue (outside contributors; scripts/sync_github.py reads them);
    `issue_of`: {task id: issue number}, to link the proof tasks."""
    L = [f"{MARK}: generated by scripts/milestone_status.py from main {repo_sha[:7]} on {date}. "
         "Do not edit: the next sync replaces this text. -->",
         f"**{st['id']}: {st['title']}**", "",
         f"Area {st['area']} · size {st['size']} · "
         + (f"v1.0" + (f" · ranking {st['ranking']}" if st.get("ranking") else "") if st["v1"]
            else "not scheduled: open to outside contributors, not worked on by the project's streams"),
         "", f"**Done when:** {st['done_when']}"]
    if st["trust"]:
        L += ["", "**Trust checks:** " + "; ".join(st["trust"])]
    if st["needs"]:
        L += ["", "**Needs:** " + ", ".join(st["needs"])]
    if st["v1"]:
        L += ["", f"### Checklist: {st['ticked']} of {st['total']} ticked", ""]
        for it in st["items"]:
            L.append(f"- [{'x' if it['ticked'] else ' '}] **{KIND_TITLE[it['kind']]}** ({it['id']}). {it['text']}")
            for d in it["decls"]:
                L.append(f"  - `{d['name']}`" + ("" if d["state"] == "ok" else f": {d['detail']}"))
            if it.get("why"):
                L.append(f"  - {it['why']}")
            if it.get("hint") and not it["ticked"]:
                L.append(f"  - {it['hint']}")
    L += ["", "### Work", ""]
    if st["claimed_by"]:
        L.append("- **Claimed by:** " + ", ".join(f"the stream {c}" for c in st["claimed_by"]))
    elif outside:
        L.append("- **Claimed by:** " + ", ".join(f"@{u}" for u in outside) + " (claim on this issue)")
    elif st["v1"]:
        L.append("- **Claimed by:** nobody: free to take")
    else:
        L.append("- **Claimed by:** nobody: comment `/claim` on this issue to take it")
    if st.get("stale_claims"):
        L.append("- **Stale claim:** " + ", ".join(f"the stream {c}" for c in st["stale_claims"])
                 + f" (its status file is more than {FRESH_HOURS} hours old)")
    ls = st.get("last_step")
    if ls:
        L.append(f"- **Last step:** {ls.get('step') or '—'} ({ls.get('updated_at') or 'no time'}"
                 + (f"; branch `{ls['branch']}`" if ls.get("branch") else "") + ")")
    if st["proof_tasks"]:
        L += ["", "### Proof tasks", "", *[f"- {p}" + (f" (#{issue_of[p]})" if (issue_of or {}).get(p) else "")
                                           for p in st["proof_tasks"]]]
    return "\n".join(L) + "\n"


# --- Ranking -------------------------------------------------------------------------------------

def rank(milestones):
    """The order in which the streams take the v1.0 milestones, from computed statuses.

    Topological over the needs (a milestone ranks below the milestones it needs). Among those whose
    needs are placed: most v1.0 milestones unblocked (directly or through others) first, then fewer
    open proof items (main theorem, piece, trust check), then fewer open review items, then the ID.
    Returns (order, unblocked, open, needs): unblocked[ID] is the sorted list of milestones that
    need ID, open[ID] the counts (proof, review, catalogue) of its unticked items."""
    v = {k: m for k, m in milestones.items() if m["v1"]}
    needs = {k: [n for n in m["needs"] if n in v] for k, m in v.items()}
    users = {k: set() for k in v}
    for k, ns in needs.items():
        for n in ns:
            users[n].add(k)

    def down(k):
        seen, stack = set(), [k]
        while stack:
            for u in users[stack.pop()] - seen:
                seen.add(u)
                stack.append(u)
        return seen

    unblocked = {k: sorted(down(k)) for k in v}
    open_ = {}
    for k, m in v.items():
        un = [i for i in m["items"] if not i["ticked"]]
        open_[k] = (sum(i["kind"] in ("main", "piece", "trust") for i in un),
                    sum(i["kind"] == "review" for i in un), sum(i["kind"] == "catalogue" for i in un))
    order, placed = [], set()
    while len(order) < len(v):
        avail = [k for k in v if k not in placed and all(n in placed for n in needs[k])]
        if not avail:
            raise SystemExit(f"milestone_status rank: the needs of {sorted(set(v) - placed)} form a cycle")
        k = min(avail, key=lambda k: (-len(unblocked[k]), open_[k][0], open_[k][1], k))
        order.append(k)
        placed.add(k)
    return order, unblocked, open_, needs


def ranking_md(res, order, unblocked, open_, needs):
    """The ranking as a Markdown page: the rule, how a stream takes work, and the table."""
    v, sha = res["milestones"], res["main"][:8]

    def short(t):
        t = t.replace("|", "/")
        return t if len(t) <= 72 else t[:71].rstrip() + "…"

    L = ["# Milestone ranking (v1.0)", "",
         f"Computed {res['computed_at']} from main {sha} by `scripts/milestone_status.py rank`. Streams "
         "read this ranking to choose work.", "",
         "**Rule.** Milestones that unblock others come first. *Unblocks* counts the v1.0 milestones that "
         "need this one, directly or through others (the Needs column of docs/tasks/milestones.md). A "
         "milestone always ranks below the milestones it needs. Ties: fewer open proof items first, then "
         "fewer open review items.", "",
         "**Taking work.** A stream takes the highest-ranked milestone that is free: not claimed by another "
         "stream's status file (fresh, at most 24 h old) or by an outside contributor's claim label, and not "
         "closed. Its needs do not have to be closed first. If its work really waits on an unfinished need, "
         "the stream hands it back (state `handed-back` and the reason in its status file) and takes the "
         "next one.", "",
         "**Open items** are the unticked items of docs/tasks/checklists.yaml, computed from main: *proof* "
         "= main theorem, piece or trust check without a declaration yet; *review* = a review item (a "
         "comparison with a source, ticked when the stream that does the work writes the evidence into the "
         "item); *catalogue* = the docs/results.yaml entries and API-map citations. A milestone is done, "
         "and its issue closed, when every item is ticked.", "",
         "Recomputed after every merge that ticks items and after every closed milestone; `ranking:` in "
         "docs/tasks/checklists.yaml carries the same numbers.", "",
         "| Rank | ID | Milestone | Size | Unblocks | Open: proof / review / catalogue | Needs | Issue |",
         "|---:|---|---|---|---:|---|---|---|"]
    for i, k in enumerate(order, 1):
        m, w = v[k], open_[k]
        L.append(f"| {i} | {k} | {short(m['title'])} | {m['size']} | {len(unblocked[k])} | "
                 f"{w[0]} / {w[1]} / {w[2]} | {', '.join(needs[k]) or '-'} | "
                 f"{('#' + str(m['issue'])) if m['issue'] else 'none yet'} |")
    tot = [sum(open_[k][j] for k in order) for j in range(3)]
    full = sum(v[k]["done"] for k in order)
    L += ["", f"Totals: {tot[0]} open proof items, {tot[1]} open review items, {tot[2]} open catalogue items "
          f"over {len(order)} milestones; {full} done (main {sha}).", ""]
    return "\n".join(L)


def write_rankings(order, path=None):
    """Set `ranking:` of each v1.0 milestone in docs/tasks/checklists.yaml to its place in `order`,
    editing only those lines (the comments and the layout stay). Returns the number changed."""
    path = pathlib.Path(path or ROOT / CHECKLISTS)
    place = {k: i for i, k in enumerate(order, 1)}
    out, key, changed = [], None, 0
    for line in path.read_text().splitlines(keepends=True):
        m = re.match(r"^  ([A-Za-z0-9]+):\s*$", line)
        if m:
            key = m.group(1)
        if key in place and re.match(r"^    ranking: (\d+|null)?\s*$", line):
            new = f"    ranking: {place[key]}\n"
            changed += new != line
            line = new
        out.append(line)
    path.write_text("".join(out))
    return changed


# --- Commands ------------------------------------------------------------------------------------

def cmd_schema(root=ROOT):
    ms, _, data, v1 = load_plan(root)
    probs = schema_problems(ms, data, v1)
    for p in probs:
        print("  - " + p)
    print(f"milestone_status schema: {'OK' if not probs else 'FAILED'} ({len(v1)} v1.0 milestones, "
          f"{sum(1 for e in (data.get('milestones') or {}).values() if (e or {}).get('items'))} checklists)")
    return 1 if probs else 0


def cmd_compute(a):
    ms, tasks, data, v1 = load_plan(ROOT)
    main = pathlib.Path(a.main).resolve()
    if a.only:
        keep = set(a.only.split(","))
        ms = {k: v for k, v in ms.items() if k in keep}
    names = {d for mid in ms if mid in v1 for it in ((data.get("milestones") or {}).get(mid) or {}).get("items") or []
             for d in it.get("decls") or []}
    aud = audit(main, names, a.lake, a.decls)
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=main, capture_output=True, text=True).stdout.strip()
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    res = compute(ms, tasks, data, v1, aud, catalogue_index(main), sha, main, read_streams(a.streams), now)
    out = pathlib.Path(a.out)
    (out / "bodies").mkdir(parents=True, exist_ok=True)
    (out / "status.json").write_text(json.dumps(res, ensure_ascii=False, indent=1) + "\n")
    for mid, st in res["milestones"].items():
        (out / "bodies" / f"{mid}.md").write_text(body(st, sha, now[:10]))
    v = [s for s in res["milestones"].values() if s["v1"]]
    print(f"milestone_status: main {sha[:7]}; {len(res['milestones'])} milestones, {len(v)} of v1.0: "
          f"{sum(s['done'] for s in v)} done; "
          f"items {sum(s['ticked'] for s in v)} of {sum(s['total'] for s in v)} ticked; wrote {out}")
    return 0


def cmd_rank(a):
    res = json.loads(pathlib.Path(a.status).read_text())
    order, unblocked, open_, needs = rank(res["milestones"])
    if a.md:
        pathlib.Path(a.md).write_text(ranking_md(res, order, unblocked, open_, needs))
    changed = write_rankings(order) if a.write else None
    print(f"milestone_status rank: {len(order)} v1.0 milestones (main {res['main'][:7]}): {' '.join(order)}"
          + (f"; wrote {a.md}" if a.md else "")
          + (f"; {changed} ranking(s) changed in {CHECKLISTS}" if changed is not None else ""))
    return 0


def selftest():
    aud = {"Lightlike.a": dict(q="Lightlike.a", found=True, module="Lightlike.X", axioms=["propext"]),
           "Lightlike.b": dict(q="Lightlike.b", found=True, module="Lightlike.X", axioms=["sorryAx", "propext"]),
           "Lightlike.c": dict(q="Lightlike.c", found=False, candidates=["Lightlike.Y.c"]),
           "Lightlike.d": dict(q="Lightlike.d", found=True, module="Mathlib.Foo", axioms=[]),
           "Lightlike.e": dict(q="Lightlike.e", found=True, module="Lightlike.X", axioms=["Lightlike.myAxiom"])}
    want = {"Lightlike.a": "ok", "Lightlike.b": "sorry", "Lightlike.c": "missing", "Lightlike.d": "outside",
            "Lightlike.e": "axioms", "Lightlike.f": "missing"}
    fails = [f"{n}: {decl_state(n, aud)[0]} != {w}" for n, w in want.items() if decl_state(n, aud)[0] != w]
    cat = ({"Lightlike.a": ["LL-1"]}, {"Lightlike.g": ["LL-2"]}, {"Lightlike.a"})
    it = lambda **k: item_status(dict(k), aud, *cat, ["Lightlike.a"])  # noqa: E731
    checks = [(it(id="m1", kind="main", decls=["Lightlike.a"])["ticked"], True),
              (it(id="m1", kind="main", decls=["Lightlike.a", "Lightlike.b"])["ticked"], False),
              (it(id="t1", kind="trust", decls=[])["ticked"], False),
              (it(id="c1", kind="catalogue", decls=[])["ticked"], True),
              (it(id="c1", kind="catalogue", decls=["Lightlike.e"])["ticked"], False),
              (it(id="r1", kind="review", review_evidence=None)["ticked"], False),
              (it(id="r1", kind="review", review_evidence="ok")["ticked"], False),
              (it(id="r1", kind="review", review_evidence="Source eq. (3.12) compared with weylOf: same sign")["ticked"],
               True)]
    fails += [f"item check {i}: {got} != {w}" for i, (got, w) in enumerate(checks) if got != w]
    bad = item_problems("x", [dict(id="m1", kind="main", text="t", decls=["short_name"]),
                              dict(id="p1", kind="review", text="t", decls=[])])
    if len(bad) < 3:
        fails.append(f"schema: planted bad items gave only {bad}")
    mk = lambda needs, kinds: dict(v1=True, needs=needs, items=[dict(kind=k, ticked=False) for k in kinds])  # noqa: E731
    order = rank({"A": mk([], ["main"]), "B": mk(["A"], []), "C": mk(["B"], []), "D": mk([], []),
                  "E": mk([], ["main", "main"]), "F": mk(["E"], []), "X": dict(v1=False, needs=[], items=[])})[0]
    if order != ["A", "B", "E", "C", "D", "F"]:
        fails.append(f"rank: unblockers first and needs first gave {order}, not A B E C D F")
    with tempfile.TemporaryDirectory() as d:
        # A milestone with a review item is done only once the evidence is written into the item.
        ms_ = {"R": dict(title="t", area="X", size="S", done_when="", trust="", needs=[])}
        data_ = {"milestones": {"R": {"items": [dict(id="m1", kind="main", decls=["Lightlike.a"]),
                                                dict(id="r1", kind="review", text="t", review_evidence=None)]}}}
        run = lambda: compute(ms_, [], data_, {"R"}, aud, cat, "0" * 40, d, [], "2026-11-25T00:00:00Z")["milestones"]["R"]  # noqa: E731
        st = run()
        if st["done"] or st["ticked"] != 1:
            fails.append(f"review item: before the evidence done={st['done']} ticked={st['ticked']}")
        data_["milestones"]["R"]["items"][1]["review_evidence"] = "Source p. 3 compared with Lightlike.a: matches"
        st = run()
        if not st["done"] or st["ticked"] != 2:
            fails.append(f"review item: with the evidence done={st['done']} ticked={st['ticked']}")
        f = pathlib.Path(d) / "c.yaml"
        f.write_text("milestones:\n  A:\n    issue: 1\n    ranking: 3\n  B:\n    ranking: null\n  C:\n    issue: 3\n")
        n = write_rankings(["B", "A"], f)
        if n != 2 or "  A:\n    issue: 1\n    ranking: 2\n  B:\n    ranking: 1\n  C:\n    issue: 3\n" not in f.read_text():
            fails.append(f"write_rankings: {n} changed, gave {f.read_text()!r}")
    for f in fails:
        print("  - " + f)
    print(f"milestone_status selftest: {'OK' if not fails else 'FAILED'}")
    return 1 if fails else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    sub = ap.add_subparsers(dest="cmd")
    sub.add_parser("schema")
    p = sub.add_parser("compute")
    p.add_argument("--main", required=True)
    p.add_argument("--streams")
    p.add_argument("--out", default=".lake/milestone-status")
    p.add_argument("--lake", default=os.environ.get("LL_LAKE", "lake"))
    p.add_argument("--decls")
    p.add_argument("--only")
    p = sub.add_parser("rank")
    p.add_argument("--status", default=".lake/milestone-status/status.json")
    p.add_argument("--md")
    p.add_argument("--write", action="store_true")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if a.cmd == "schema":
        return cmd_schema()
    if a.cmd == "compute":
        return cmd_compute(a)
    if a.cmd == "rank":
        return cmd_rank(a)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
