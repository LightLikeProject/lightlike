#!/usr/bin/env python3
"""API maps (`Lightlike/<Area>/API-map.md`) and the results registry (`docs/results.yaml`).

A pull request puts its new entries in a file of its own, `docs/results.d/<topic>.yaml`, with draft
IDs (`LL-XXXX`, or `LL-XXXX-a`, `LL-XXXX-b`, ... for several), so that parallel pull requests do not
conflict at the end of `docs/results.yaml`. At merge, `combine` appends those files to
`docs/results.yaml` and removes them, and the maintainers assign the numbers. The registry is
`docs/results.yaml` followed by the files of `docs/results.d/`, in file-name order.

Usage, from the repository root:

    python3 scripts/api_map.py check [--base REF]   lint the API maps and the registry, and fail if
                                                   docs/RESULTS.md is out of date; with --base, also
                                                   check that IDs at git ref REF are kept
    python3 scripts/api_map.py names               write .lake/api_names.tsv for scripts/NameCheck.lean
    python3 scripts/api_map.py generate            write docs/RESULTS.md from the registry
    python3 scripts/api_map.py combine             at merge: append docs/results.d/*.yaml to
                                                   docs/results.yaml and remove those files
    python3 scripts/api_map.py --selftest          planted bad cases must be caught

The API-map format follows Physlib's: `# Title` (in words, not the module path), then exactly the
sections `## Abstract (Alpha)` (no citations), `## Content (Alpha)` (Lean citations `[n]`, one
number per bracket, `[TODO]` for unformalized parts, literature citations `{n}`),
`## Lean References` (`n. path.lean - `decl`, …`, numbered from 1 without gaps, one file per entry,
each cited) and `## References` (`n. …`, each cited). Raw markdown links are not allowed.
Declarations are written relative to the `Lightlike` namespace.

The text checks here are complemented by `scripts/NameCheck.lean`, which resolves every name in Lean.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

import yaml

SECTIONS = ["## Abstract (Alpha)", "## Content (Alpha)", "## Lean References", "## References"]
STATUSES = {"proven", "conditional", "stated", "retired"}
STATUS_TEXT = {
    "proven": "proven",
    "conditional": "conditional",
    "stated": "stated, not proven",
    "retired": "retired",
}
# Tier of a result: what kind of mathematics it is about. The definitions are the maintainers'; changing
# them is a change of scope.
TIERS = ("established", "frontier", "exploratory")
TIER_TEXT = (
    "Tier: **established** (standard mathematics and physics that the frontier work needs; candidates "
    "for Mathlib or Physlib later); **frontier** (proposals published in the peer-reviewed "
    "literature, labelled as proposals); **exploratory** (new or unpublished models and "
    "conjectures, kept in `Exploratory/` folders that nothing else imports; promoted to frontier "
    "only after publication). Every result is about the mathematics of a model, not a claim that "
    "the model describes nature.")

# The kind of an entry that is not a result in the sense of a paper's theorem. An entry without `kind`
# is a result. The count of entries is read with these kinds taken out (docs/RESULTS.md, "How to
# read the count").
KINDS = {
    "supporting": "a supporting lemma of another entry; under the rule that an entry is a result a "
                  "paper or book would state as a theorem it would get no entry today",
    "elementary": "an elementary fact with a short standard proof",
    "wrapper": "a restatement of a result that Mathlib or Physlib already proves; the proof is theirs",
}
COMPARISON_PENDING = "comparison pending"

# A main result: the main theorem of a cited paper or book, or a named theorem.
MAIN_TEXT = (
    "The main theorem of a cited paper or book, or a named theorem (`main: true` in "
    "`docs/results.yaml`). Each is listed again in its area below.")

# Review status of a result or a locked statement. `ref` is the issue with the expert's review.
REVIEWS = ("kernel-checked", "human-reviewed")
REVIEW_TEXT = (
    "Review: every entry is **kernel-checked**: Lean's kernel verified the proof (for a stated "
    "target, that the statement is well-formed). A kernel check guarantees the proof, not that a "
    "statement or a definition means what its source means. An entry that a domain expert has "
    "compared with its source is marked **human-reviewed**, with a link to the issue that holds the "
    "review. To review an entry, or to report that a statement does not match its source, open an "
    "issue that names the entry's ID.")


def review_errors(where: str, review, ref, root: Path) -> list[str]:
    """Errors in a `review` / `review_ref` pair."""
    if review is None or review == "kernel-checked":
        return [] if ref is None else [f"{where}: review_ref given without a review above kernel-checked"]
    if review not in REVIEWS:
        return [f"{where}: review must be one of {list(REVIEWS)}"]
    if not str(ref or "").startswith("https://github.com/"):
        return [f"{where}: human-reviewed needs the URL of the issue with the review"]
    return []


def review_cell(review, ref, prefix: str = "") -> str:
    review = review or "kernel-checked"
    if not ref:
        return review
    return f"[{review}]({ref if str(ref).startswith('http') else prefix + str(ref)})"


# LL-XXXX and LL-XXXX-<letter> are draft IDs in a pull request; merging assigns the numbers
ID_RE = re.compile(r"^LL-(?:\d{4}|XXXX(?:-[a-z])?)$")
DRAFT_RE = re.compile(r"^LL-XXXX(?:-[a-z])?$")
REGISTRY = "docs/results.yaml"
PENDING = "docs/results.d"
ENTRY_RE = re.compile(r"^(\d+)\. (\S+\.lean) [-\u2014] (.+)$")
REF_RE = re.compile(r"^(\d+)\. \S")


def sections(text: str) -> tuple[str, dict[str, str], list[str]]:
    """Split an API map into its title, its sections and a list of format errors."""
    errs: list[str] = []
    lines = text.splitlines()
    title = lines[0] if lines else ""
    if not re.match(r"^# \S", title):
        errs.append("first line must be '# Title'")
    elif re.fullmatch(r"# [\w.-]+(/[\w.-]+)+", title.strip()):
        errs.append("the title names the area in words (it heads the area's section of "
                    "docs/RESULTS.md), not its path")
    heads = [(i, l) for i, l in enumerate(lines) if l.startswith("#")][1:]
    if [l for _, l in heads] != SECTIONS:
        errs.append(f"headings must be exactly {SECTIONS}, found {[l for _, l in heads]}")
        return title, {}, errs
    body = {}
    for k, (i, h) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        body[h] = "\n".join(lines[i + 1:end])
    return title, body, errs


def lean_entries(block: str) -> tuple[list[tuple[int, str, list[str]]], list[str]]:
    """Parse `## Lean References` into (number, file, declarations), joining wrapped lines."""
    errs, items, cur = [], [], None
    for line in block.splitlines():
        if not line.strip():
            continue
        if re.match(r"^\d+\. ", line):
            cur = line
            items.append(cur)
        elif line.startswith("   ") and items:
            items[-1] += " " + line.strip()
        else:
            errs.append(f"unexpected line in Lean References: {line!r}")
    out = []
    for it in items:
        m = ENTRY_RE.match(it)
        if not m:
            errs.append(f"Lean reference must be 'n. path.lean - `decl`, …': {it[:70]!r}")
            continue
        decls = re.findall(r"`([^`]+)`", m.group(3))
        if not decls:
            errs.append(f"Lean reference {m.group(1)} lists no declarations")
        out.append((int(m.group(1)), m.group(2), decls))
    return out, errs


def numbered(nums: list[int], what: str) -> list[str]:
    return [] if nums == list(range(1, len(nums) + 1)) else [f"{what} must be numbered 1..n, got {nums}"]


def last_name(decl: str) -> str:
    return decl.rsplit(".", 1)[-1]


# An inline code span: a run of backticks, its text, and a run of the same length (CommonMark).
CODE_SPAN_RE = re.compile(r"(?<!`)(`+)(?!`)(.+?)(?<!`)\1(?!`)", re.S)


def without_code(text: str) -> str:
    """The text with each inline code span blanked, so that math such as `[0,1]^F` or `{0}` is not read as a
    citation. Spans are paired within a paragraph: a span may wrap onto the next line but never crosses a blank
    line."""
    return "\n\n".join(CODE_SPAN_RE.sub(" ", p) for p in re.split(r"\n[ \t]*\n", text))


def in_file(decl: str, src: str) -> bool:
    """Text check: the declaration's last name component occurs as a word in the file."""
    return re.search(r"(?<![\w'])" + re.escape(last_name(decl)) + r"(?![\w'])", src) is not None


def lint_map(root: Path, path: Path) -> tuple[list[str], list[tuple[str, str]]]:
    """Errors for one API map, and its (file, declaration) pairs."""
    rel = path.relative_to(root)
    text = path.read_text(encoding="utf-8")
    _, body, errs = sections(text)
    names: list[tuple[str, str]] = []
    if "](" in text:
        errs.append("raw markdown link")
    if not body:
        return [f"{rel}: {e}" for e in errs], names
    # citations are read from the prose only: brackets and braces inside code spans are math or code
    abstract, content = without_code(body[SECTIONS[0]]), without_code(body[SECTIONS[1]])
    if re.search(r"\[\d|\{\d", abstract):
        errs.append("the abstract must not cite")
    if re.search(r"\[\d+\s*[,;–-]", content):
        errs.append("each Lean citation needs its own brackets: [1] [2], not [1, 2]")
    entries, e2 = lean_entries(body[SECTIONS[2]])
    errs += e2
    errs += numbered([n for n, _, _ in entries], "Lean References")
    cited = {int(n) for n in re.findall(r"\[(\d+)\]", content)}
    have = {n for n, _, _ in entries}
    errs += [f"citation [{n}] has no Lean reference" for n in sorted(cited - have)]
    errs += [f"Lean reference {n} is never cited" for n in sorted(have - cited)]
    seen = set()
    for n, f, decls in entries:
        if f in seen:
            errs.append(f"{f} has two entries")
        seen.add(f)
        fp = root / f
        if not fp.is_file():
            errs.append(f"Lean reference {n}: no file {f}")
            continue
        src = fp.read_text(encoding="utf-8")
        for d in decls:
            names.append((f, d))
            if not in_file(d, src):
                errs.append(f"Lean reference {n}: `{d}` not found in {f}")
    refs = [int(m.group(1)) for l in body[SECTIONS[3]].splitlines() if (m := REF_RE.match(l))]
    errs += numbered(refs, "References")
    lit = {int(n) for n in re.findall(r"\{(\d+)\}", content)}
    errs += [f"citation {{{n}}} has no reference" for n in sorted(lit - set(refs))]
    errs += [f"reference {n} is never cited" for n in sorted(set(refs) - lit)]
    return [f"{rel}: {e}" for e in errs], names


def pending_files(root: Path) -> list[Path]:
    """The files of new entries, `docs/results.d/*.yaml`, in file-name order."""
    return sorted((root / PENDING).glob("*.yaml"))


def load_file(path: Path) -> list:
    data = yaml.safe_load(path.read_text(encoding="utf-8")) if path.is_file() else None
    return data if isinstance(data, list) else []


def load(root: Path) -> list[dict]:
    """The registry: `docs/results.yaml`, then the new entries in `docs/results.d/`."""
    reg = load_file(root / REGISTRY)
    for p in pending_files(root):
        reg += load_file(p)
    return [e for e in reg if isinstance(e, dict)]


def lint_pending(root: Path) -> list[str]:
    """New entries live in `docs/results.d/` with draft IDs; `docs/results.yaml` has numbers only."""
    errs = [f"{e.get('id')}: a new entry goes in {PENDING}/<topic>.yaml, not in {REGISTRY}"
            for e in load_file(root / REGISTRY) if isinstance(e, dict) and DRAFT_RE.match(str(e.get("id")))]
    for p in pending_files(root):
        rel = p.relative_to(root)
        data = yaml.safe_load(p.read_text(encoding="utf-8"))
        if not isinstance(data, list) or not all(isinstance(e, dict) for e in data):
            errs.append(f"{rel}: must be a list of entries, as in {REGISTRY}")
            continue
        errs += [f"{rel}: {e.get('id')}: an entry in {PENDING} has a draft ID (LL-XXXX, or "
                 f"LL-XXXX-a, LL-XXXX-b, ...); the merge assigns the number"
                 for e in data if not DRAFT_RE.match(str(e.get("id")))]
    return errs


def combine(root: Path) -> list[str]:
    """Append the files of `docs/results.d/` to `docs/results.yaml`, in file-name order, and
    remove them. Refuses, changing nothing, if the joined text would not read as the same entries."""
    files = pending_files(root)
    if not files:
        return []
    before = load(root)
    reg = root / REGISTRY
    text = reg.read_text(encoding="utf-8") if reg.is_file() else ""
    for p in files:
        add = p.read_text(encoding="utf-8")
        if text and not text.endswith("\n"):
            text += "\n"
        text += add if add.endswith("\n") or not add else add + "\n"
    try:
        after = yaml.safe_load(text) or []
    except yaml.YAMLError:
        after = None
    if after != before:
        raise SystemExit(f"api_map combine: the files of {PENDING} do not append cleanly to "
                         f"{REGISTRY} (a document marker, another indentation?); nothing changed")
    reg.write_text(text, encoding="utf-8")
    for p in files:
        p.unlink()
    if not any((root / PENDING).iterdir()):
        (root / PENDING).rmdir()
    return [str(p.relative_to(root)) for p in files]


def lint_registry(root: Path, reg: list[dict]) -> list[str]:
    errs, prev = [], ""
    for e in reg:
        i = e.get("id", "?")
        for k in ("id", "title", "area", "file", "decls", "status", "tier", "since"):
            if k not in e:
                errs.append(f"{i}: missing '{k}'")
        if not ID_RE.match(str(i)):
            errs.append(f"{i}: ID must be LL-dddd, or a draft LL-XXXX or LL-XXXX-<letter>")
        elif i <= prev:
            errs.append(f"{i}: IDs must increase (after {prev}); drafts come last, each once")
        prev = max(prev, str(i))
        st = e.get("status")
        if st not in STATUSES:
            errs.append(f"{i}: status must be one of {sorted(STATUSES)}")
        errs += review_errors(str(i), e.get("review"), e.get("review_ref"), root)
        if "tier" in e and e["tier"] not in TIERS:
            errs.append(f"{i}: tier must be one of {list(TIERS)}")
        if "kind" in e:
            if e["kind"] not in KINDS:
                errs.append(f"{i}: kind must be one of {sorted(KINDS)} or absent")
            elif not e.get("note"):
                errs.append(f"{i}: an entry of kind {e['kind']} needs a note saying why")
        if "main" in e:
            src = e.get("source")
            if e["main"] is not True:
                errs.append(f"{i}: main is `true` or absent")
            elif st != "proven":
                errs.append(f"{i}: a main result is proven")
            elif not (isinstance(src, dict) and src.get("refs")):
                errs.append(f"{i}: a main result cites its source")
        if e.get("tier") == "exploratory" and "/Exploratory/" not in str(e.get("file")):
            errs.append(f"{i}: an exploratory result lives in an Exploratory/ folder")
        if e.get("source") == "exploratory" and "/Exploratory/" not in str(e.get("file")):
            errs.append(f"{i}: `source: exploratory` is only for files in an Exploratory/ folder "
                        f"(use `source: pending` while no source is attached)")
        if st == "conditional" and not e.get("hypotheses"):
            errs.append(f"{i}: a conditional result lists its hypotheses")
        if st in ("stated", "retired") and not e.get("note"):
            errs.append(f"{i}: a {st} result needs a note")
        if not (root / "Lightlike" / str(e.get("area")) / "API-map.md").is_file():
            errs.append(f"{i}: area {e.get('area')} has no API-map.md")
        fp = root / str(e.get("file"))
        if not fp.is_file():
            errs.append(f"{i}: no file {e.get('file')}")
            continue
        if st == "retired":
            continue
        src = fp.read_text(encoding="utf-8")
        for d in (e.get("decls") or []) + (e.get("hypotheses") or []):
            if not str(d).startswith("Lightlike."):
                errs.append(f"{i}: `{d}` must be a full name starting with Lightlike.")
        for d in e.get("decls") or []:
            if not in_file(d, src):
                errs.append(f"{i}: `{d}` not found in {e.get('file')}")
    return errs


def stability(reg: list[dict], base: list[dict]) -> list[str]:
    now = {e["id"]: e for e in reg}
    errs = [f"{b['id']}: removed (retire it instead)" for b in base if b["id"] not in now]
    errs += [f"{b['id']}: area changed from {b['area']} to {now[b['id']]['area']}"
             for b in base if b["id"] in now and now[b["id"]]["area"] != b["area"]]
    top = max((b["id"] for b in base), default="")
    old = {b["id"] for b in base}
    errs += [f"{i}: new IDs must be above {top}" for i in now if i not in old and i <= top]
    return errs


def area_title(root: Path, area: str) -> str:
    """The title of an area: the first line of its API map, without the `# `."""
    m = root / "Lightlike" / area / "API-map.md"
    first = m.read_text(encoding="utf-8").split("\n", 1)[0] if m.is_file() else ""
    return first[2:].strip() if first.startswith("# ") else area


def lean_cell(e: dict) -> str:
    return ", ".join(f"`{d}`" for d in e["decls"]) + f" in [{Path(e['file']).name}](../{e['file']})"


def title_cell(e: dict) -> str:
    return e["title"] + (" (see note)" if e.get("note") else "")


def notes(rows: list[dict]) -> list[str]:
    """The notes of `rows`, as a list under their table."""
    ns = [f"- **{e['id']}.** {e['note'].strip()}" for e in rows if e.get("note")]
    return ["Notes:", "", *ns, ""] if ns else []


def counts(reg: list[dict]) -> dict:
    """The honest breakdown of the catalog: kinds, conditional and stated, comparison pending."""
    live = [e for e in reg if e["status"] != "retired"]
    c = {k: sum(e.get("kind") == k for e in live) for k in KINDS}
    c["entries"] = len(live)
    c["results"] = len(live) - sum(c[k] for k in KINDS)
    c["open"] = sum(e["status"] in ("conditional", "stated") for e in live)
    pend = [e for e in live if COMPARISON_PENDING in str(e.get("note", "")).lower()]
    c["pending"] = len(pend)
    # An entry whose source is a string (`pending`, `structural`) cites no source: nothing is named to compare with.
    c["pending_own"] = sum(isinstance(e.get("source"), str) for e in pend)
    c["pending_cited"] = c["pending"] - c["pending_own"]
    c["limits"] = sum("Limits:" in str(e.get("note", "")) for e in live)
    return c


def limit_of(e: dict) -> str:
    """The sentence after `Limits:` in the note of an entry, shortened."""
    note = " ".join(str(e.get("note", "")).split())
    if "Limits:" not in note:
        return ""
    text = note.split("Limits:", 1)[1].split(" Check:", 1)[0].strip()
    if len(text) > 240:
        text = text[:240].rsplit(" ", 1)[0] + " …"
    return text.replace("|", "\\|")


def read_count(reg: list[dict]) -> list[str]:
    """The section of RESULTS.md that says what the number of entries counts."""
    live = [e for e in reg if e["status"] != "retired"]
    c = counts(reg)
    out = ["## How to read the count", "",
           f"The catalog has {c['entries']} entries. They are not {c['entries']} theorems of equal weight:", "",
           f"- {c['results']} are results in the sense of a paper's theorem (no `kind`).",
           *[f"- {c[k]} {'is' if c[k] == 1 else 'are'} of kind `{k}`: {t}." for k, t in KINDS.items()],
           f"- {c['open']} of the entries are conditional (proven under hypotheses) or stated targets (proof open): "
           "the table below lists them with their hypotheses.",
           f"- {c['pending']} entries still have the note \"Comparison pending\": the statement was not compared with the "
           f"text of a source. {c['pending_cited']} of them cite a source whose text at the cited location was not "
           f"read against the statement; {c['pending_own']} cite no source (their `source` is `pending` or "
           "`structural`: no source is named, so there was nothing to compare with; many are textbook statements for "
           "which a source still has to be chosen and read). The kernel has checked their proofs; a person has not "
           "checked that the statement says what the literature says.",
           f"- {c['limits']} entries state a limit (`Limits:`): the statement is narrower than the "
           "source (one chart, finitely many modes, a special family, and so on). The last table lists them.", "",
           "### Conditional and stated results", "",
           "| ID | Result | Status | Tier | Hypotheses |", "|---|---|---|---|---|"]
    for e in live:
        if e["status"] in ("conditional", "stated"):
            hyp = ", ".join(f"`{h}`" for h in e.get("hypotheses", [])) or "the proof is open"
            out.append(f"| {e['id']} | {e['title']} | {STATUS_TEXT[e['status']]} | {e['tier']} | {hyp} |")
    out += ["", f"### Entries of another kind", "",
            "| ID | Kind | Result |", "|---|---|---|"]
    for e in live:
        if e.get("kind"):
            out.append(f"| {e['id']} | {e['kind']} | {e['title']} |")
    out += ["", "### Limits stated by the entries", "",
            "Quoted from the `Limits:` sentence of the note of each entry.", "",
            "| ID | Tier | Limit |", "|---|---|---|"]
    for e in live:
        if limit_of(e):
            out.append(f"| {e['id']} | {e['tier']} | {limit_of(e)} |")
    return out + [""]


def render(reg: list[dict], root: Path) -> str:
    n = {s: sum(e["status"] == s for e in reg) for s in STATUSES}
    targets = [e for e in reg if e["status"] == "stated"]
    out = ["<!-- Generated by `python3 scripts/api_map.py generate` from docs/results.yaml. Do not edit. -->",
           "", "# Results", "",
           f"{n['proven']} proven results with stable IDs{',' if targets else ' and'} {n['conditional']} conditional "
           f"result{'s' * (n['conditional'] != 1)} (proven under hypotheses that are named Lean "
           f"propositions)" + (f" and {len(targets)} [stated target{'s' * (len(targets) != 1)}](#stated-targets) "
           "(the statement is defined in Lean, the proof is open)" if targets else "") +
           ". An ID is never reused; a withdrawn "
           "result is kept as `retired`. Every declaration of the library, and so every proven result, "
           "depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.", "",
           TIER_TEXT, "", REVIEW_TEXT, "", *read_count(reg)]
    mains = [e for e in reg if e.get("main") is True and e["status"] == "proven"]
    if mains:
        out += ["## Main results", "", MAIN_TEXT, "",
                "| ID | Result | Area | Tier | Lean |", "|---|---|---|---|---|"]
        for e in mains:
            out.append(f"| {e['id']} | {e['title']} | {area_title(root, e['area'])} | {e['tier']} | {lean_cell(e)} |")
        out.append("")
    areas: list[str] = []
    for e in reg:
        if e["area"] not in areas and e["status"] != "stated":
            areas.append(e["area"])
    for a in areas:
        rows = [x for x in reg if x["area"] == a and x["status"] != "stated"]
        out += [f"## {area_title(root, a)}", "",
                f"API map: [Lightlike/{a}/API-map.md](../Lightlike/{a}/API-map.md)", "",
                "| ID | Result | Status | Tier | Lean |", "|---|---|---|---|---|"]
        for e in rows:
            st = STATUS_TEXT[e["status"]]
            if e.get("hypotheses"):
                st += " on " + ", ".join(f"`{h}`" for h in e["hypotheses"])
            if e.get("review") == "human-reviewed":
                st += f", {review_cell(e['review'], e.get('review_ref'))}"
            out.append(f"| {e['id']} | {title_cell(e)} | {st} | {e['tier']} | {lean_cell(e)} |")
        out += ["", *notes(rows)]
    if targets:
        out += ["## Stated targets", "",
                "Statements defined in Lean and checked to be well-formed, whose proofs are open. "
                "They are not results.", "",
                "| ID | Target | Area | Tier | Lean |", "|---|---|---|---|---|"]
        for e in targets:
            out.append(f"| {e['id']} | {title_cell(e)} | {area_title(root, e['area'])} | {e['tier']} | {lean_cell(e)} |")
        out += ["", *notes(targets)]
    return "\n".join(out).rstrip("\n") + "\n"


README_SUMMARY = ("<!-- results:summary (generated by scripts/api_map.py) -->", "<!-- /results:summary -->")


def summary(reg: list[dict]) -> str:
    """The size and review state of the catalog, for README.md."""
    live = [e for e in reg if e["status"] != "retired"]
    c = {s: sum(e["status"] == s for e in live) for s in ("proven", "conditional", "stated")}
    h = sum(e.get("review") == "human-reviewed" for e in live)

    def count(k, one, many):
        return f"{k} {one if k == 1 else many}"

    human = ("No entry has had expert human review yet" if not h else
             f"{count(h, 'entry has', 'entries have')} had expert human review")
    k = counts(reg)
    # An entry whose `source` is a string (`pending`: none attached yet, `structural`) cites no source.
    nosrc_n = sum(isinstance(e.get("source"), str) for e in live)
    text = (f"The [catalog](docs/RESULTS.md) has {count(len(live), 'entry', 'entries')}: "
            f"{count(c['proven'], 'proven result', 'proven results')}"
            f"{', ' if c['stated'] else ' and '}"
            f"{count(c['conditional'], 'conditional result', 'conditional results')} (proven under "
            f"hypotheses that are named Lean propositions)"
            + (f" and {count(c['stated'], 'stated target', 'stated targets')} (the statement is "
               f"defined in Lean, the proof is open)" if c['stated'] else "") +
            f". {count(nosrc_n, 'entry does', 'entries do')} not yet cite a source for the statement; "
            f"the other {len(live) - nosrc_n} cite one"
            f", of which {k['pending_cited']} were not yet read against the text at the cited location. "
            f"Lean's kernel has checked every proof. Statements are "
            f"reviewed against their sources by agents, since the kernel cannot check that a statement matches "
            f"its source. {human}, and a review of any entry is welcome "
            f"([how to report a mismatch](#review)).")
    kinds = sum(k[x] for x in KINDS)
    text2 = (f"Read the count with care ([details](docs/RESULTS.md#how-to-read-the-count)): "
             f"{count(kinds, 'entry is', 'entries are')} a supporting lemma, an elementary fact or a wrapper of a "
             f"Mathlib or Physlib result, so {k['results']} are results in the sense of a paper's theorem; "
             f"{count(k['open'], 'entry is', 'entries are')} conditional or a stated target; "
             f"{count(k['pending'], 'entry has', 'entries have')} a statement that was not yet compared with "
             f"the text of a source ({k['pending_cited']} cite one, {k['pending_own']} cite none); {count(k['limits'], 'entry states', 'entries state')} a limit (the "
             f"statement is narrower than the source).")
    return (textwrap.fill(text, 100, break_on_hyphens=False) + "\n\n"
            + textwrap.fill(text2, 100, break_on_hyphens=False))


def readme_summary(text: str, reg: list[dict]) -> str:
    """README.md with `summary(reg)` between the README_SUMMARY markers."""
    if README_SUMMARY[0] not in text:
        return text
    head, rest = text.split(README_SUMMARY[0], 1)
    return (head + README_SUMMARY[0] + "\n" + summary(reg) + "\n" + README_SUMMARY[1]
            + rest.split(README_SUMMARY[1], 1)[1])


def maps(root: Path) -> list[Path]:
    return sorted((root / "Lightlike").glob("**/API-map.md"))


def check(root: Path, base: str | None = None) -> list[str]:
    errs: list[str] = []
    for m in maps(root):
        errs += lint_map(root, m)[0]
    reg = load(root)
    errs += lint_pending(root)
    errs += lint_registry(root, reg)
    res = root / "docs/RESULTS.md"
    if not res.is_file() or res.read_text(encoding="utf-8") != render(reg, root):
        errs.append("docs/RESULTS.md is out of date (expected on a branch: the maintainers regenerate it "
                    "after merging; see scripts/generated.py)")
    readme = root / "README.md"
    if readme.is_file() and readme.read_text(encoding="utf-8") != readme_summary(readme.read_text(encoding="utf-8"), reg):
        errs.append("the results summary in README.md is out of date (expected on a branch: the "
                    "maintainers regenerate it after merging; see scripts/generated.py)")
    if base:
        r = subprocess.run(["git", "-C", str(root), "show", f"{base}:docs/results.yaml"],
                           capture_output=True, text=True)
        if r.returncode == 0:
            errs += stability(reg, yaml.safe_load(r.stdout) or [])
    return errs


def names(root: Path) -> int:
    rows = [("map", f, d) for m in maps(root) for f, d in lint_map(root, m)[1]]
    rows += [("registry", e["file"], d) for e in load(root) if e["status"] != "retired"
             for d in e["decls"]]
    # a hypothesis is stated where it is defined, usually not in the file of the result that takes it,
    # so it is checked to exist, not to be declared in a given file (an empty file column)
    rows += [("hypothesis", "", h) for e in load(root) if e["status"] != "retired"
             for h in e.get("hypotheses") or []]
    out = root / ".lake/api_names.tsv"
    out.parent.mkdir(exist_ok=True)
    out.write_text("".join(f"{s}\t{f}\t{d}\n" for s, f, d in rows), encoding="utf-8")
    print(f"wrote {len(rows)} names to {out.relative_to(root)}")
    return 0


GOOD_MAP = """# Toy

## Abstract (Alpha)

A toy area.

## Content (Alpha)

The lemma [1] follows {1}. [TODO] the rest.

## Lean References

1. Lightlike/Toy/A.lean - `Toy.lemma1`

## References

1. A. Author, A paper, 2000.
"""
GOOD_REG = """- id: LL-0001
  title: A lemma
  area: Toy
  file: Lightlike/Toy/A.lean
  decls: [Lightlike.Toy.lemma1]
  status: proven
  tier: established
  since: 0.1.0
"""


def selftest() -> int:
    cases = [
        ("control", None, None, False),
        ("planted: citation without a Lean reference", "[1] follows", "[1] [2] follows", True),
        ("planted: Lean reference never cited", "The lemma [1] follows", "The lemma follows", True),
        ("planted: declaration missing from the file", "`Toy.lemma1`", "`Toy.lemma9`", True),
        ("planted: wrong heading", "## Content (Alpha)", "## Contents", True),
        ("planted: path as title", "# Toy\n", "# Lightlike/Toy\n", True),
        ("planted: citation in the abstract", "A toy area.", "A toy area [1].", True),
        ("planted: raw markdown link", "A toy area.", "A [toy](x.md) area.", True),
        ("planted: shared brackets", "The lemma [1]", "The lemma [1, 1]", True),
        ("planted: uncited literature reference", " follows {1}.", " follows.", True),
        ("planted: bad ID", "REG:LL-0001", "LL-001", True),
        ("a draft ID in docs/results.d is accepted", "NEW:LL-0001", "LL-XXXX-a", False),
        ("planted: bad draft ID", "NEW:LL-0001", "LL-XXXX-1", True),
        ("planted: a numbered ID in docs/results.d", "NEW:LL-0001", "LL-0002", True),
        ("planted: a draft ID in docs/results.yaml", "REG:LL-0001", "LL-XXXX", True),
        ("planted: the same draft in two files of docs/results.d", "TWO:LL-0001", "LL-XXXX", True),
        ("planted: unknown tier", "REG:tier: established", "tier: central", True),
        ("kind with a note accepted", "REG:tier: established", "tier: established\n  kind: supporting\n  note: supports LL-0002", False),
        ("planted: unknown kind", "REG:tier: established", "tier: established\n  kind: minor\n  note: x", True),
        ("planted: kind without a note", "REG:tier: established", "tier: established\n  kind: supporting", True),
        ("planted: RESULTS.md out of date", "RES", "", True),
        ("main result accepted", "REG:  since:", "  main: true\n  source:\n    refs:\n      - {ref: toy-2000, location: \"Theorem 1\"}\n  since:", False),
        ("planted: source exploratory outside an Exploratory/ folder", "REG:  since:", "  source: exploratory\n  since:", True),
        ("source pending is accepted", "REG:  since:", "  source: pending\n  since:", False),
        ("planted: main result without a source", "REG:  since:", "  main: true\n  since:", True),
        ("planted: main result not proven", "REG:status: proven", "status: retired\n  note: gone\n  main: true\n  source:\n    refs:\n      - {ref: toy-2000, location: \"Theorem 1\"}\n", True),
        ("planted: main not true", "REG:  since:", "  main: false\n  source:\n    refs:\n      - {ref: toy-2000, location: \"Theorem 1\"}\n  since:", True),
    ]
    fails = 0
    for name, old, new, bad in cases:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "Lightlike/Toy").mkdir(parents=True)
            (root / "docs").mkdir()
            (root / "Lightlike/Toy/A.lean").write_text(
                "theorem lemma1 : True := trivial\ntheorem lemma2 : True := trivial\n")
            mp, rg, new_files = GOOD_MAP, GOOD_REG, []
            if old and old.startswith("REG:"):
                rg = rg.replace(old[4:], new)
            elif old and old[:4] in ("NEW:", "TWO:"):
                new_files = [GOOD_REG.replace(old[4:], new)] * (2 if old[:4] == "TWO:" else 1)
            elif old and old != "RES":
                mp = mp.replace(old, new)
            (root / "Lightlike/Toy/API-map.md").write_text(mp)
            (root / "docs/results.yaml").write_text(rg)
            for n, text in enumerate(new_files):
                (root / PENDING).mkdir(exist_ok=True)
                (root / PENDING / f"topic{n}.yaml").write_text(text)
            if old != "RES":
                (root / "docs/RESULTS.md").write_text(render(load(root), root))
            errs = check(root)
            ok = bool(errs) == bad
            fails += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}" + ("" if ok else f": {errs}"))
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / "docs" / "results.d").mkdir(parents=True)
        (root / REGISTRY).write_text(GOOD_REG)
        for n, i in ((1, "LL-XXXX"), (2, "LL-XXXX-a")):
            (root / PENDING / f"t{n}.yaml").write_text(GOOD_REG.replace("LL-0001", i))
        before = load(root)
        done = combine(root)
        ok = (len(done) == 2 and not (root / PENDING).exists() and load(root) == before
              and [e["id"] for e in load_file(root / REGISTRY)] == ["LL-0001", "LL-XXXX", "LL-XXXX-a"])
        (root / PENDING).mkdir()
        (root / PENDING / "bad.yaml").write_text("---\n" + GOOD_REG.replace("LL-0001", "LL-XXXX-b"))
        reg_text = (root / REGISTRY).read_text()
        try:
            combine(root)
            ok = False
        except SystemExit:
            ok = ok and (root / REGISTRY).read_text() == reg_text and len(pending_files(root)) == 1
    fails += not ok
    print(f"{'ok  ' if ok else 'FAIL'} combine appends docs/results.d in order and removes it; "
          f"planted: a file that does not append cleanly changes nothing")
    base = yaml.safe_load(GOOD_REG)
    ok = bool(stability([], base)) and not stability(base, base)
    fails += not ok
    print(f"{'ok  ' if ok else 'FAIL'} planted: a removed ID is caught by --base")
    one = yaml.safe_load(GOOD_REG)[0]
    planted = [dict(one, source="pending"), dict(one, source="structural"), dict(one), dict(one)]
    text = " ".join(summary(planted).split())
    ok = "2 entries do not yet cite a source for the statement; the other 2 cite one" in text
    fails += not ok
    print(f"{'ok  ' if ok else 'FAIL'} planted: the README counts the entries whose source is pending or structural")
    print("selftest:", "OK" if not fails else f"FAILED ({fails})")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("cmd", nargs="?", choices=["check", "names", "generate", "combine"])
    ap.add_argument("--base", help="git ref whose docs/results.yaml IDs must be kept")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    root = Path(__file__).resolve().parent.parent
    if a.selftest:
        return selftest()
    if a.cmd == "generate":
        reg = load(root)
        (root / "docs/RESULTS.md").write_text(render(reg, root), encoding="utf-8")
        readme = root / "README.md"
        if readme.is_file():
            readme.write_text(readme_summary(readme.read_text(encoding="utf-8"), reg), encoding="utf-8")
        print("wrote docs/RESULTS.md and the results summary in README.md")
        return 0
    if a.cmd == "names":
        return names(root)
    if a.cmd == "combine":
        done = combine(root)
        print(f"combined into {REGISTRY}: {', '.join(done)}" if done else f"nothing in {PENDING}")
        return 0
    if a.cmd == "check":
        errs = check(root, a.base)
        for e in errs:
            print("ERROR", e)
        print(f"api maps: {len(maps(root))} maps, {len(load(root))} registry entries, "
              f"{'OK' if not errs else f'{len(errs)} problems'}")
        return 1 if errs else 0
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
