#!/usr/bin/env python3
"""No planning IDs in Lean folder names, file names or declaration names (hard rule 9 of
CONTRIBUTING.md). Files go in subject folders and are named by what they formalise.

A planning ID is any of:
  * a gap row ID of the old plan: `G1-007`, written `G1_007` in Lean;
  * a milestone ID, a row of docs/tasks/milestones.md: `GE3`, `SF5a`, `OP2`, as a name part in
    capitals (`OP2Summary`, `T_GE3`); in lower case it is not caught (`mm3` is also a 3 x 3 matrix
    product), so `op2_summary` is a reviewer's catch;
  * a row number: an area code with `Row` (`HARow055`, `GERow016`, `SP3Row`), `Row` with digits,
    and a folder named `Rows` or ending in `Row` (`PeterWeylRow`);
  * a catalogue ID: `LL-0031`, `LL0031`, `LL_0031`.

Under Lightlike/ the check reads every folder and file name, and the namespaces and declaration
names of the .lean files (from the source text, so it needs no build). Docstrings and comments may
name IDs. A deprecated alias that keeps a renamed declaration's old name for one release
(`@[deprecated (since := "0.4.0")] alias Old := New`) passes when its new name has no ID. The proof-task statements in Tasks/ are named by their task ID on purpose (`T_QU1_P5`
is their public handle), so there only gap IDs and a `Rows` folder count. A name such as `SixJRow`
(a row of a recurrence) is mathematics, not a planning ID: only a folder name is checked for a bare
`Row`.

  python3 -I scripts/planning_ids.py              # exit 1, one line per name, when one is found
  python3 -I scripts/planning_ids.py --selftest
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GAP_ID = re.compile(r"(?<![A-Za-z0-9])G[0-9]+[_-][0-9]{3}(?![0-9])")
CATALOGUE_ID = re.compile(r"(?<![A-Z])LL[_-]?[0-9]{4}(?![0-9])|(?<![A-Za-z0-9])ll_?[0-9]{4}(?![0-9])")
ROW = re.compile(r"(?<![A-Za-z])[A-Z]{2}[0-9]*[a-z]?Rows?(?![a-z])|Rows?[0-9]")
MILESTONE_ROW = re.compile(r"^\| ([A-Z]{1,4}[0-9]+[a-z]?) \|", re.M)
# a name part: an upper-case run with digits (`OP2`, `SF5a`), an upper-case run, a word, digits
PART = re.compile(r"[A-Z]+[0-9]+[a-z]?(?![a-z])|[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+")
DECL_LINE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
                       r"(namespace|theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|irreducible_def|alias)"
                       r"\s+([^\s:({\[⦃]+)")
DEPRECATED_ALIAS = re.compile(r"^\s*@\[deprecated\b[^\]]*\]\s*alias\s+\S+\s*:=\s*(\S+)")


def milestone_ids(root: pathlib.Path) -> set[str]:
    p = root / "docs/tasks/milestones.md"
    return set(MILESTONE_ROW.findall(p.read_text(encoding="utf-8"))) if p.is_file() else set()


def name_ids(name: str, ids: set[str]) -> list[str]:
    """The planning IDs in one name (a path component without `.lean`, or a Lean name)."""
    found = GAP_ID.findall(name) + CATALOGUE_ID.findall(name) + ROW.findall(name)
    for chunk in re.split(r"[^A-Za-z0-9]+", name):
        found += [t for t in PART.findall(chunk) if t in ids]
    return sorted(set(found))


def folder_row(name: str) -> bool:
    words = PART.findall(name)
    return bool(words) and (words[-1] in ("Row", "Rows") or "Rows" in words)


def check(root: pathlib.Path = ROOT) -> list[str]:
    ids = milestone_ids(root)
    out = []
    base = root / "Lightlike"
    for p in sorted(base.rglob("*")) if base.is_dir() else []:
        rel = p.relative_to(root)
        if p.is_dir():
            bad = name_ids(p.name, ids) + (["Row"] if folder_row(p.name) else [])
            if bad:
                out.append(f"{rel}/: folder name has {', '.join(sorted(set(bad)))}")
            continue
        if p.suffix != ".lean":
            continue
        bad = name_ids(p.stem, ids)
        if bad:
            out.append(f"{rel}: file name has {', '.join(bad)}")
        for n, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            m = DECL_LINE.match(line)
            old = DEPRECATED_ALIAS.match(line)
            if old and not name_ids(old.group(1), ids):
                continue
            if m:
                bad = name_ids(m.group(2), ids)
                if bad:
                    out.append(f"{rel}:{n}: {m.group(1)} {m.group(2)} has {', '.join(bad)}")
    tasks = root / "Tasks"
    for p in sorted(tasks.rglob("*")) if tasks.is_dir() else []:
        rel = p.relative_to(root)
        part = p.name if p.is_dir() else p.stem
        if GAP_ID.search(part) or part == "Rows":
            out.append(f"{rel}: name has a gap ID or Rows")
        if p.suffix == ".lean":
            for n, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
                m = DECL_LINE.match(line)
                if m and (GAP_ID.search(m.group(2)) or re.search(r"(?:^|\.)Rows(?:\.|$)", m.group(2))):
                    out.append(f"{rel}:{n}: {m.group(1)} {m.group(2)} has a gap ID or Rows")
    return out


def selftest() -> int:
    fails = []

    def expect(what, cond):
        if not cond:
            fails.append(what)
            print("FAIL", what)

    with tempfile.TemporaryDirectory() as d:
        r = pathlib.Path(d)
        (r / "docs/tasks").mkdir(parents=True)
        (r / "docs/tasks/milestones.md").write_text("| ID | Title |\n|---|---|\n| OP2 | Fock |\n| SF5a | X |\n| GE3 | Y |\n")
        files = {
            "Lightlike/Rows/G1_007/A.lean": "namespace Lightlike.Rows.G1_007\ntheorem t : True := trivial\n",
            "Lightlike/Spacetime/GE3Row/Conjugate.lean": "namespace Lightlike.Geodesic\n",
            "Lightlike/Harmonic/PeterWeylRow/Acceptance.lean": "namespace Lightlike.HarmonicAnalysis\n",
            "Lightlike/Lorentz/Orbits/Summary.lean": "namespace Lightlike.Lorentz.HARow055\n",
            "Lightlike/OperatorAlgebras/OP2Summary.lean": "theorem op2_summary : True := trivial\n"
                                                          "def boundLL0031 : Nat := 0\ndef ll_0356_note : Nat := 0\n"
                                                          "def mm3 : Nat := 0\n",
            "Lightlike/TuraevViro/SixJRow.lean": "theorem sixJRow_rec : True := trivial\n-- milestone SF5a, row G1-007, LL-0031\n"
                                                 "/-- see GE3 -/\ntheorem SU2_spin : True := trivial\ntheorem SF5ab : True := trivial\n",
            "Lightlike/Asymptotics/FreeBoson/Growth.lean": "namespace Lightlike.Asymptotics.FreeBosonGrowth\n",
            "Lightlike/Lorentz/WignerOrbits/Old.lean": '@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_007.t'
                                                       " := _root_.Lightlike.Lorentz.WignerOrbits.t\n"
                                                       "alias Lightlike.Lorentz.HARow055.t := t\n"
                                                       "@[deprecated] alias Lightlike.Rows.G1_007.u := Lightlike.Rows.G1_007.t\n",
            "Tasks/GE/T_GE3_P1.lean": "theorem Lightlike.Tasks.T_GE3_P1 : True := trivial\n",
            "Tasks/GE/T_G1_007.lean": "theorem t : True := trivial\n",
        }
        for k, v in files.items():
            (r / k).parent.mkdir(parents=True, exist_ok=True)
            (r / k).write_text(v)
        hits = check(r)
        joined = "\n".join(hits)
        expect("a Rows folder and a gap-ID folder, namespace", "Lightlike/Rows/: folder" in joined
               and "Lightlike/Rows/G1_007/: folder name has G1_007" in joined and "namespace Lightlike.Rows.G1_007" in joined)
        expect("an area code with Row and a folder ending in Row", "GE3Row/: folder name has GE3, GE3Row" in joined
               and "PeterWeylRow/: folder name has Row" in joined)
        expect("a row number in a namespace", "namespace Lightlike.Lorentz.HARow055 has HARow" in joined)
        expect("a milestone ID in a file name, catalogue IDs; lower case (op2, mm3) is not caught",
               "OP2Summary.lean: file name has OP2" in joined and "boundLL0031 has LL0031" in joined
               and "ll_0356_note has ll_0356" in joined and "op2_summary" not in joined and "mm3" not in joined)
        expect("SixJRow, SU2, SF5ab, comments, docstrings and a subject folder pass",
               "SixJRow" not in joined and "SU2" not in joined and "SF5ab" not in joined and "FreeBoson" not in joined)
        expect("a task file named by its task ID passes; a gap ID in Tasks fails",
               "T_GE3_P1" not in joined and "Tasks/GE/T_G1_007.lean: name has a gap ID" in joined)
        expect("a deprecated alias keeping an old name passes; a plain alias, or one whose new name has an ID, fails",
               "Old.lean:1:" not in joined and "Old.lean:2: alias Lightlike.Lorentz.HARow055.t has HARow" in joined
               and "Old.lean:3: alias Lightlike.Rows.G1_007.u has G1_007" in joined)
        expect("nothing else", len(hits) == 12 or print(joined) or False)
        (r / "Lightlike").rename(r / "Gone")
        (r / "Tasks").rename(r / "Gone2")
        expect("an empty tree passes", check(r) == [])
    print("selftest:", "OK" if not fails else f"FAILED ({len(fails)})")
    return 1 if fails else 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--root", type=pathlib.Path, default=ROOT)
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    hits = check(a.root)
    for h in hits:
        print(h)
    print(f"planning IDs: {len(hits)} name(s) found" if hits else "planning IDs: none in Lean folder, file or declaration names")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
