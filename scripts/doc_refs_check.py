#!/usr/bin/env python3
"""Checks the references in the comments and docstrings of the Lean files and of the numerical
cross-checks in `scripts/` (run by CI, usable locally).

1. File paths: a path with a folder (`Lightlike/SU2/SpinRep.lean`) exists from the repository
   root, or, for `Mathlib/...` and `Physlib/...`, in that package under `.lake/packages/`. A bare
   file name (`SpinRep.lean`) is a file in the same folder or the only tracked file of that name.
2. Status claims: a clause that says something is not proven, open, conjectured or planned
   names no theorem of `Lightlike/`, since every theorem there is proven (CI rejects `sorry`),
   and no declaration of a `proven` result in `docs/results.yaml`. A clause that says something
   is proven, without a condition (`given`, `if`, `follows`, ...), names no declaration of a
   `stated` result.

The status check reads clauses, so it can miss a claim worded in an unusual way; it does not
flag a sentence that names a theorem only to say that it is proven.

Usage: python3 scripts/doc_refs_check.py [--root DIR]
Exit code 0 = no problem found; 1 = problems (printed with file and line).
"""
import argparse
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import api_map  # noqa: E402
import leansrc  # noqa: E402

# Maintainer tools: their file names are fixtures and command-line examples, not references.
TOOLING = {"ci_check.py", "proof_task_check.py", "tooling_selftest.py", "run_python_checks.py",
           "gate.py", "tasks.py", "api_map.py", "sources.py", "prune_docs.py", "leansrc.py",
           "sixj_support.py", "doc_refs_check.py", "milestone_status.py", "sync_github.py",
           "consistency_check.py"}
PACKAGES = {"Mathlib": ".lake/packages/mathlib", "Physlib": ".lake/packages/Physlib",
            "PhyslibAlpha": ".lake/packages/Physlib"}
PATH = re.compile(r"(?<![\w./-])((?:[\w.-]+/)*[\w-][\w.-]*\.(?:lean|py|md|yaml|yml|json|toml|txt))"
                  r"(?![\w/])")
NEGATIVE = re.compile(r"\b(not (yet )?(been )?(proven|proved|formali[sz]ed)|unproven|is open|"
                      r"remains open|are open|still open|open problem|conjectur\w*|planned)\b", re.I)
POSITIVE = re.compile(r"\b(proven|proved)\b", re.I)
CONDITIONAL = re.compile(r"\b(follows|given|assum\w*|if|under|conditional|hypothes[ie]s)\b", re.I)
TICK = re.compile(r"`([^`\s]+)`")
THEOREM = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*(?:theorem|lemma)\s+([^\s(:{\[]+)",
                     re.M)


def tracked(root):
    out = subprocess.run(["git", "ls-files"], cwd=root, capture_output=True, text=True, check=True)
    return [pathlib.Path(f) for f in out.stdout.split()]


def scanned(files):
    """The files whose comments are checked: Lean files, and the numerical cross-checks."""
    return [f for f in files if f.suffix == ".lean"
            or (f.suffix == ".py" and f.parts[0] == "scripts" and f.name not in TOOLING)]


def comment_text(path, text):
    """`text` with code blanked out, keeping line breaks (Lean); Python files are read whole."""
    if path.suffix != ".lean":
        return text
    mask = leansrc.code_mask(text)
    return "".join(ch if (not c or ch == "\n") else " " for ch, c in zip(text, mask))


def check_paths(root, files):
    names = {}
    for f in files:
        names.setdefault(f.name, []).append(f)
    problems = []
    for f in scanned(files):
        text = comment_text(f, (root / f).read_text())
        for i, line in enumerate(text.split("\n"), 1):
            for m in PATH.finditer(line):
                p = m[1]
                if "/" in p:
                    head = p.split("/")[0]
                    if (root / p).exists():
                        continue
                    if head in PACKAGES:
                        pkg = root / PACKAGES[head]
                        if not pkg.exists() or (pkg / p).exists():
                            continue
                    problems.append(f"{f}:{i}: `{p}` does not exist (paths are from the repository root)")
                elif not (root / f.parent / p).exists() and len(names.get(p, [])) != 1:
                    where = ", ".join(str(x) for x in names.get(p, [])) or "no tracked file"
                    problems.append(f"{f}:{i}: `{p}` is not in {f.parent}/ ({where}); give its path")
    return problems


def sentences(text):
    """(line, sentence) pairs of a comment text: split at full stops, semicolons, blank lines and
    list items."""
    out, start, buf = [], 1, []
    for i, line in enumerate(text.split("\n"), 1):
        s = line.strip()
        if not s or re.match(r"^([*-]|\d+\.)\s", s) or s.startswith("#"):
            if buf:
                out.append((start, " ".join(buf)))
            buf, start = ([s] if s else []), i
            continue
        if not buf:
            start = i
        buf.append(s)
    if buf:
        out.append((start, " ".join(buf)))
    res = []
    for line, s in out:
        for part in re.split(r"(?<=[.;])\s+(?=[A-Z*(`])|;\s+|,\s+(?:so|but|while|whereas)\s+", s):
            res.append((line, part))
    return res


def matches(token, names):
    t = token.strip("()[],.:")
    return any(n == t or n.endswith("." + t) or t.endswith("." + n) for n in names.get(t.split(".")[-1], ()))


def check_claims(root, files):
    theorems = {}
    for f in files:
        if f.suffix == ".lean" and f.parts[0] == "Lightlike":
            for m in THEOREM.finditer((root / f).read_text()):
                theorems.setdefault(m[1].split(".")[-1], set()).add(m[1])
    proven, stated = {}, {}
    results = api_map.load(root)
    for r in results:
        for d in r.get("decls", []):
            target = proven if r.get("status") == "proven" else stated if r.get("status") == "stated" else None
            if target is not None:
                target.setdefault(d.split(".")[-1], set()).add(d)
    problems = []
    for f in scanned(files):
        if f.suffix != ".lean":
            continue
        text = comment_text(f, (root / f).read_text())
        for line, s in sentences(text):
            toks = TICK.findall(s)
            if not toks:
                continue
            if NEGATIVE.search(s):
                bad = [t for t in toks if matches(t, theorems) or matches(t, proven)]
                if bad:
                    problems.append(f"{f}:{line}: says not proven or open, but names the proven "
                                    f"{', '.join(f'`{b}`' for b in bad)}: {s[:120]}")
            elif POSITIVE.search(s) and not CONDITIONAL.search(s):
                bad = [t for t in toks if matches(t, stated) and not matches(t, theorems)]
                if bad:
                    problems.append(f"{f}:{line}: says proven, but {', '.join(f'`{b}`' for b in bad)} "
                                    f"is a stated result in docs/results.yaml: {s[:120]}")
    return problems


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=str(pathlib.Path(__file__).resolve().parent.parent))
    a = ap.parse_args(argv)
    root = pathlib.Path(a.root)
    files = tracked(root)
    problems = check_paths(root, files) + check_claims(root, files)
    for p in problems:
        print(p)
    n = len(scanned(files))
    print(f"doc_refs_check: {n} files, {len(problems)} problem(s)")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
