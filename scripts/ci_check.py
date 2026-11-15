#!/usr/bin/env python3
"""Trust checks for Lightlike (run by CI, usable locally).

1. Source scan: no `sorry`, `admit`, `native_decide`, `axiom` declarations, `implemented_by` or
   `extern` in any Lean source under Lightlike/ (comments and string literals are ignored).
2. Build log (optional): no "declaration uses 'sorry'" warning and no error.
3. Reachability: every Lean file under Lightlike/ is imported, directly or through
   other modules, by `Lightlike.lean`; an unreachable module is neither built nor audited.
   `lake exe mk_all --lib Lightlike` adds the missing imports.
4. Deprecations (needs --build-log): a warning, never a failure, for deprecation warnings in the
   build log beyond the counts per file recorded in `scripts/deprecation_baseline.txt`.
5. Test coverage: a warning, never a failure, for every declaration of a result in
   `docs/results.yaml` that no Tests/ directory file and no `*Tests.lean` file mentions.
6. Exploratory imports: no Lean module outside an `Exploratory/` folder imports, directly or
   through other modules, a module inside one. Exempt are the build roots that only collect
   modules (`Lightlike.lean` and `Exploratory.lean` files).
7. Finite heartbeats: no `maxHeartbeats 0` (unlimited elaboration time and memory) in any Lean
   source under Lightlike/. Files listed in `scripts/heartbeats_baseline.txt` may keep exactly
   the listed number of uses until they are bounded; the list may only shrink, so a listed count
   that no longer matches the file also fails. The list is empty before v0.2.0.

Checks 1-3, 6 and 7 are hard rules (CONTRIBUTING.md); 4 and 5 only print warnings. The axioms of
every declaration are checked by `scripts/AxiomAudit.lean`.

Usage (local):
  lake build 2>&1 | tee build.log
  python3 scripts/ci_check.py --build-log build.log
Exit code 0 = all checks pass; 1 = a check failed (details printed).
"""
import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
FORBIDDEN = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*axiom\b",
                re.M), "axiom declaration"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
    (re.compile(r"@\[\s*extern\b"), "extern"),
]


def strip_comments(src: str) -> str:
    """Blank out Lean comments (`--`, nested `/- -/`) and string literals, keeping newlines."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            seg = src[i:j + 1]
            out.append("".join("\n" if c == "\n" else " " for c in seg))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def scan_sources() -> list[str]:
    errors = []
    files = sorted((ROOT / "Lightlike").rglob("*.lean")) + [ROOT / "Lightlike.lean"]
    for f in files:
        code = strip_comments(f.read_text(encoding="utf-8"))
        for pat, name in FORBIDDEN:
            for m in pat.finditer(code):
                line = code.count("\n", 0, m.start()) + 1
                errors.append(f"{f.relative_to(ROOT)}:{line}: forbidden `{name}`")
    print(f"[source] scanned {len(files)} files: {len(errors)} forbidden tokens")
    return errors


UNLIMITED = re.compile(r"\bmaxHeartbeats\s+0\b")
HEARTBEATS_BASELINE = ROOT / "scripts" / "heartbeats_baseline.txt"


def check_heartbeats(root: pathlib.Path = ROOT, baseline_path: pathlib.Path = HEARTBEATS_BASELINE
                     ) -> list[str]:
    """Check 7: count `maxHeartbeats 0` per file (comments ignored) against the baseline."""
    found = {}
    for f in sorted((root / "Lightlike").rglob("*.lean")) + [root / "Lightlike.lean"]:
        if not f.exists():
            continue
        n = len(UNLIMITED.findall(strip_comments(f.read_text(encoding="utf-8"))))
        if n:
            found[str(f.relative_to(root))] = n
    baseline = read_baseline(baseline_path)
    errors = []
    for rel in sorted(set(found) | set(baseline)):
        have, allowed = found.get(rel, 0), baseline.get(rel, 0)
        if have > allowed:
            errors.append(f"{rel}: {have} uses of `maxHeartbeats 0` (allowed {allowed}); "
                          "set a finite limit, e.g. `set_option maxHeartbeats 400000 in`")
        elif have < allowed:
            errors.append(f"{rel}: {have} uses of `maxHeartbeats 0`, baseline says {allowed}; "
                          f"lower its line in {baseline_path.relative_to(root)}")
    print(f"[heartbeats] {sum(found.values())} uses of `maxHeartbeats 0` in {len(found)} files "
          f"(baseline {sum(baseline.values())})")
    return errors


DEPRECATED = re.compile(r"^warning: (\S+?):\d+:\d+: .*(?:has been|is) deprecated", re.M)
BASELINE = ROOT / "scripts" / "deprecation_baseline.txt"


def read_baseline(path: pathlib.Path) -> dict[str, int]:
    """`path count` per line; `#` starts a comment."""
    out = {}
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.split("#")[0].split()
            if len(line) == 2:
                out[line[0]] = int(line[1])
    return out


def check_deprecations(text: str, baseline: dict[str, int]) -> list[str]:
    """Deprecation warnings per file beyond the recorded baseline."""
    counts: dict[str, int] = {}
    for f in DEPRECATED.findall(text):
        counts[f] = counts.get(f, 0) + 1
    errors = [f"deprecation: {f} has {n} deprecation warnings (baseline {baseline.get(f, 0)}); "
              f"fix them or, for a known case, record them in scripts/deprecation_baseline.txt"
              for f, n in sorted(counts.items()) if n > baseline.get(f, 0)]
    stale = [f for f, n in baseline.items() if counts.get(f, 0) < n]
    for f in stale:
        print(f"[deprecations] note: {f} has fewer warnings than its baseline; lower the entry")
    print(f"[deprecations] {sum(counts.values())} warnings in {len(counts)} files "
          f"(baseline {sum(baseline.values())}), {len(errors)} files over baseline")
    return errors


def check_build_log(path: str) -> list[str]:
    text = pathlib.Path(path).read_text(encoding="utf-8", errors="replace")
    for w in check_deprecations(text, read_baseline(BASELINE)):
        print("WARN", w)
    errors = []
    if "declaration uses 'sorry'" in text:
        errors.append("build log: a declaration uses 'sorry'")
    for line in text.splitlines():
        if re.search(r"(^|\s)error(:|\()", line):
            errors.append(f"build log: {line.strip()[:200]}")
    if "Build completed successfully" not in text:
        errors.append("build log: no 'Build completed successfully' line")
    print(f"[build] {len(errors)} problems")
    return errors


IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(Lightlike[\w.]*)",
                       re.M)
IMPORT_ANY = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)


def check_reachability(root: pathlib.Path = ROOT) -> list[str]:
    """Lean files under Lightlike/ that `Lightlike.lean` does not import (transitively)."""
    files = {str(f.relative_to(root))[:-5].replace("/", "."): f
             for f in (root / "Lightlike").rglob("*.lean")}
    files["Lightlike"] = root / "Lightlike.lean"
    seen, stack = set(), ["Lightlike"]
    while stack:
        m = stack.pop()
        if m in seen or m not in files:
            continue
        seen.add(m)
        stack += IMPORT_RE.findall(strip_comments(files[m].read_text(encoding="utf-8")))
    errors = [f"{files[m].relative_to(root)} is not imported by Lightlike.lean (directly or "
              f"through other modules), so it is neither built nor audited"
              for m in sorted(files) if m not in seen]
    print(f"[reachability] {len(files)} modules, {len(errors)} unreachable")
    return errors


def is_test_file(rel: str) -> bool:
    return "/Tests/" in rel or rel.endswith("Tests.lean") or rel.endswith("/Tests.lean")


def check_test_coverage(root: pathlib.Path = ROOT) -> list[str]:
    """Warnings: declarations of results in docs/results.yaml mentioned by no test file.
    Matching is by the last component of the name, as a whole word, in comment-stripped code."""
    registry = root / "docs" / "results.yaml"
    names = [n.strip() for line in re.findall(r"^\s*decls:\s*\[([^\]]*)\]",
                                              registry.read_text(encoding="utf-8"), re.M)
             for n in line.split(",") if n.strip()] if registry.exists() else []
    tests = {str(f.relative_to(root)): strip_comments(f.read_text(encoding="utf-8"))
             for f in (root / "Lightlike").rglob("*.lean")
             if is_test_file(str(f.relative_to(root)))}
    warns, total = [], 0
    for name in names:
        total += 1
        short = re.escape(name.split(".")[-1])
        if not any(re.search(rf"(?<![\w.']){short}(?![\w']|\.)", c) for c in tests.values()):
            warns.append(name)
    print(f"[test coverage] {total} result declarations, {len(warns)} mentioned by no test file")
    return warns


def check_exploratory_imports(root: pathlib.Path = ROOT) -> list[str]:
    """Modules outside an Exploratory/ folder that import one inside it, directly or transitively."""
    files = {str(f.relative_to(root))[:-5].replace("/", "."): f
             for d in ("Lightlike", "Tasks", "Tests", "scripts") if (root / d).is_dir()
             for f in (root / d).rglob("*.lean")}
    for f in root.glob("*.lean"):
        files[f.stem] = f
    imports = {m: set(IMPORT_ANY.findall(strip_comments(f.read_text(encoding="utf-8"))))
               for m, f in files.items()}
    is_exp = lambda m: "Exploratory" in m.split(".")[:-1]  # noqa: E731
    exempt = lambda m: is_exp(m) or m == "Lightlike" or m.split(".")[-1] == "Exploratory"  # noqa: E731
    memo: dict[str, set[str]] = {}

    def reach(m, path=()):
        if m not in memo:
            memo[m] = set()
            for i in imports.get(m, ()):
                if is_exp(i) or i.split(".")[-1] == "Exploratory":
                    memo[m].add(i)
                if i in files and i not in path:
                    memo[m] |= reach(i, path + (m,))
        return memo[m]
    errors = [f"{files[m].relative_to(root)} imports {sorted(reach(m))[0]} (Exploratory is never "
              f"imported outside Exploratory/)" for m in sorted(files) if not exempt(m) and reach(m)]
    print(f"[exploratory] {sum(map(is_exp, files))} exploratory modules, {len(errors)} bad imports")
    return errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--build-log")
    ap.add_argument("--list-untested", action="store_true",
                    help="print every result declaration that no test file mentions (warnings)")
    args = ap.parse_args()
    errors = scan_sources()
    errors += check_reachability()
    errors += check_exploratory_imports()
    errors += check_heartbeats()
    for w in check_test_coverage()[:None if args.list_untested else 0]:
        print("WARN not mentioned by any test file:", w)
    if args.build_log:
        errors += check_build_log(args.build_log)
    for e in errors:
        print("FAIL", e)
    print("OK: all checks pass" if not errors else f"FAILED: {len(errors)} problems")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
