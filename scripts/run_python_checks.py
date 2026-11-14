#!/usr/bin/env python3
"""Runs the Python cross-checks of scripts/ and reports pass/fail per script.

Each script exits 0 only when its values agree and its wrong-input controls are detected. So a
listed script must be able to exit nonzero: it needs a sys.exit, raise or assert (checked
statically; NO_EXIT_BASELINE lists the scripts that still lack one, and it only shrinks). A script
that exits 0 while its last output line says FAIL or FAILED fails too.
Install the pinned versions first:  python3 -m venv .venv && .venv/bin/pip install -r requirements.txt

  python3 -I scripts/run_python_checks.py          # quick set (about 3 min)
  python3 -I scripts/run_python_checks.py --all    # also the slow scripts (about 10 min more)
  python3 -I scripts/run_python_checks.py --list   # list the scripts and whether they are slow

Exit 0 = all selected scripts passed. A script missing from the list below, or a listed script
that does not exist, is an error (so a new cross-check cannot be forgotten)."""
import argparse, ast, importlib.util, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
# (path, slow?) -- slow = more than about 60 s on a laptop
CHECKS = [
    ("scripts/be_check.py", False), ("scripts/be_symmetry_check.py", True),
    ("scripts/pentagon_dict_check.py", False), ("scripts/pr14_check.py", False),
    ("scripts/pr23_check.py", False), ("scripts/pr_asymptotics.py", False),
    ("scripts/pr_tree_check.py", False), ("scripts/sixj_zero_check.py", False),
    ("scripts/wrong_schwarzschild_check.py", False), ("scripts/tv_check.py", False),
    ("scripts/asymptotics/eprl_asymptotics_check.py", False),
    ("scripts/asymptotics/pr_hypotheses_search.py", False),
    ("scripts/asymptotics/saddle_identities.py", False),
    ("scripts/lorentz/casimir_check.py", False),
    ("scripts/recoupling/fifteenj_check.py", True),
    ("scripts/recoupling/fifteenj_orth_check.py", False),
    ("scripts/recoupling/intertwiner_check.py", False), ("scripts/recoupling/ladder_check.py", False),
    ("scripts/regge/distance_expansion_check.py", False),
    ("scripts/regge/regge2d_convergence.py", True), ("scripts/regge/regge4_check.py", False),
    ("scripts/regge/regge4_numerics.py", False), ("scripts/regge/regge_equations_check.py", False),
    ("scripts/regge/schlaefli_check.py", False), ("scripts/spin4/coherent_check.py", True),
    ("scripts/spin4/eprl_check.py", False), ("scripts/spin4/spin4_check.py", False),
    ("scripts/spin4/vertex_check.py", False),
    ("scripts/asymptotics/closing_check.py", False),
    ("scripts/asymptotics/contour_identity_check.py", False),
    ("scripts/asymptotics/gamma_bounds_check.py", False),
    ("scripts/asymptotics/kernel_bound_check.py", False),
    ("scripts/asymptotics/landing_check.py", False),
    ("scripts/asymptotics/level_check.py", False),
    ("scripts/asymptotics/racah_sum_asymptotics.py", False),
    ("scripts/asymptotics/stirling_check.py", False),
    ("scripts/asymptotics/valley_check.py", False),
    ("scripts/lorentz/eprl_check.py", False),
    ("scripts/lorentz/limit_formula_check.py", False),
    ("scripts/lorentz/plancherel_check.py", True),
    ("scripts/lorentz/radial_check.py", False),
    ("scripts/lorentz/sl2r_check.py", True),
    ("scripts/lorentz/spherical_check.py", False),
    ("scripts/oscillatory/gauss_check.py", False),
    ("scripts/oscillatory/laplace_check.py", False),
    ("scripts/oscillatory/localisation_check.py", False),
    ("scripts/oscillatory/phasered_check.py", False),
    ("scripts/oscillatory/quadphase_check.py", False),
    ("scripts/oscillatory/stationary_check.py", False),
    ("scripts/pl/surf_chains.py", False),
    ("scripts/recoupling/ooguri_moves_check.py", True),
    ("scripts/regge/midpoint_sixth_check.py", True),
    ("scripts/spinfoam/vertex_check.py", False),
]
# Scripts that are not cross-checks (tools, the gate itself)
NOT_CHECKS = {"scripts/ci_check.py", "scripts/prune_docs.py", "scripts/gate.py", "scripts/sixj_support.py", "scripts/tooling_selftest.py",
              "scripts/run_python_checks.py", "scripts/api_map.py",
              "scripts/leansrc.py", "scripts/proof_task_check.py", "scripts/tasks.py",
              "scripts/sources.py", "scripts/doc_refs_check.py",
              "scripts/pl/check_chain.py",  # a library of surf_chains.py
              "scripts/pl/surf_search.py"}  # a search tool; its results are checked by surf_chains.py


# Listed scripts with no way to exit nonzero: they print their verdict only. Shrink-only: remove a
# script when it gains an exit path (the runner warns); a script not listed here must have one.
NO_EXIT_BASELINE = {
    "scripts/regge/regge2d_convergence.py", "scripts/regge/regge4_check.py",
    "scripts/regge/regge4_numerics.py", "scripts/regge/regge_equations_check.py",
    "scripts/regge/schlaefli_check.py",
}
FAIL_VERDICT = re.compile(r"\bFAIL(?:ED)?\b")


REQUIRED = ["numpy", "mpmath", "sympy", "scipy", "yaml"]  # yaml: used by gate.py and the self-test


def missing_packages(names=None) -> list[str]:
    return [n for n in (REQUIRED if names is None else names) if importlib.util.find_spec(n) is None]


def has_exit_path(path: str) -> bool:
    """True if the script contains a raise, an assert or a call to sys.exit, exit or SystemExit."""
    for n in ast.walk(ast.parse((ROOT / path).read_text(encoding="utf-8"))):
        if isinstance(n, (ast.Raise, ast.Assert)):
            return True
        if isinstance(n, ast.Call):
            f = n.func
            if (f.attr if isinstance(f, ast.Attribute) else getattr(f, "id", "")) in {
                    "exit", "_exit", "quit", "SystemExit"}:
                return True
    return False


def exit_path_problems() -> tuple[list[str], list[str]]:
    """(errors, warnings): listed scripts that cannot exit nonzero; stale baseline entries."""
    listed = {c for c, _ in CHECKS if (ROOT / c).exists()}
    errors = [f"{c}: no exit path (sys.exit, raise or assert), so a failing check exits 0"
              for c in sorted(listed - NO_EXIT_BASELINE) if not has_exit_path(c)]
    warnings = [f"{c}: has an exit path now; remove it from NO_EXIT_BASELINE"
                for c in sorted(listed & NO_EXIT_BASELINE) if has_exit_path(c)]
    warnings += [f"{c}: in NO_EXIT_BASELINE but not listed in CHECKS"
                 for c in sorted(NO_EXIT_BASELINE - listed)]
    return errors, warnings


def verdict_failed(stdout: str) -> bool:
    """True if the last nonempty output line says FAIL or FAILED."""
    lines = [l for l in stdout.splitlines() if l.strip()]
    return bool(lines) and bool(FAIL_VERDICT.search(lines[-1]))


def unlisted() -> list[str]:
    on_disk = {str(p.relative_to(ROOT)) for p in (ROOT / "scripts").rglob("*.py")
               if "health" not in p.parts}
    return sorted(on_disk - {c for c, _ in CHECKS} - NOT_CHECKS)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true", help="include the slow scripts")
    ap.add_argument("--list", action="store_true")
    a = ap.parse_args()
    miss = missing_packages()
    if miss and not a.list:
        print(f"Missing Python packages: {', '.join(miss)}. Install the pinned versions: "
              f"see the header of requirements.txt.")
        return 2
    problems = [f"{c}: listed but missing" for c, _ in CHECKS if not (ROOT / c).exists()]
    problems += [f"{c}: not in run_python_checks.py (add it to CHECKS or NOT_CHECKS)" for c in unlisted()]
    exit_errors, exit_warnings = exit_path_problems()
    problems += exit_errors
    if a.list:
        for c, slow in CHECKS:
            print(("slow  " if slow else "quick ") + c)
        return 0
    failed = []
    for c, slow in CHECKS:
        if slow and not a.all:
            print(f"skip {c} (slow; use --all)")
            continue
        t = time.time()
        r = subprocess.run([sys.executable, "-I", str(ROOT / c)], capture_output=True, text=True,
                           cwd=ROOT)
        bad = r.returncode != 0 or verdict_failed(r.stdout)
        why = "" if not bad or r.returncode else ", exit 0 but the last line says FAIL"
        print(f"{'FAIL' if bad else 'ok  '} {c} ({time.time() - t:.0f}s{why})")
        if bad:
            failed.append(c)
            print("\n".join((r.stdout + r.stderr).splitlines()[-8:]))
    for p in problems:
        print("FAIL", p)
    for w in exit_warnings:
        print("warning:", w)
    print("OK: all Python checks pass" if not failed and not problems
          else f"FAILED: {len(failed)} scripts, {len(problems)} list problems")
    return 1 if failed or problems else 0


if __name__ == "__main__":
    sys.exit(main())
