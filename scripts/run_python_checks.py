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
  python3 -I scripts/run_python_checks.py --changed FILE   # quick set + the slow checks a change touches
  python3 -I scripts/run_python_checks.py --all --jobs 4   # 4 scripts at a time (CI uses 4)

--changed FILE reads the changed paths, one per line (a pull request's `git diff --name-only`), and
runs the quick set plus every slow check whose script, or a scripts/ module it imports (directly or
through other scripts/ modules), is among them. A change to this runner, requirements.txt or the CI
workflow runs every check. The import match is generous: a name matches every scripts/ file it
could be imported as, so a doubtful case runs the check rather than skipping it. Data files a script
reads are not followed; main runs every check after each merge.

Exit 0 = all selected scripts passed. A script missing from the list below, or a listed script
that does not exist, is an error (so a new cross-check cannot be forgotten)."""
import argparse, ast, concurrent.futures, importlib.util, os, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
# (path, slow?) -- slow = more than about 60 s on a laptop
CHECKS = [
    ("scripts/adm_algebra_check.py", False), ("scripts/be_check.py", False), ("scripts/be_symmetry_check.py", True),
    ("scripts/pentagon_dict_check.py", False), ("scripts/pr14_check.py", False),
    ("scripts/pr23_check.py", False), ("scripts/pr_asymptotics.py", False),
    ("scripts/causal_sets/cs2_check.py", False), ("scripts/causal_sets/cs3_check.py", False), ("scripts/causal_sets/cs6_check.py", False), ("scripts/causal_sets/cs8_check.py", False), ("scripts/pr_tree_check.py", False), ("scripts/sixj_zero_check.py", False),
    ("scripts/wrong_schwarzschild_check.py", False), ("scripts/tv_check.py", False),
    ("scripts/flrw_check.py", False),
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
    ("scripts/asymptotics/link_integral_check.py", False),
    ("scripts/asymptotics/lorentzian_hessian_check.py", True),
    ("scripts/asymptotics/lorentzian_hessian_xx_certificate.py", False),
    ("scripts/asymptotics/lorentzian_hessian_closed_form_check.py", True),
    ("scripts/asymptotics/lorentzian_hessian_node_check.py", True),
    ("scripts/asymptotics/lorentzian_hessian_paper61_check.py", False),
    ("scripts/asymptotics/lorentzian_hessian_noncritical_check.py", False),
    ("scripts/asymptotics/lorentzian_hessian_kernel_check.py", False),
    ("scripts/asymptotics/lorentzian_regge_frequency_check.py", False),
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
    ("scripts/oscillatory/cy_moves_check.py", False),
    ("scripts/oscillatory/gauss_check.py", False),
    ("scripts/oscillatory/laplace_check.py", False),
    ("scripts/oscillatory/localisation_check.py", False),
    ("scripts/oscillatory/phasered_check.py", False),
    ("scripts/oscillatory/quadphase_check.py", False),
    ("scripts/oscillatory/stationary_check.py", False),
    ("scripts/pl/surf_chains.py", False),
    ("scripts/recoupling/ooguri_moves_check.py", True),
    ("scripts/regge/midpoint_sixth_check.py", True),
    ("scripts/regge/area_jacobian_check.py", False), ("scripts/regge/lorentzian_check.py", False),
    ("scripts/regge/regge3d_affine.py", False), ("scripts/regge/regge3d_core.py", False),
    ("scripts/regge/regge3d_jet.py", False), ("scripts/vertex_identity_check.py", False),
    ("scripts/regge/regge3d_g0_certificate.py", False),
    ("scripts/regge/regge3d_sphere_check.py", True),
    ("scripts/regge/regge3d_linearized_check.py", True),
    ("scripts/regge/fierz_pauli_check.py", True),
    ("scripts/regge/eh_jet_poly_check.py", True),
    ("scripts/regge/eh_wrong_model_check.py", True),
    ("scripts/qracah/qd_map_check.py", False), ("scripts/qracah/jhyp_coverage_check.py", False),
    ("scripts/qracah/jackson_degenerate_check.py", False),
    ("scripts/qracah/qd_coverage_check.py", False),
    ("scripts/spinfoam/vertex_check.py", False),
    ("scripts/spinfoam/bc_sign_check.py", False),
    ("scripts/spinfoam/bing_house_check.py", False),
    ("scripts/spinfoam/gauge_manifold_check.py", False),
    ("scripts/spinfoam/forcechain.py", True),
    ("scripts/spinfoam/forcing_cocycle_check.py", False),
    ("scripts/spinfoam/gauge_cutoff_limit.py", True),
    ("scripts/spinfoam/robust_check.py", False),
    ("scripts/spinfoam/robust_counterexample_verify.py", False),
    ("scripts/spinfoam/forcing_repair_check.py", False),
    ("scripts/spinfoam/gauge_independence_check.py", True),
    ("scripts/spinfoam/tetra_partition_check.py", False),
    ("scripts/spinfoam/eprl_node_check.py", False), ("scripts/spinfoam/eprl_high_check.py", False), ("scripts/spinfoam/u1_bubble.py", False),
    ("scripts/spinfoam/eprl_order_check.py", False),
    ("scripts/spinfoam/eprl_free_gluing_check.py", False),
]
# Scripts that are not cross-checks (tools, the gate itself)
NOT_CHECKS = {"scripts/ci_check.py", "scripts/prune_docs.py", "scripts/gate.py", "scripts/sixj_support.py", "scripts/tooling_selftest.py",
              "scripts/run_python_checks.py", "scripts/api_map.py",
              "scripts/leansrc.py", "scripts/proof_task_check.py", "scripts/comparator_run.py", "scripts/tasks.py",
              "scripts/contributors.py", "scripts/review_gate.py", "scripts/automerge.py",
              "scripts/sources.py", "scripts/doc_refs_check.py", "scripts/leak_check.py", "scripts/generated.py",
              "scripts/milestone_status.py",  # the status of the milestones (its selftest is in tooling_selftest.py)
              "scripts/sync_github.py",  # milestone issues and the Project board (its selftest is in tooling_selftest.py)
              "scripts/consistency_check.py",  # the task management against itself; needs GitHub and a built main (selftest in tooling_selftest.py)
              "scripts/planning_ids.py",  # rule 9: no planning ID in a Lean name; its own CI step (selftest in tooling_selftest.py)
              "scripts/regge/regge3d_convergence.py",  # a library of the regge3d_* checks (dihedral); its demo has no verdict
              "scripts/regge/gen_chart_change.py",  # generator of Lightlike/Regge/Conv3/ChartChangeClasses.lean
              "scripts/regge/gen_sv_sigma.py",  # generator of Lightlike/Regge/Linear3/SaintVenantSigma0..5.lean
              "scripts/regge/gen_star_angle.py",  # generator of the edge-class fans in Lightlike/Regge/Conv3/StarAngle.lean
              "scripts/regge/gen_kuhn_basis.py",  # generator of Lightlike/Regge/Conv3/KuhnBasis.lean from regge3d_g0_certificate.py
              "scripts/regge/gen_flat_star.py",  # generator of Lightlike/Regge/Conv3/FlatStar.lean (prints, no exit code)
              "scripts/pl/check_chain.py",  # a library of surf_chains.py
              "scripts/pl/surf_search.py",  # a search tool; its results are checked by surf_chains.py
              "scripts/spinfoam/exact3j.py",  # a library of gauge_cutoff_limit.py (exact 3j symbols)
              # q-Racah certificate pipeline: generators that write Lightlike/TuraevViro/Reflect/Racah*.lean
              # from intermediate files (parts.pkl, facs.out), run by hand from scripts/qracah
              "scripts/qracah/wz8.py", "scripts/qracah/size.py", "scripts/qracah/size2.py",
              "scripts/qracah/gen_cert.py", "scripts/qracah/gen_core.py", "scripts/qracah/gen_eval.py",
              "scripts/qracah/mu_check.py",  # needs parts.pkl from size2.py; prints, no exit code
              # numerical evidence that takes the level r on the command line and prints; no exit code
              "scripts/qracah/endrow_check.py", "scripts/qracah/jacobi_check.py",
              "scripts/qracah/orth_support.py",
              "scripts/qracah/chunk.py",  # splits the long Poly literals of the generated certificates; used by gen_cert.py
              "scripts/qracah/docs.py",  # module docstrings of the generated Racah files; used by gen_core.py
              "scripts/spinfoam/all15.py", "scripts/spinfoam/all24.py",  # print the reduction data of the 1-5 and 2-4 moves; Lean checks them
              "scripts/spinfoam/gen15.py", "scripts/spinfoam/gen24.py",  # generators of the Lean tables of Move15 and Move24
              "scripts/spinfoam/gauge_match.py", "scripts/spinfoam/net_model.py",  # libraries of the move searches
              "scripts/spinfoam/search15.py", "scripts/spinfoam/search24.py"}  # search tools; Lean checks what they find


# Listed scripts with no way to exit nonzero: they print their verdict only. Shrink-only: remove a
# script when it gains an exit path (the runner warns); a script not listed here must have one.
NO_EXIT_BASELINE: set[str] = set()
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


# A change to one of these runs every check (they decide how every check runs).
RUN_ALL_ON = {"scripts/run_python_checks.py", "requirements.txt", ".github/workflows/ci.yml"}


def module_index() -> dict:
    """Every dotted name a scripts/ file can be imported as -> the files it could be. A file
    scripts/a/b.py is `a.b` (from scripts/) and `b` (from scripts/a/, as the scripts that put their
    own folder or a sibling folder on sys.path import it)."""
    idx: dict = {}
    for f in (ROOT / "scripts").rglob("*.py"):
        parts = list(f.relative_to(ROOT / "scripts").with_suffix("").parts)
        if parts[-1] == "__init__":
            parts = parts[:-1]
        for k in range(len(parts)):
            idx.setdefault(".".join(parts[k:]), set()).add(f)
    return idx


def imported_names(f: pathlib.Path) -> set:
    """The module names a file imports (with their prefixes, and `from m import x` as m.x too)."""
    names = set()
    try:
        tree = ast.parse(f.read_text(encoding="utf-8"))
    except (OSError, SyntaxError, ValueError):
        return names
    for n in ast.walk(tree):
        mods = []
        if isinstance(n, ast.Import):
            mods = [a.name for a in n.names]
        elif isinstance(n, ast.ImportFrom):
            base = n.module or ""
            if n.level:  # relative: resolve against the file's own folder
                pkg = f.parent
                for _ in range(n.level - 1):
                    pkg = pkg.parent
                rel = ".".join(pkg.relative_to(ROOT / "scripts").parts) if pkg != ROOT / "scripts" else ""
                base = ".".join(x for x in (rel, base) if x)
            mods = [base] + [f"{base}.{a.name}" if base else a.name for a in n.names]
        for m in mods:
            ps = m.split(".")
            names.update(".".join(ps[:k]) for k in range(1, len(ps) + 1))
    return names


def local_deps(check: str, idx: dict) -> set:
    """The repository paths of a check script and every scripts/ module it imports, transitively."""
    seen, todo = set(), [ROOT / check]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        for name in imported_names(f):
            todo.extend(idx.get(name, ()))
    return {str(f.relative_to(ROOT)) for f in seen}


def select(changed: set) -> tuple:
    """(the checks to run, why) for a change: every check if it touches RUN_ALL_ON; otherwise the
    quick set plus the slow checks whose script or a scripts/ module they import changed."""
    hit = sorted(changed & RUN_ALL_ON)
    if hit:
        return [c for c, _ in CHECKS], f"every check: the change touches {', '.join(hit)}"
    idx = module_index()
    touched = [c for c, slow in CHECKS if slow and (ROOT / c).exists() and local_deps(c, idx) & changed]
    run = [c for c, slow in CHECKS if not slow or c in touched]
    return run, (f"the quick set and {len(touched)} slow check(s) the change touches"
                 + (f": {', '.join(touched)}" if touched else ""))


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def take_slot(root: str, n: int) -> str:
    """Wait for one of n slot directories under `root` (mkdir is atomic) and return its path. A slot
    whose owner process is gone is taken over. Several runs on one machine share the slots, so that
    together they run at most n scripts at a time, whatever --jobs each was given."""
    os.makedirs(root, exist_ok=True)
    while True:
        for i in range(n):
            d = os.path.join(root, f"slot{i}")
            try:
                os.mkdir(d)
            except FileExistsError:
                try:
                    owner = int(pathlib.Path(d, "pid").read_text())
                except (OSError, ValueError):
                    owner = None
                if owner is not None and not _alive(owner):
                    pathlib.Path(d, "pid").unlink(missing_ok=True)
                    try:
                        os.rmdir(d)
                    except OSError:
                        pass
                continue
            pathlib.Path(d, "pid").write_text(str(os.getpid()))
            return d
        time.sleep(2)


def run_one(c: str) -> tuple:
    """Runs one script. With LL_CHECK_SLOTS=<dir> (and LL_CHECK_SLOTS_N, default 6) it first takes a slot
    shared by every run that sets the same directory; the local gates do, so that nine of them do not
    run 36 scripts at once next to the Lean builds."""
    root = os.environ.get("LL_CHECK_SLOTS")
    slot = take_slot(root, max(1, int(os.environ.get("LL_CHECK_SLOTS_N", "6")))) if root else None
    try:
        t = time.time()
        r = subprocess.run([sys.executable, "-I", str(ROOT / c)], capture_output=True, text=True,
                           cwd=ROOT)
        return c, r, time.time() - t
    finally:
        if slot:
            pathlib.Path(slot, "pid").unlink(missing_ok=True)
            try:
                os.rmdir(slot)
            except OSError:
                pass


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true", help="include the slow scripts")
    ap.add_argument("--changed", metavar="FILE",
                    help="the changed paths, one per line: the quick set plus the slow checks they touch")
    ap.add_argument("--auto", action="store_true",
                    help="pull request or local gate: the checks the change selects (--changed); main: every check")
    ap.add_argument("--jobs", type=int, default=1, help="scripts run at a time (default 1)")
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
        picked = None
        if a.changed:  # with --changed, --list also says which checks the change selects
            picked = set(select({l.strip() for l in pathlib.Path(a.changed).read_text(encoding="utf-8").splitlines()
                                 if l.strip()})[0])
        for c, slow in CHECKS:
            print(("slow  " if slow else "quick ") + ("" if picked is None else ("RUN  " if c in picked else "skip ")) + c)
        return 0
    if a.auto:
        base = "HEAD^1" if os.environ.get("GITHUB_EVENT_NAME") == "pull_request" else os.environ.get("LL_GATE_BASE", "")
        diff = subprocess.run(["git", "-C", str(ROOT), "diff", "--name-only", base, "HEAD"],
                              capture_output=True, text=True) if base else None
        if diff is not None and diff.returncode == 0:
            run, reason = select({l.strip() for l in diff.stdout.splitlines() if l.strip()})
            reason += f" (changes since {base})"
            a.changed = a.changed or "auto"
        else:  # a push to main, an on-demand run, or no base to compare with: everything
            run, reason = [c for c, _ in CHECKS], "every check (no pull request to compare with)"
    elif a.all:
        run, reason = [c for c, _ in CHECKS], "every check (--all)"
    elif a.changed:
        changed = {l.strip() for l in pathlib.Path(a.changed).read_text(encoding="utf-8").splitlines()
                   if l.strip()}
        run, reason = select(changed)
    else:
        run, reason = [c for c, slow in CHECKS if not slow], "the quick set"
    run = [c for c in run if (ROOT / c).exists()]
    print(f"Running {len(run)} of {len(CHECKS)} checks, {max(1, a.jobs)} at a time: {reason}.")
    for c, slow in CHECKS:
        if c not in run and (ROOT / c).exists():
            print(f"skip {c} (slow; {'not touched by the change' if a.changed else 'use --all'})")
    slow_set = {c for c, slow in CHECKS if slow}
    order = sorted(run, key=lambda c: c not in slow_set)  # slow ones first: shorter wall time
    failed = []
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, a.jobs)) as pool:
        for c, r, secs in (f.result() for f in concurrent.futures.as_completed(
                [pool.submit(run_one, c) for c in order])):
            bad = r.returncode != 0 or verdict_failed(r.stdout)
            why = "" if not bad or r.returncode else ", exit 0 but the last line says FAIL"
            print(f"{'FAIL' if bad else 'ok  '} {c} ({secs:.0f}s{why})", flush=True)
            if bad:
                failed.append(c)
                print("\n".join((r.stdout + r.stderr).splitlines()[-8:]), flush=True)
    print(f"{len(run)} checks in {time.time() - t0:.0f}s")
    failed.sort(key=[c for c, _ in CHECKS].index)
    for c in failed:
        print("FAIL", c)
    for p in problems:
        print("FAIL", p)
    for w in exit_warnings:
        print("warning:", w)
    print("OK: all Python checks pass" if not failed and not problems
          else f"FAILED: {len(failed)} scripts, {len(problems)} list problems")
    return 1 if failed or problems else 0


if __name__ == "__main__":
    sys.exit(main())
