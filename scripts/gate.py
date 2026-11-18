#!/usr/bin/env python3
"""The local gate: runs the `run:` steps of .github/workflows/ci.yml in order, plus a
record of the result keyed to the commit.

The steps are read from ci.yml, so the gate and CI cannot drift apart:
  * a step with `uses:` (checkout, setup-python, cache) is CI-only and listed as such;
  * a `run:` step is executed with `bash -eo pipefail`, from the repository root;
  * a `run:` step whose name contains `[ci-only]` is not executed (for example installing elan);
  * every job runs, in the order of the file: the job keys that only steer CI (`needs`, `if`,
    `outputs`, `permissions`) are ignored;
  * `if:` and `env:` are allowed only on CI-only steps, which the gate does not run; on any other
    step they, and any other key the gate does not implement (`working-directory`, ...), are an
    error, so a step can never be skipped or misrun by accident;
  * a step with `continue-on-error: true` is advisory: a failure is recorded as WARN and the gate
    goes on (only the hard rules of CONTRIBUTING.md fail the gate). The last line names every
    advisory warning, `GATE OK (2 advisory warnings: [9] ..., [28] ...)`, and the step that
    failed the gate, `GATE FAILED at [19] ...`.
The steps run with the interpreter that runs the gate first on PATH, so `python3` in a step is
that interpreter (`venv/bin/python -I scripts/gate.py` makes the venv's `python3` the one every step
uses), then `~/.elan/bin`.
The tree must be clean, because the record names the commit.

Record: `.gate/log.jsonl` (untracked, git-ignored), one JSON line per run: commit, branch, start
time, each step with its return code and seconds, tool versions, `ok`. The last line is printed
at the end, ready to paste into a pull request. A tracked log would need a commit that changes the
hash it records.

  python3 -I scripts/gate.py              # run everything
  python3 -I scripts/gate.py --list       # show the steps and what the gate does with each
  python3 -I scripts/gate.py --full       # every Python cross-check (default: those the change since
                                          # origin/main selects, as CI does on a pull request)
  python3 -I scripts/gate.py --from N     # resume at step N (the record is marked partial)
  python3 -I scripts/gate.py --task T-QU1-P5   # fast mode for a proof-task pull request

Fast mode (`--task T-...-P<n>`) is for a contributor who proves one task. It runs, on the committed
tree: (1) no `sorry` in the task's declaration, (2) `proof_task_check.py` against `--base` (default
`origin/main`, else `main`): only the proof changed, the statement matches its lock, (3)
`lake build` of the task's module only, (4) `#print axioms` of the declaration: only the standard
three. It builds no other part of the library; CI does the full build, so a fast-mode record says
`mode: task <ID>` and is not a substitute for the full gate on a change to `Lightlike/`.
Exit 0 = every step passed on a clean tree."""
import argparse, json, os, pathlib, platform, subprocess, sys, time

HERE = pathlib.Path(__file__).resolve().parent
SUPPORTED = {"name", "id", "run", "uses", "with", "shell", "continue-on-error"}
CI_ONLY_KEYS = {"if", "env"}  # allowed on CI-only steps, which the gate does not run
JOB_KEYS = {"runs-on", "timeout-minutes", "defaults", "steps", "needs", "if", "outputs",
            "permissions"}


def load_steps(workflow: pathlib.Path) -> tuple[list[dict], list[str]]:
    try:
        import yaml
    except ImportError:
        sys.exit("gate: PyYAML is missing; install requirements.txt (see its header)")
    doc = yaml.safe_load(workflow.read_text(encoding="utf-8"))
    jobs = doc.get("jobs", {})
    steps, errors = [], []
    for jn, job in jobs.items():
        for k in job:
            if k not in JOB_KEYS:
                errors.append(f"job {jn}: unsupported key `{k}`")
        for i, st in enumerate(job.get("steps", []), 1):
            label = st.get("name") or st.get("uses") or f"step {i}"
            ci_only = "uses" in st or "[ci-only]" in label
            extra = set(st) - SUPPORTED - (CI_ONLY_KEYS if ci_only else set())
            if extra:
                errors.append(f"{label}: unsupported key(s) {sorted(extra)}; the gate would skip "
                              f"or misrun this step")
            if "run" not in st and "uses" not in st:
                errors.append(f"{label}: neither `run` nor `uses`")
            steps.append({"name": label, "run": st.get("run"), "uses": st.get("uses"),
                          "ci_only": ci_only,
                          "advisory": st.get("continue-on-error") is True})
    return steps, errors


def git(root, *a) -> str:
    return subprocess.run(["git", "-C", str(root), *a], capture_output=True, text=True,
                          check=True).stdout.strip()


def dirty(root, untracked=True) -> str:
    """Uncommitted changes, ignoring the gate's own record directory. After the steps ran, only
    tracked files count (steps write logs and caches)."""
    st = git(root, "status", "--porcelain", "--untracked-files=" + ("all" if untracked else "no"))
    return "\n".join(l for l in st.splitlines() if ".gate/" not in l)


def versions(root) -> dict:
    def out(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, text=True, cwd=root, env=env(),
                                  timeout=60).stdout.strip().splitlines()[0]
        except Exception:
            return "unavailable"
    v = {"python": platform.python_version(), "platform": platform.platform(),
         "lean": out(["lake", "env", "lean", "--version"])}
    for p in ("numpy", "mpmath", "sympy", "yaml"):
        try:
            v[p] = __import__(p).__version__
        except Exception:
            v[p] = "missing"
    tc = pathlib.Path(root) / "lean-toolchain"
    v["lean-toolchain"] = tc.read_text().strip() if tc.exists() else "none"
    return v


def env(py_base=None) -> dict:
    e = dict(os.environ)
    # The Python cross-check step runs `run_python_checks.py --auto`: with a base, only the checks the
    # change since that base selects (as CI does on a pull request); without one, every check.
    e.pop("LL_GATE_BASE", None)
    if py_base:
        e["LL_GATE_BASE"] = py_base
    # The steps run with the interpreter that runs the gate (its packages were checked), then elan.
    e["PATH"] = (os.path.dirname(sys.executable) + os.pathsep + str(pathlib.Path.home() / ".elan" / "bin")
                 + os.pathsep + e["PATH"])
    return e


STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_NOTE = ("   note: the self-test plants bad cases on purpose, so FAIL lines are expected in the\n"
                 "   output below; only its last line and the step result count")


def task_steps(root, tid, base):
    """The steps of fast mode for proof task `tid`: [(name, function returning a return code)]."""
    sys.path.insert(0, str(HERE))
    import proof_task_check as ptc
    import leansrc
    t = ptc.lookup(tid, root)
    if t is None or t.get("kind") != "proof":
        sys.exit(f"gate: {tid} is not a proof task in docs/tasks/tasks.yaml")
    file, decl = t["file"], t["decl"]
    module = file[:-len(".lean")].replace("/", ".")

    def no_sorry():
        text = (root / file).read_text()
        parts = ptc.split_block(text, decl.split(".")[-1])
        if parts is None:
            print(f"declaration {decl} not found exactly once in {file}")
            return 1
        body = "".join(ch if c else " " for ch, c in zip(parts[2], leansrc.code_mask(parts[2])))
        bad = sorted(set(ptc.FORBIDDEN.findall(body)))
        if bad:
            print(f"the proof of {decl} contains: {', '.join(bad)}")
            return 1
        print(f"no sorry or other forbidden word in the proof of {decl}")
        return 0

    def run(cmd):
        return subprocess.run(cmd, cwd=root, env=env(py_base)).returncode

    def check():
        return run([sys.executable, "-I", "scripts/proof_task_check.py", "--base", base, "--head", "HEAD",
                    "--task", tid])

    def build():
        return run(["lake", "build", module])

    def axioms():
        d = root / ".gate"
        d.mkdir(exist_ok=True)
        f = d / "axioms_task.lean"
        f.write_text(f"import {module}\n#print axioms {decl}\n")
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=root, env=env(), capture_output=True, text=True)
        out = r.stdout + r.stderr
        print(out.strip())
        if r.returncode != 0:
            return 1
        found = set()
        for l in out.splitlines():
            if "depends on axioms:" in l:
                found = {x.strip() for x in l.split("[", 1)[1].rstrip("]").split(",") if x.strip()}
        if found - STANDARD_AXIOMS or "sorryAx" in out:
            print("axioms beyond propext, Classical.choice, Quot.sound: " + ", ".join(sorted(found - STANDARD_AXIOMS)))
            return 1
        return 0

    return [("no sorry in the task's declaration", no_sorry),
            (f"only the proof changed, statement locked (proof_task_check, base {base})", check),
            (f"lake build {module}", build),
            (f"axioms of {decl}", axioms)]


def default_base(root):
    for ref in ("origin/main", "main"):
        if subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "-q", ref],
                          capture_output=True).returncode == 0:
            return ref
    sys.exit("gate: neither origin/main nor main exists; give --base")


def fast_mode(root, tid, base) -> int:
    if dirty(root):
        print("FAIL the working tree is not clean; commit first (the record names the commit)")
        return 3
    commit = git(root, "rev-parse", "HEAD")
    steps = task_steps(root, tid, base)
    rec = {"commit": commit, "branch": git(root, "rev-parse", "--abbrev-ref", "HEAD"),
           "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "steps": [],
           "mode": f"task {tid}", "partial": False, "versions": versions(root)}
    ok = True
    for i, (name, fn) in enumerate(steps, 1):
        print(f"== [{i}/{len(steps)}] {name}", flush=True)
        t = time.time()
        rc = fn()
        rec["steps"].append({"n": i, "name": name, "rc": rc, "seconds": round(time.time() - t),
                             "result": "ok" if rc == 0 else "FAIL"})
        if rc != 0:
            ok = False
            break
    if git(root, "rev-parse", "HEAD") != commit or dirty(root, untracked=False):
        ok = False
        rec["note"] = "the tree changed while the gate ran"
    rec["ok"] = ok
    rec["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    d = root / ".gate"
    d.mkdir(exist_ok=True)
    with open(d / "log.jsonl", "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")
    print(f"GATE {'OK' if ok else 'FAILED'} mode={rec['mode']} commit={commit[:7]} branch={rec['branch']} "
          f"steps_ok={sum(1 for s in rec['steps'] if s['result'] == 'ok')}/{len(steps)} "
          f"lean={rec['versions']['lean']} (fast mode: CI runs the full build)")
    return 0 if ok else 1


def verdict(rec: dict) -> str:
    """OK or FAILED, then the step that failed the gate and the advisory warnings, each by number
    and name, and why the tree is not the one the record names, if it changed."""
    name = lambda s: f"[{s['n']}] {s['name']}"
    warn = [name(s) for s in rec["steps"] if s["result"] == "WARN"]
    fail = [name(s) for s in rec["steps"] if s["result"] == "FAIL"]
    out = "OK" if rec["ok"] else "FAILED"
    if fail:
        out += f" at {fail[0]}"
    if warn:
        out += f" ({len(warn)} advisory warning{'' if len(warn) == 1 else 's'}: {', '.join(warn)})"
    if rec.get("note"):
        out += f" ({rec['note']})"
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--workflow", type=pathlib.Path)
    ap.add_argument("--root", type=pathlib.Path, default=HERE.parent)
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--from", dest="start", type=int, default=1)
    ap.add_argument("--task", help="fast mode: check one proof task, e.g. T-QU1-P5")
    ap.add_argument("--full", action="store_true",
                    help="run every Python cross-check, not only those the change since origin/main selects")
    ap.add_argument("--base", help="fast mode: the ref the pull request is based on (default origin/main)")
    a = ap.parse_args()
    root = a.root.resolve()
    wf = a.workflow or root / ".github" / "workflows" / "ci.yml"
    if a.task:
        return fast_mode(root, a.task, a.base or default_base(root))
    steps, errors = load_steps(wf)
    if a.list:
        for i, s in enumerate(steps, 1):
            print(f"{i:2d} {'CI-only' if s['ci_only'] else 'RUN    '} {s['name']}")
        for e in errors:
            print("ERROR", e)
        return 1 if errors else 0
    for e in errors:
        print("FAIL", e)
    if errors:
        return 1
    if dirty(root):
        print("FAIL the working tree is not clean; commit first (the record names the commit)")
        return 3
    commit = git(root, "rev-parse", "HEAD")
    py_base = None if a.full else git(root, "merge-base", a.base or default_base(root), "HEAD")
    rec = {"commit": commit, "branch": git(root, "rev-parse", "--abbrev-ref", "HEAD"),
           "python_checks": f"selected by the change since {py_base[:7]}" if py_base else "all",
           "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "steps": [],
           "partial": a.start > 1, "versions": versions(root)}
    ok = True
    for i, s in enumerate(steps, 1):
        if s["ci_only"]:
            rec["steps"].append({"n": i, "name": s["name"], "rc": None, "result": "ci-only"})
            continue
        if i < a.start:
            rec["steps"].append({"n": i, "name": s["name"], "rc": None, "result": "not run"})
            continue
        print(f"== [{i}/{len(steps)}] {s['name']}", flush=True)
        if "planted" in s["name"]:
            print(EXPECTED_NOTE, flush=True)
        t = time.time()
        rc = subprocess.run(["bash", "-eo", "pipefail", "-c", s["run"]], cwd=root, env=env()).returncode
        rec["steps"].append({"n": i, "name": s["name"], "rc": rc, "seconds": round(time.time() - t),
                             "result": "ok" if rc == 0 else "WARN" if s["advisory"] else "FAIL"})
        if rc != 0 and not s["advisory"]:
            ok = False
            break
    if git(root, "rev-parse", "HEAD") != commit or dirty(root, untracked=False):
        ok = False
        rec["note"] = "the tree changed while the gate ran"
    rec["ok"] = ok and not rec["partial"]
    rec["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    d = root / ".gate"
    d.mkdir(exist_ok=True)
    with open(d / "log.jsonl", "a", encoding="utf-8") as f:
        f.write(json.dumps(rec) + "\n")
    done = [s for s in rec["steps"] if s["result"] == "ok"]
    print(f"GATE {verdict(rec)} commit={commit[:7]} branch={rec['branch']} "
          f"steps_ok={len(done)}/{sum(1 for s in steps if not s['ci_only'])}"
          f"{' (partial: --from)' if rec['partial'] else ''} lean={rec['versions']['lean']}")
    return 0 if rec["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
