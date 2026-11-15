#!/usr/bin/env python3
"""Plants a bad case for each gate check and requires the check to catch it.

Run: python3 -I scripts/tooling_selftest.py     Exit 0 = every planted case was detected and
the clean control passed. Works on a temporary copy; the repository is not modified."""
import pathlib, shutil, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import ci_check  # noqa: E402

fails = []


def expect(name, cond):
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        fails.append(name)


def mini(tmp: pathlib.Path):
    q = tmp / "Lightlike"
    (q / "Tests").mkdir(parents=True, exist_ok=True)
    (tmp / "docs").mkdir(exist_ok=True)
    (tmp / "Lightlike.lean").write_text("import Lightlike.A\nimport Lightlike.Tests.T\n")
    (q / "A.lean").write_text("theorem foo : True := trivial\ntheorem bar : True := trivial\n")
    (tmp / "docs" / "results.yaml").write_text("- id: LL-0001\n  decls: [Lightlike.foo, Lightlike.bar]\n")
    (q / "Tests" / "T.lean").write_text("example := foo\n")


with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    mini(tmp)
    expect("reachability control: all modules reachable", ci_check.check_reachability(tmp) == [])
    (tmp / "Lightlike" / "Orphan.lean").write_text("theorem o : True := trivial\n")
    expect("reachability planted: orphan file is reported",
           len(ci_check.check_reachability(tmp)) == 1)
    (tmp / "Lightlike" / "Orphan.lean").unlink()
    (tmp / "Lightlike.lean").write_text("module\npublic import Lightlike.A\n"
                                             "import all Lightlike.Tests.T\n")
    expect("reachability control: `public import` and `import all` are followed",
           ci_check.check_reachability(tmp) == [])
    (tmp / "Lightlike.lean").write_text("-- import Lightlike.A\nimport Lightlike.Tests.T\n")
    expect("reachability planted: a commented-out import does not count",
           any("A.lean" in e for e in ci_check.check_reachability(tmp)))
    mini(tmp)
    w = ci_check.check_test_coverage(tmp)
    expect("untested results planted: untested declaration `bar` warned, tested `foo` not",
           len(w) == 1 and "Lightlike.bar" in w[0])
    e = tmp / "Lightlike" / "Exploratory"
    e.mkdir()
    (e / "M.lean").write_text("import Lightlike.A\ntheorem m : True := trivial\n")
    (tmp / "Lightlike" / "Exploratory.lean").write_text("import Lightlike.Exploratory.M\n")
    (tmp / "Lightlike.lean").write_text("import Lightlike.A\nimport Lightlike.Exploratory\n")
    expect("exploratory control: Exploratory/ imports core, the build roots collect it",
           ci_check.check_exploratory_imports(tmp) == [])
    (tmp / "Lightlike" / "B.lean").write_text("import Lightlike.Tests.T\n")
    (tmp / "Lightlike" / "Tests" / "T.lean").write_text("import Lightlike.Exploratory.M\n")
    expect("exploratory planted: a core module importing Exploratory/ through another module fails",
           len(ci_check.check_exploratory_imports(tmp)) == 2)

import api_map  # noqa: E402
_root = pathlib.Path(__file__).resolve().parent.parent
expect("review control: kernel-checked needs no reference; a human review with its issue URL passes",
       api_map.review_errors("x", "kernel-checked", None, _root) == []
       and api_map.review_errors("x", "human-reviewed", "https://github.com/o/r/issues/1", _root) == [])
expect("review planted: a human review without an issue URL, an unknown or retired level, a stray reference",
       all(api_map.review_errors("x", r, ref, _root) for r, ref in
           [("human-reviewed", None), ("human-reviewed", "docs/x.md"), ("peer-reviewed", "y"),
            ("agent-reviewed", "docs/x.md"), ("kernel-checked", "docs/x.md")]))

log = "warning: Lightlike/Lorentz/Density.lean:5:2: `x` has been deprecated, use `y` instead\n"
expect("deprecations control: warning within baseline passes",
       ci_check.check_deprecations(log, {"Lightlike/Lorentz/Density.lean": 1}) == [])
expect("deprecations planted: warning beyond baseline is reported",
       len(ci_check.check_deprecations(log * 2, {"Lightlike/Lorentz/Density.lean": 1})) == 1)
expect("deprecations planted: warning in a file without baseline is reported",
       len(ci_check.check_deprecations(log, {})) == 1)
expect("deprecations control: ordinary linter warning ignored",
       ci_check.check_deprecations("warning: A.lean:1:1: unused variable `x`\n", {}) == [])

import run_python_checks as rp  # noqa: E402
expect("python checks control: every script in scripts/ is listed", rp.unlisted() == [])
expect("python checks control: every listed script outside NO_EXIT_BASELINE has an exit path",
       rp.exit_path_problems()[0] == [])
with tempfile.TemporaryDirectory() as d:
    (pathlib.Path(d) / "scripts").mkdir()
    (pathlib.Path(d) / "scripts" / "new_check.py").write_text("print('x')\n")
    old, base = rp.ROOT, set(rp.NO_EXIT_BASELINE)
    rp.ROOT = pathlib.Path(d)
    rp.NO_EXIT_BASELINE.clear()  # the real entries do not exist here
    expect("python checks planted: an unlisted new script is reported",
           rp.unlisted() == ["scripts/new_check.py"])
    (pathlib.Path(d) / "scripts" / "new_check.py").write_text("import sys; sys.exit(1)\n")
    rp.CHECKS[:] = [("scripts/new_check.py", False)]
    rp.REQUIRED[:] = []
    sys.argv = ["x"]
    expect("python checks planted: a failing script makes the runner exit 1", rp.main() == 1)
    s = pathlib.Path(d) / "scripts" / "new_check.py"
    s.write_text("import sys\nprint('1 case: 0 mismatches')\nprint('OK')\nsys.exit(0)\n")
    expect("python checks control: a passing script with an exit path passes", rp.main() == 0)
    s.write_text("import sys\nprint('1 case: 1 mismatch')\nprint('CHECK FAILED')\nsys.exit(0)\n")
    expect("python checks planted: exit 0 with a last line saying FAILED makes the runner exit 1",
           rp.main() == 1)
    s.write_text("print('FAIL (control, expected)')\nprint('OK')\nraise SystemExit(0)\n")
    expect("python checks control: FAIL on an earlier line (a control) does not fail the script",
           rp.main() == 0)
    s.write_text("print('OK')\n")
    expect("python checks planted: a listed script with no exit path is an error",
           rp.exit_path_problems()[0] != [] and rp.main() == 1)
    rp.NO_EXIT_BASELINE.add("scripts/new_check.py")
    expect("python checks control: a script in NO_EXIT_BASELINE is not an error",
           rp.exit_path_problems() == ([], []) and rp.main() == 0)
    s.write_text("import sys\nprint('OK')\nsys.exit(0)\n")
    expect("python checks planted: a baseline script that gained an exit path is a warning only",
           rp.exit_path_problems()[0] == [] and len(rp.exit_path_problems()[1]) == 1
           and rp.main() == 0)
    rp.NO_EXIT_BASELINE.clear()
    rp.NO_EXIT_BASELINE.update(base)
    rp.ROOT = old

expect("python checks control: installed packages are found", rp.missing_packages(["sys", "json"]) == [])
expect("python checks planted: a missing package is reported once, not per script",
       rp.missing_packages(["no_such_pkg_xyz"]) == ["no_such_pkg_xyz"])
rp.REQUIRED[:] = ["no_such_pkg_xyz"]
sys.argv = ["x"]
expect("python checks planted: runner exits 2 with one message when packages are missing", rp.main() == 2)

# The gate runs the steps of ci.yml, records the commit, and cannot skip a step silently
def toy(steps: str):
    d = tempfile.mkdtemp()
    r = pathlib.Path(d)
    (r / ".github" / "workflows").mkdir(parents=True)
    (r / ".github" / "workflows" / "ci.yml").write_text(
        "name: T\non:\n  workflow_dispatch:\njobs:\n  b:\n    runs-on: x\n    steps:\n" + steps)
    g = lambda *a: subprocess.run(["git", "-C", d, *a], check=True, capture_output=True)
    g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
    g("add", "-A"); g("commit", "-qm", "c")
    return r, g


def gate(r):
    return subprocess.run([sys.executable, "-I", str(HERE / "gate.py"), "--root", str(r)],
                          capture_output=True, text=True)


import json  # noqa: E402
r, g = toy("      - uses: actions/checkout@v7\n      - name: one\n        run: echo one > one.txt\n"
           "      - name: skipme [ci-only]\n        run: echo x > skipped.txt\n"
           "      - name: two\n        run: test -f one.txt\n")
res = gate(r)
rec = json.loads((r / ".gate" / "log.jsonl").read_text().splitlines()[-1]) if (r / ".gate").exists() else {}
head = subprocess.run(["git", "-C", str(r), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
expect("gate control: gate passes, runs steps in order, records the commit",
       res.returncode == 0 and rec.get("commit") == head and rec.get("ok") is True
       and [x["result"] for x in rec["steps"]] == ["ci-only", "ok", "ci-only", "ok"])
expect("gate control: a [ci-only] step is not executed", not (r / "skipped.txt").exists())
r, g = toy("      - name: good\n        run: echo a\n      - name: bad\n        run: exit 3\n"
           "      - name: after\n        run: echo b > after.txt\n")
res = gate(r)
out = res.stdout + res.stderr
expect("gate planted: a failing step fails the gate, is named, and stops it",
       res.returncode == 1 and not (r / "after.txt").exists() and "PyYAML" not in out
       and "bad" in out and "FAILED" in out
       and [x["result"] for x in json.loads((r / ".gate" / "log.jsonl").read_text().splitlines()[-1])["steps"]][:1] == ["ok"])
r, g = toy("      - name: cond\n        if: github.ref == 'x'\n        run: echo a\n")
res = gate(r)
expect("gate planted: a step with a key the gate does not implement is an error",
       res.returncode == 1 and "unsupported" in res.stdout and "PyYAML" not in res.stdout + res.stderr)
r, g = toy("      - name: env [ci-only]\n        if: github.ref == 'x'\n        env:\n          A: b\n"
           "        run: echo a > ci.txt\n      - name: one\n        id: s\n        run: echo b > one.txt\n"
           "  c:\n    needs: b\n    if: github.ref == 'x'\n    outputs:\n      o: x\n"
           "    permissions:\n      actions: write\n    runs-on: x\n    steps:\n"
           "      - name: two\n        run: test -f one.txt\n")
res = gate(r)
expect("gate control: `if`/`env` on a CI-only step, `id`, and the job keys that steer CI are "
       "accepted; every job runs, in order",
       res.returncode == 0 and not (r / "ci.txt").exists() and (r / "one.txt").exists())
r, g = toy("      - name: ok\n        run: echo a\n")
(r / "dirty.txt").write_text("x")
res = gate(r)
expect("gate planted: an unclean tree is refused with its message",
       res.returncode == 3 and "clean" in res.stdout + res.stderr)
res = subprocess.run([sys.executable, "-I", "-S", str(HERE / "gate.py"), "--root", str(r)],
                     capture_output=True, text=True)  # -S: no site-packages, so no PyYAML
expect("gate planted: without PyYAML the gate says so and exits",
       res.returncode != 0 and "PyYAML is missing" in res.stdout + res.stderr)

# Context packs: the size limit holds and whatever is dropped is named
import importlib.machinery, importlib.util  # noqa: E402
_ld = importlib.machinery.SourceFileLoader("context_pack", str(HERE / "context-pack"))
cp = importlib.util.module_from_spec(importlib.util.spec_from_loader("context_pack", _ld))
_ld.exec_module(cp)
_dep = lambda i: {"name": f"Lightlike.d{i}", "kind": "definition", "file": "Lightlike/A.lean",
                  "line": 10 * i + 1, "source": f"def d{i} : Nat :=\n  " + "1 + " * 200 + "1"}
_pack = {"decl": "Lightlike.t", "file": "Lightlike/A.lean", "line": 1, "use": [],
         "source": "theorem t : d0 = d0 := by\n  sorry",
         "deps": [_dep(i) for i in range(40)] + [dict(_dep(0), name="Lightlike.d0.mk")],
         "lemmas": [{"name": "Lightlike.l", "signature": "Lightlike.l : d0 = d0", "file": "Lightlike/A.lean",
                     "line": 900}]}
_full = cp.render(_pack, 10 ** 6)
expect("context-pack control: an unlimited pack has every entry and no truncation note",
       all(f"Lightlike.d{i} " in _full for i in range(40)) and "Lightlike.l" in _full and "Truncated" not in _full)
expect("context-pack control: an entry inside an earlier one (a constructor) is listed once",
       "Lightlike.d0.mk" not in _full)
_small = cp.render(_pack, 6000)
expect("context-pack planted: an oversized pack stays under the limit, keeps the nearest entries "
       "and names what it dropped",
       len(_small) <= 6000 and "Lightlike.d0 " in _small and "Truncated" in _small and "Lightlike.d39 (" in _small
       and _small.count("```") % 2 == 0)
expect("context-pack control: a proof in a dependency is replaced by sorry",
       "sorry -- proof omitted" in cp.entry({"name": "Lightlike.x", "kind": "theorem", "file": "f", "line": 1,
                                              "source": "theorem x : True := by\n  trivial"}))

# Proof tasks: only the proof body of the task's declaration may change
import proof_task_check as ptc  # noqa: E402
_task = ("import Lightlike\n\n/-!\nStructural: a fixture for the task checks.\n-/\n\nnamespace Lightlike.Tasks\n\n"
         "/-- Two plus two. -/\n"
         "theorem four : 2 + 2 = 4 := by\n  sorry\n\nend Lightlike.Tasks\n")


def _ptc(new_text, other=None, lock=None):
    d = pathlib.Path(tempfile.mkdtemp())
    g = lambda *a: subprocess.run(["git", "-C", str(d), *a], check=True, capture_output=True)
    g("init", "-q"); g("config", "user.email", "t@t"); g("config", "user.name", "t")
    (d / "Tasks").mkdir()
    (d / "Tasks" / "Four.lean").write_text(_task)
    g("add", "-A"); g("commit", "-qm", "base"); g("tag", "base")
    (d / "Tasks" / "Four.lean").write_text(new_text)
    if other:
        (d / other).write_text("x\n")
    g("add", "-A"); g("commit", "-qm", "head")
    return ptc.check("base", "HEAD", "Tasks/Four.lean", "Lightlike.Tasks.four", lock, root=d)


_hdr = "/-- Two plus two. -/\ntheorem four : 2 + 2 = 4 :="
expect("proof-task control: a proof that replaces sorry passes",
       _ptc(_task.replace("  sorry", "  norm_num")) == [])
expect("proof-task control: a matching statement lock passes",
       _ptc(_task.replace("  sorry", "  rfl"), lock=ptc.statement_hash(_hdr)) == [])
expect("proof-task planted: a changed statement fails",
       any("statement changed" in p for p in _ptc(_task.replace("2 + 2 = 4 := by\n  sorry",
                                                                "2 + 2 = 4 ∨ True := by\n  simp"))))
expect("proof-task planted: a changed docstring fails",
       any("statement changed" in p for p in _ptc(_task.replace("Two plus two", "Four").replace("  sorry", "  rfl"))))
expect("proof-task planted: a second changed file fails",
       any("other than" in p for p in _ptc(_task.replace("  sorry", "  rfl"), other="Other.lean")))
expect("proof-task planted: a new top-level lemma after the proof fails",
       any("after the proof" in p for p in _ptc(_task.replace("  sorry\n", "  rfl\n\ntheorem extra : True := trivial\n"))))
expect("proof-task planted: a new lemma before the declaration fails",
       any("before the declaration" in p for p in _ptc(_task.replace("/-- Two", "theorem extra : True := trivial\n\n/-- Two").replace("  sorry", "  rfl"))))
expect("proof-task planted: an indented new declaration after the proof fails",
       any("new declaration" in p for p in _ptc(_task.replace("  sorry\n", "  rfl\n  theorem extra : True := trivial\n"))))
expect("proof-task control: `open ... in` and `set_option ... in` inside a tactic proof are not flagged",
       _ptc(_task.replace("  sorry", "  open Nat in\n  set_option maxHeartbeats 400000 in\n  rfl")) == [])
expect("proof-task planted: a proof that still has sorry fails",
       any("sorry" in p for p in _ptc(_task.replace("  sorry", "  first | rfl | sorry"))))
expect("proof-task control: sorry inside a comment of the proof is allowed",
       _ptc(_task.replace("  sorry", "  rfl -- was sorry")) == [])
expect("proof-task planted: a statement that does not match its lock fails",
       any("locked hash" in p for p in _ptc(_task.replace("  sorry", "  rfl"), lock="0" * 16)))
expect("proof-task control: the task ID is read from the body, not from template comments",
       ptc.task_from_body("<!-- for example Task: T-QU1-P6 -->\nAI assistance (optional): none\nTask: T-QU1-P5\n") == "T-QU1-P5")
expect("proof-task planted: two different task IDs in one body are refused",
       ptc.task_from_body("Task: T-QU1-P5\nTask: T-QU1-P6\n") is None)


def _ptc_main(body, *flags):
    import contextlib, io
    f = pathlib.Path(tempfile.mkdtemp()) / "body.txt"
    f.write_text(body)
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = ptc.main(["--base", "base", "--head", "HEAD", "--body-file", str(f), *flags])
    return rc, out.getvalue()


# which pull requests are proof tasks: the label, or a Task line with a -P<n> ID (only these are checked)
for _tid in ("T-RC6", "T-UP-1", "T-PL5", "T-SF4b"):
    _r = _ptc_main(f"## Task\n\nTask: {_tid}\n")
    expect(f"proof-task control: a milestone or upstream Task line {_tid} without the label passes, nothing to check",
           _r == (0, f"not a proof task: {_tid}, nothing to check\n"))
for _b in ("Task: T-RC6\n", "Task: none\n", "<!-- Task: T-QU1-P5 -->\nTask: T-RC6\n"):
    expect(f"proof-task planted: the proof-task label without a proof-task ID fails ({_b.strip()!r})",
           _ptc_main(_b, "--proof-label")[0] == 2)
for _tid in ("T-DT4-P", "T-DT4-Px", "T-QU1-P5-b", "T-DT4-p1"):
    expect(f"proof-task planted: a malformed proof-task ID {_tid} fails, with or without the label",
           _ptc_main(f"Task: {_tid}\n")[0] == 2 and _ptc_main(f"Task: {_tid}\n", "--proof-label")[0] == 2)
expect("proof-task planted: two different proof-task IDs without the label fail",
       _ptc_main("Task: T-QU1-P5\nTask: T-QU1-P6\n")[0] == 2)
_check, ptc.check = ptc.check, lambda *a, **k: []
try:
    expect("proof-task control: a proof-task ID without the label is checked",
           _ptc_main("Task: T-QU1-P5\n")[1].startswith("proof-task check OK for T-QU1-P5"))
    expect("proof-task control: the label with a proof-task ID is checked",
           _ptc_main("Task: T-QU1-P5\n", "--proof-label")[1].startswith("proof-task check OK for T-QU1-P5"))
finally:
    ptc.check = _check

# --- scripts/tasks.py: milestone parsing, the generic split, readiness, sync and the file check.
import tasks as tk  # noqa: E402

_road = """## Mathematical and QFT foundations

### Alpha

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| X1 | First \\| thing | it holds | value 1; value 2 | S | - |
| X2 | Second | below | below | L (dim 2), R (all) | X1, Mathlib or core |
| X3 | Third | x | y | M | X1–2 |
| X4 | Fourth | x | y | M | X3, B1 or B2 |

- **X2, done when**: it is proved. Trust checks: the sphere, the torus, and a
  wrong model. More text.

## Approaches to quantum gravity

### Beta

| ID | Milestone | Size | Needs |
|---|---|---|---|
| B1 | Only one | S | - |
| B2 | Two | S | B1 |
"""
_cfg = {"areas": {"Alpha": "alpha", "Beta": "beta"},
        "tasks": [{"id": "T-X1-P1", "milestone": "X1", "kind": "proof", "title": "t", "size": "XS",
                   "file": "Tasks/A.lean", "decl": "Lightlike.Tasks.four"},
                  {"id": "T-X1-P2", "milestone": "X1", "kind": "proof", "title": "u", "size": "S",
                   "deps": ["T-X1-P1"]}]}
_ms = tk.parse_roadmap(_road, _cfg)
expect("tasks: milestone rows, escaped pipes and sizes parse; the tables carry no status",
       list(_ms) == ["X1", "X2", "X3", "X4", "B1", "B2"] and _ms["X1"]["title"] == "First | thing"
       and _ms["X2"]["size"] == "R" and "status" not in _ms["X3"])
expect("tasks: trust checks split from the cell and from a done-when bullet",
       _ms["X1"]["trust"] == ["value 1", "value 2"]
       and _ms["X2"]["trust"] == ["the sphere", "the torus", "a wrong model"])
expect("tasks: needs ranges expand; external alternatives are not dependencies",
       _ms["X3"]["needs"] == ["X1", "X2"] and _ms["X2"]["needs"] == ["X1"] and _ms["X4"]["needs"] == ["X3", "B1"])
_ts = tk.decompose(_ms, _cfg)
_by = {t["id"]: t for t in _ts}
expect("tasks: one task per milestone, with its trust checks, then its proof tasks",
       [t["id"] for t in _ts if t["milestone"] == "X1"] == ["T-X1", "T-X1-P1", "T-X1-P2"]
       and _by["T-X1"]["checks"] == ["value 1", "value 2"] and "T-B2" in _by and "status" not in _by["T-X1"])
expect("tasks: dependencies follow the milestone graph",
       _by["T-X4"]["deps"] == ["T-X3", "T-B1"] and _by["T-X3"]["deps"] == ["T-X1", "T-X2"]
       and _by["T-X2"]["size"] == "R" and _by["T-X2"]["difficulty"] == "research-level")
_read = lambda p: _task  # noqa: E731
tk.compute(_ts, _ms, dict(_cfg), _read)
_p = tk.progress(_ts, _cfg)
expect("tasks: an unlocked drafted statement blocks its proof task and its dependants",
       _p["T-X1-P1"] == ("blocked", [tk.UNLOCKED]) and _p["T-X1-P2"] == ("blocked", ["needs T-X1-P1"])
       and _p["T-X1"] == ("ready", []))
expect("tasks: a milestone whose issue is closed is done, and the milestones that need it become ready",
       _p["T-X2"] == ("blocked", ["needs T-X1"])
       and tk.progress(_ts, _cfg, {"T-X1"})["T-X2"] == ("ready", [])
       and tk.progress(_ts, _cfg, {"T-X1"})["T-X1"][0] == "done")
_c1, _c1b = tk.generic_card(_by["T-X1"], _ms)
expect("tasks: a milestone card links background and conventions, lists its trust checks and says how to claim it",
       "docs/tasks/milestones.md#alpha" in _c1b and tk.CONVENTIONS in _c1b and "It must satisfy" in _c1b
       and "hard rules" in _c1b and "- value 2" in _c1b and "non-vacuity" in _c1b
       and "`claiming`" in _c1b and "Task: T-X1" in _c1b and "Status" not in _c1b)
expect("tasks: the board lists proof tasks first, then milestones by area, and links the live issue searches",
       (lambda b: b.index("## Proof tasks") < b.index("## Milestones by area") and "label%3Aready" in b
        and "Status" not in b and "Generated by" not in b.split("-->", 1)[1])(tk.readme(_ts, _ms, "o/r")))
_rk = tk.readme_kinds("# T\n\nThe plan has 0 tasks,\nold line.\n\n## Next\n", _ts)
expect("tasks: generate rewrites the README paragraph of task counts, and only it",
       _rk.startswith("# T\n\nThe plan has ") and _rk.endswith("\n\n## Next\n") and "old line" not in _rk
       and f"{sum(t['kind'] == 'proof' for t in _ts)} **proof tasks**" in _rk
       and tk.readme_kinds("# T\n\nNo counts.\n", _ts) == "# T\n\nNo counts.\n")
_cl = tk.changelog_counts("# C\n\n## [0.2.0]\n\n- 0 areas in [ROADMAP](R)\n- 0 tasks on the [task board](B)\n\n"
                          "## [0.1.0]\n\n- 9 tasks on the [task board](B)\n", _ts, _ms)
expect("tasks: generate brings the CHANGELOG counts of the newest version up to date, not older ones",
       f"- {len(_ts)} tasks on the [task board](B)\n\n## [0.1.0]" in _cl
       and f"- {len({m['area'] for m in _ms.values()})} areas in [ROADMAP]" in _cl
       and _cl.endswith("- 9 tasks on the [task board](B)\n") and len(_ts) != 9)
with tempfile.TemporaryDirectory() as d:
    (pathlib.Path(d) / "docs/tasks").mkdir(parents=True)
    (pathlib.Path(d) / tk.SOURCES).write_text(
        "references:\n  a-2000:\n    cite: \"A. Author, A paper (2000)\"\n"
        "  b-2001:\n    cite: \"B. Author, A book (2001)\"\n")
    _hm = {"X9": dict(id="X9", title="A milestone: details", section="Sec",
                      src=dict(cls="sourced", refs=[dict(ref="a-2000", location="Abstract"),
                                                    dict(ref="b-2001", location="Chapter: Chapter 2|doi")]))}
    _ht = dict(id="T-X9-P2", title="Two is two", decl="Lightlike.two", deps=["T-X9-P1"],
               routes=["Use `one`."], difficulty="good first issue", milestone="X9")
    _hp = {"deps": [dict(name="Lightlike.One", kind="def", file="Lightlike/A.lean", statement=True),
                    dict(name="Lightlike.Far", kind="def", file="Lightlike/B.lean", statement=False)],
           "lemmas": [dict(name="Lightlike.one", file="Lightlike/A.lean")]}
    _h = tk.task_header(_ht, {"T-X9-P1": dict(decl="Lightlike.one")}, _hm, _hp, pathlib.Path(d))
    _order = [_h.find(x) for x in ("Two is two.", "The statement is `Lightlike.two`", "Hint. Use",
                                   tk.DEPS_HEAD, "## References", "Source: ")]
    expect("tasks: a task header puts the statement first, then the hint, what the statement uses, "
           "and the references",
           -1 not in _order and _order == sorted(_order) and "T-X9-P1 (`one`)" in _h)
    expect("tasks: the header lists only the definitions the statement names, and cites no abstract",
           "`One`" in _h and "`Far`" not in _h and "Abstract" not in _h
           and "A. Author, A paper (2000); B. Author, A book (2001), Chapter 2 (" in _h)
_ts2 = tk.decompose(_ms, _cfg)
_cfg2 = dict(_cfg, locked={"T-X1-P1": "0" * 16})
tk.compute(_ts2, _ms, _cfg2, _read)
_p2 = tk.progress(_ts2, _cfg2)
expect("tasks: a locked statement makes its proof task ready, and dependants need only the lock",
       _p2["T-X1-P1"][0] == "ready" and _p2["T-X1-P2"][0] == "ready" and "needs T-X1" in _p2["T-X2"][1])
_ts4 = tk.decompose(_ms, _cfg)
_lk = {"T-X1-P1": "0" * 16, "T-X1-P2": "1" * 16}
_cfg4 = dict(_cfg, locked=_lk, stated=["X1"])
tk.compute(_ts4, _ms, _cfg4, _read)
_ts5 = tk.decompose(_ms, _cfg)
tk.compute(_ts5, _ms, dict(_cfg, locked=_lk), _read)
expect("tasks: a stated milestone with every proof task locked counts as met; an unstated one does not",
       tk.progress(_ts4, _cfg4)["T-X2"] == ("ready", [])
       and "needs T-X1" in tk.progress(_ts5, dict(_cfg, locked=_lk))["T-X2"][1])
expect("tasks: a proof without sorry counts as done",
       tk.proven(_task.replace("  sorry", "  norm_num"), "Lightlike.Tasks.four")
       and not tk.proven(_task, "Lightlike.Tasks.four"))
_ts6 = tk.decompose(_ms, _cfg)
tk.compute(_ts6, _ms, _cfg2, lambda p: _task.replace("  sorry", "  norm_num"))
expect("tasks: a proven proof task is done without any record in the repository",
       tk.progress(_ts6, _cfg2)["T-X1-P1"] == ("done", []))
_files = {"Tasks/A.lean": _task.replace("theorem four", "theorem bad : True := sorry\n\ntheorem four")}
expect("tasks check planted: a sorry outside the task's proof fails",
       any("outside the proof" in p for p in tk.check_task_files(_files, _ts2)))
expect("tasks check planted: a lock that does not match fails; an unregistered file fails",
       any("does not match its lock" in p for p in tk.check_task_files({"Tasks/A.lean": _task}, _ts2))
       and any("not registered" in p for p in tk.check_task_files({"Tasks/A.lean": _task, "Tasks/B.lean": _task}, _ts2)))
expect("tasks check control: a clean task file passes (no lock)",
       tk.check_task_files({"Tasks/A.lean": _task}, _ts) == [])
expect("tasks check planted: a task file without a Source, Structural or Exploratory line fails",
       any("needs a `Source:` line" in p for p in tk.check_task_files(
           {"Tasks/A.lean": _task.replace("Structural:", "Note:")}, _ts)))
_up = dict(_cfg, upstream=[
    {"id": "T-UP-1", "target": "Mathlib", "area": "alpha", "size": "S", "results": ["LL-0001"],
     "title": "u", "rework": "r"},
    {"id": "T-UP-2", "target": "Physlib", "area": "beta", "size": "M", "results": ["LL-0002"],
     "deps": ["T-UP-1"], "title": "v", "rework": "r"}])
_ts3 = tk.decompose(_ms, _up)
tk.compute(_ts3, _ms, _up, _read)
_by3 = {t["id"]: t for t in _ts3}
_p3 = tk.progress(_ts3, _up)
expect("tasks: upstream tasks need no milestone, are exclusive, and carry the target label",
       _p3["T-UP-1"][0] == "ready" and _p3["T-UP-2"][1] == ["needs T-UP-1"]
       and _by3["T-UP-1"]["mode"] == "exclusive"
       and "upstream: Mathlib" in tk.labels_for(_by3["T-UP-1"])
       and "Rework needed: r" in tk.generic_card(_by3["T-UP-1"], _ms)[1])
_bad = []
for _u in ({"target": "Coq"}, {"area": "nowhere"}, {"rework": ""}):
    try:
        tk.decompose(_ms, dict(_cfg, upstream=[dict(_up["upstream"][0], **_u)]))
    except ValueError:
        _bad.append(True)
expect("tasks planted: an upstream task with an unknown target or area, or no rework, is refused",
       len(_bad) == 3)
expect("tasks sync: a pull request's `Task:` line is read whole (T-UP-1, T-QU1-P5, T-SF5a)",
       tk.TASK_LINE_ANY.findall("Task: T-UP-1\nTask: T-QU1-P5\n Task: T-SF5a\n") == ["T-UP-1", "T-QU1-P5", "T-SF5a"])

# The sync: issues, comments and pull requests in, label, assignment and comment changes out.
for _t in _ts2 + _ts6:
    _t["labels"] = tk.labels_for(_t)
_c = lambda a, body, when: {"author": a, "body": body, "createdAt": when}  # noqa: E731
_iss = lambda n, title, labels, comments, state="open", reason="", assignees=(): dict(  # noqa: E731
    number=n, title=title, state=state, reason=reason, labels=list(labels), assignees=list(assignees),
    comments=comments)
_card = lambda tid: (f"{tid}: title", "body")  # noqa: E731
_lapse = tk.MARK.format("lapse old 2026-10-01T00:00:00Z")
_data = {"now": "2026-11-07T00:00:00Z", "labels": tk.LIVE + sorted({x for t in _ts2 for x in t["labels"]}), "issues": [
    _iss(1, "[proof task] T-X1-P1: t", ["proof-task", "ready"], [
        _c("ann", "attempting via route 1", "2026-11-01T00:00:00Z"),
        _c("bob", "Attempting too", "2026-11-02T00:00:00Z"),
        _c("bob", "stopping, no time", "2026-11-03T00:00:00Z"),
        _c("cy", "attempting", "2026-09-01T00:00:00Z"),
        _c("ann", "a second note", "2026-11-04T00:00:00Z")]),
    _iss(2, "T-X1: x", ["milestone", "ready"], [_c("dee", "claiming", "2026-11-05T00:00:00Z")]),
    _iss(3, "T-B1: b", ["ready"], [_c("old", "claiming", "2026-10-01T00:00:00Z")], assignees=["old", "maint"]),
    _iss(4, "T-X2: s", ["blocked"], [], state="closed", reason="completed"),
    _iss(5, "T-B2: dup", [], [], state="closed", reason="not_planned"),
    _iss(9, "T-X1: a later duplicate", [], [])],
    "pulls": [{"number": 7, "body": "<!--\nTask: T-X1\n-->\nTask: T-B1\n", "author": "eve", "state": "open",
               "updatedAt": "2026-11-05T00:00:00Z"}]}
_st, _acts = tk.sync_plan(_ts2, _cfg2, _data, _card)
_on = lambda acts, tid, op: [a for a in acts if a.get("task") == tid and a["op"] == op]  # noqa: E731
_e = lambda acts, tid: (_on(acts, tid, "edit") or [{}])[0]  # noqa: E731
expect("tasks sync: attempts are live comments `attempting` (released and lapsed ones drop out)",
       _e(_acts, "T-X1-P1").get("add") == ["attempting"] and not _e(_acts, "T-X1-P1").get("remove"))
expect("tasks sync: a claim assigns the claimant and replaces `ready` by `claimed`",
       _e(_acts, "T-X1") == dict(op="edit", task="T-X1", issue=2, add=["claimed"], remove=["ready"],
                                 assign=["dee"], unassign=[]))
expect("tasks sync: a lapsed claim unassigns the claimant only and is announced; an open PR sets `in review`",
       _e(_acts, "T-B1").get("unassign") == ["old"] and _e(_acts, "T-B1").get("add") == ["in review"]
       and _e(_acts, "T-B1").get("remove") == ["ready"] and len(_on(_acts, "T-B1", "comment")) == 1
       and _lapse in _on(_acts, "T-B1", "comment")[0]["body"])
_data3 = json.loads(json.dumps(_data))
_data3["issues"][2]["comments"].append(_c("github-actions[bot]", "lapsed\n" + _lapse, "2026-11-06T00:00:00Z"))
_data3["issues"][2]["assignees"] = ["maint"]
_data3["issues"][2]["labels"] = ["in review"]
expect("tasks sync: the lapse notice is posted once and ends the claim",
       not [a for a in tk.sync_plan(_ts2, _cfg2, _data3, _card)[1] if a.get("task") == "T-B1"])
expect("tasks sync: a closed issue loses its live labels and makes its task done; a duplicate is ignored",
       _e(_acts, "T-X2").get("remove") == ["blocked"] and _st["T-X2"][0] == "done"
       and not _on(_acts, "T-B2", "create") and not [a for a in _acts if a.get("issue") == 9])
expect("tasks sync: a task that becomes ready gets an issue; a blocked one does not; a commented-out Task line is ignored",
       [a["labels"] for a in _on(_acts, "T-X1-P2", "create")] == [["proof-task", "area: alpha", "size: S",
                                                                   "intermediate", "ready"]]
       and not _on(_acts, "T-X4", "create") and not _on(_acts, "T-X3", "create"))
expect("tasks sync control: labels that exist are not created again",
       not [a for a in _acts if a["op"] == "label"])
_seed = {"closed": {"X4": "done (older work)"}, "notes": {"X3": "in progress"}}
_s1 = tk.sync_plan(_ts2, _cfg2, _data, _card, _seed)[1]
expect("tasks sync: the seed opens and closes the issue of earlier done work, and posts earlier notes",
       [a["op"] for a in _s1 if a.get("task") == "T-X4"] == ["create", "close"]
       and "(older work)." in _on(_s1, "T-X4", "close")[0]["body"]
       and [a["op"] for a in _s1 if a.get("task") == "T-X3"] == ["create", "comment"])
_data2 = json.loads(json.dumps(_data))
_data2["issues"] += [_iss(10, "T-X4: f", [], [_c("bot", tk.MARK.format("seed"), "2026-11-06T00:00:00Z")],
                          state="closed", reason="completed"),
                     _iss(11, "T-X3: t", ["milestone", "blocked"],
                          [_c("bot", tk.MARK.format("seed"), "2026-11-06T00:00:00Z")])]
expect("tasks sync: a second seed run changes nothing more",
       not [a for a in tk.sync_plan(_ts2, _cfg2, _data2, _card, _seed)[1] if a.get("task") in ("T-X3", "T-X4")])
_bad = []
try:
    tk.sync_plan(_ts2, _cfg2, _data, _card, {"closed": {"ZZ9": "done"}})
except ValueError:
    _bad.append(True)
expect("tasks sync planted: a seed entry that is not a task is refused", _bad == [True])
_s6 = tk.sync_plan(_ts6, _cfg2, _data, _card)[1]
_data6 = json.loads(json.dumps(_data))
_data6["issues"][0]["comments"].append(_c("bot", tk.MARK.format("proven"), "2026-11-06T00:00:00Z"))
expect("tasks sync: a proof task proven on main has its issue closed, once",
       len(_on(_s6, "T-X1-P1", "close")) == 1 and "has no `sorry`" in _on(_s6, "T-X1-P1", "close")[0]["body"]
       and not _on(tk.sync_plan(_ts6, _cfg2, _data6, _card)[1], "T-X1-P1", "close"))

import doc_refs_check as drc  # noqa: E402
with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    (tmp / "Lightlike" / "B").mkdir(parents=True)
    (tmp / "docs").mkdir()
    (tmp / "docs" / "results.yaml").write_text("- id: LL-0001\n  decls: [Lightlike.foo]\n  status: proven\n")
    (tmp / "Lightlike" / "A.lean").write_text(
        "/-! See `Lightlike/B/C.lean` and `C.lean`. -/\ntheorem foo : True := trivial\n")
    (tmp / "Lightlike" / "B" / "C.lean").write_text("/-! `foo` is proven in `Lightlike/A.lean`. -/\n")
    subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
    subprocess.run(["git", "add", "-A"], cwd=tmp, check=True)
    _f = drc.tracked(tmp)
    expect("doc refs control: existing paths, a unique bare name and a true claim pass",
           drc.check_paths(tmp, _f) == [] and drc.check_claims(tmp, _f) == [])
    (tmp / "Lightlike" / "A.lean").write_text(
        "/-! See `Lightlike/B/Gone.lean`; `B/C.lean` too. -/\ntheorem foo : True := trivial\n")
    expect("doc refs planted: a missing path and a path not from the root are reported",
           len(drc.check_paths(tmp, _f)) == 2)
    (tmp / "Lightlike" / "B" / "C.lean").write_text("/-! `foo` is not proven yet. -/\n")
    expect("doc refs planted: a claim that the proven theorem `foo` is not proven is reported",
           len(drc.check_claims(tmp, _f)) == 1)

# Leak check: local paths, other e-mail addresses, token-like strings and secrets files fail;
# noreply and project addresses, version pins and the dev container's user pass. The planted
# strings are built at run time, so this file itself stays clean.
import leak_check as lk  # noqa: E402

_ok = [("a.md", "Co-Authored-By: x <noreply@github.com>, 1+x@users.noreply.github.com"),
       ("b.json", '"remoteEnv": "/home/vscode/.elan/bin", "pkg@1.2.3"')]
expect("leak check control: noreply addresses, a version pin and the container user pass",
       lk.check(_ok) == [])
_bad = [("a.md", "see " + "/Us" + "ers/alice/notes"), ("b.md", "mail " + "bob" + "@corp.io"),
        ("c.py", "t = '" + "gh" + "p_" + "a" * 36 + "'"), ("d.txt", "~" + "/Desktop/x"),
        ("config/id_rsa", None)]
expect("leak check planted: a local path, an e-mail, a token, ~/Desktop and a key file fail",
       len(lk.check(_bad)) == 5)

print("selftest:", "OK" if not fails else f"FAILED ({len(fails)})")
sys.exit(1 if fails else 0)
