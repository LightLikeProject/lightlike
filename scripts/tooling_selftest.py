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
    (tmp / "Lightlike" / "Tests" / "T.lean").write_text("example := foo\nexample := Lightlike.bar\n")
    expect("untested results control: a use qualified by the namespace, `Lightlike.bar`, counts",
           ci_check.check_test_coverage(tmp) == [])
    (tmp / "docs" / "results.d").mkdir()
    (tmp / "docs" / "results.d" / "new.yaml").write_text("- id: LL-XXXX\n  decls: [Lightlike.baz]\n")
    w = ci_check.check_test_coverage(tmp)
    expect("untested results planted: a new entry in docs/results.d is covered too",
           len(w) == 1 and "Lightlike.baz" in w[0])
    (tmp / "docs" / "results.d" / "new.yaml").unlink()
    (tmp / "Lightlike" / "Tests" / "T.lean").write_text("example := foo\nexample := h.bar\n")
    expect("untested results planted: dot notation `h.bar` is not counted as a use of `bar`",
           len(ci_check.check_test_coverage(tmp)) == 1)
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

with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    mini(tmp)
    bl = tmp / "base.txt"
    expect("constructs control (flag off): a clean tree passes", ci_check.scan_constructs(tmp, bl) == [])
    kinds = ["elab x : term => pure x", "macro_rules | `(a) => `(b)", "syntax \"a\" : term",
             "initialize r : IO.Ref Nat <- IO.mkRef 0", "run_cmd pure ()", "unsafe def u := 0",
             "opaque o : Nat"]
    for k in kinds:
        (tmp / "Lightlike" / "A.lean").write_text("theorem foo : True := trivial\n" + k + "\n")
        expect("constructs planted (flag on): `" + k.split()[0] + "` is reported",
               len(ci_check.scan_constructs(tmp, bl)) == 1)
    (tmp / "Lightlike" / "A.lean").write_text("-- unsafe opaque x\n/- syntax a -/\ntheorem foo : \"unsafe\" = \"unsafe\" := rfl\n")
    expect("constructs control: comments and strings are ignored", ci_check.scan_constructs(tmp, bl) == [])
    (tmp / "Lightlike" / "A.lean").write_text("local syntax \"a\" : term\n")
    bl.write_text("Lightlike/A.lean syntax 1\n")
    expect("constructs control: a baselined use passes", ci_check.scan_constructs(tmp, bl) == [])
    (tmp / "Lightlike" / "A.lean").write_text("theorem foo : True := trivial\n")
    expect("constructs planted: a baseline line whose use is gone must be lowered",
           len(ci_check.scan_constructs(tmp, bl)) == 1)
    expect("constructs: the real baseline matches the real tree",
           ci_check.scan_constructs() == [])

import api_map  # noqa: E402
import generated  # noqa: E402
expect("generated files: the guard tells generated from hand-written parts, and its planted changes fail",
       generated.selftest() == 0)
_ms = subprocess.run([sys.executable, str(HERE / "milestone_status.py"), "--selftest"], capture_output=True, text=True)
expect("milestone status: planted bad checklists fail the schema, and ticks follow the declarations' audit",
       _ms.returncode == 0)
_root = pathlib.Path(__file__).resolve().parent.parent
expect("review control: kernel-checked needs no reference; a human review with its issue URL passes",
       api_map.review_errors("x", "kernel-checked", None, _root) == []
       and api_map.review_errors("x", "human-reviewed", "https://github.com/o/r/issues/1", _root) == [])
expect("review planted: a human review without an issue URL, an unknown or retired level, a stray reference",
       all(api_map.review_errors("x", r, ref, _root) for r, ref in
           [("human-reviewed", None), ("human-reviewed", "docs/x.md"), ("peer-reviewed", "y"),
            ("agent-reviewed", "docs/x.md"), ("kernel-checked", "docs/x.md")]))


def _map_errs(abstract, content):
    """lint_map's errors for a one-entry API map with this abstract and content (citing [1] and {1})."""
    with tempfile.TemporaryDirectory() as d:
        r = pathlib.Path(d); (r / "Lightlike").mkdir()
        (r / "Lightlike" / "A.lean").write_text("theorem foo : True := trivial\n")
        (r / "Lightlike" / "API-map.md").write_text(
            f"# Area\n## Abstract (Alpha)\n{abstract}\n## Content (Alpha)\n{content}\n"
            "## Lean References\n1. Lightlike/A.lean - `foo`\n## References\n1. A. Author, A book.\n")
        return [e.split(": ", 1)[1] for e in api_map.lint_map(r, r / "Lightlike" / "API-map.md")[0]]


_math = "the integral `∫_{[0,1]^F} f` over\n`[0,1]^{P_n}`, the set `{0}` and `v[2]`"
expect("API map citations control: brackets and braces in code spans are math, not citations, in the abstract and "
       "the content (a span may wrap onto the next line)",
       _map_errs(f"A forest formula: {_math}.", f"It holds [1] {{1}}: {_math}.") == [])
expect("API map citations planted: a real [1, 2] in the content and a [1] in the abstract still fail beside a code span",
       _map_errs(f"It cites [1] beside {_math}.", f"It holds [1] and [1, 2] {{1}}: {_math}.")
       == ["the abstract must not cite", "each Lean citation needs its own brackets: [1] [2], not [1, 2]"])
expect("API map citations planted: a citation only inside a code span does not count, so its reference is never cited",
       _map_errs("A formula.", "It holds `[1]` {1}.") == ["Lean reference 1 is never cited"])
expect("API map citations planted: an unmatched backtick does not hide what follows it, and a span does not cross a "
       "blank line",
       _map_errs("A formula.", "It holds [1] ` [1, 2] {1}.") == ["each Lean citation needs its own brackets: [1] [2], not [1, 2]"]
       and _map_errs("A formula.", "It holds [1] `x\n\n[1, 2]` {1}.")
       == ["each Lean citation needs its own brackets: [1] [2], not [1, 2]"])

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
    old, base, checks0 = rp.ROOT, set(rp.NO_EXIT_BASELINE), list(rp.CHECKS)
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
    rp.CHECKS[:] = checks0

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
r, g = toy("      - name: good\n        run: echo a\n      - name: adv\n        continue-on-error: true\n"
           "        run: exit 1\n      - name: after\n        run: echo b > after.txt\n")
res = gate(r)
last = (res.stdout.strip().splitlines() or [""])[-1]
expect("gate planted: a failing advisory step is a named warning, and the gate goes on and passes",
       res.returncode == 0 and (r / "after.txt").exists()
       and last.startswith("GATE OK (1 advisory warning: [2] adv) "))
r, g = toy("      - name: good\n        run: echo a\n      - name: bad\n        run: exit 3\n")
res = gate(r)
last = (res.stdout.strip().splitlines() or [""])[-1]
expect("gate planted: the last line names the step that failed the gate",
       res.returncode == 1 and last.startswith("GATE FAILED at [2] bad "))
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
_v1 = {"areas": ["geometry"], "sizes": ["L"], "later": ["GE16"]}
expect("v1.0 membership: its areas and sizes select the milestones, `later` takes one out, another area stays out",
       tk.in_v1({"id": "GE1", "area": "geometry", "size": "L"}, _v1)
       and not tk.in_v1({"id": "GE16", "area": "geometry", "size": "L"}, _v1)
       and not tk.in_v1({"id": "CO1", "area": "cosmology", "size": "L"}, _v1)
       and not tk.in_v1({"id": "GE2", "area": "geometry", "size": "R"}, _v1))

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
       and "`/claim`" in _c1b and "48 hours" in _c1b and "Task: T-X1" in _c1b and "Status" not in _c1b)
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
_rc = tk.roadmap_counts("## G\n\n### Alpha\n\n- **Milestones:** 0 · [milestones](m#alpha) · [tasks](t#alpha)\n",
                        _ms, "o/r")
expect("tasks: generate keeps the ROADMAP milestone counts current and links each area's done milestones",
       "- **Milestones:** 4 · [milestones](m#alpha) · [tasks](t#alpha) · [done](https://github.com/o/r/" in _rc
       and "reason%3Acompleted" in _rc and "label%3A%22area%3A+alpha%22" in _rc
       and _rc.count(tk.DONE_LINK) == 1 and tk.roadmap_counts(_rc, _ms, "o/r") == _rc)
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
def _sync(tasks, cfg, data, card, seed=None):
    """sync_plan with the fixture's own clock, as `sync` passes it: without it the claim windows
    of the fixture comments run out with the real date."""
    return tk.sync_plan(tasks, cfg, data, card, seed, data.get("now"))


_card = lambda tid: (f"{tid}: title", "body")  # noqa: E731
_lapse = tk.MARK.format("lapse old 2026-10-01T00:00:00Z")
_data = {"now": "2026-11-07T00:00:00Z", "labels": tk.LIVE + sorted({x for t in _ts2 for x in t["labels"]}), "issues": [
    _iss(1, "[proof task] T-X1-P1: t", ["proof-task", "ready"], [
        _c("ann", "/claim via route 1", "2026-11-06T10:00:00Z"),
        _c("bob", "Attempting too", "2026-11-06T12:00:00Z"),
        _c("bob", "/unclaim, no time", "2026-11-06T13:00:00Z"),
        _c("cy", "attempting", "2026-09-01T00:00:00Z"),
        _c("ann", "a second note", "2026-11-06T14:00:00Z")]),
    _iss(2, "T-X1: x", ["milestone", "ready"], [_c("dee", "claiming", "2026-11-06T20:00:00Z")]),
    _iss(3, "T-B1: b", ["ready"], [_c("old", "claiming", "2026-10-01T00:00:00Z")], assignees=["old", "maint"]),
    _iss(4, "T-X2: s", ["blocked", "claimed"], [], state="closed", reason="completed"),
    _iss(5, "T-B2: dup", [], [], state="closed", reason="not_planned"),
    _iss(9, "T-X1: a later duplicate", [], [])],
    "pulls": [{"number": 7, "body": "<!--\nTask: T-X1\n-->\nTask: T-B1\n", "author": "eve", "state": "open",
               "updatedAt": "2026-11-05T00:00:00Z"}]}
_st, _acts = _sync(_ts2, _cfg2, _data, _card)
_on = lambda acts, tid, op: [a for a in acts if a.get("task") == tid and a["op"] == op]  # noqa: E731
_e = lambda acts, tid: (_on(acts, tid, "edit") or [{}])[0]  # noqa: E731
expect("tasks sync: a claim is a live `/claim` (or `claiming`, `attempting`) comment of the last 48 hours; "
       "released and expired ones drop out; a proof task is exclusive like any other",
       _e(_acts, "T-X1-P1").get("add") == ["claimed"] and _e(_acts, "T-X1-P1").get("remove") == ["ready"]
       and _e(_acts, "T-X1-P1").get("assign") == ["ann"]
       and tk.MARK.format("lapse cy 2026-09-01T00:00:00Z") in _on(_acts, "T-X1-P1", "comment")[0]["body"])
expect("tasks sync: a claim on a milestone's issue assigns the claimant and adds `claimed`; its other labels "
       "(ready, blocked, in review) are left to scripts/sync_github.py",
       _e(_acts, "T-X1") == dict(op="edit", task="T-X1", issue=2, add=["claimed"], remove=[],
                                 assign=["dee"], unassign=[]))
expect("tasks sync: a lapsed claim unassigns the claimant only and is announced; on a milestone's issue an "
       "open PR sets no label",
       _e(_acts, "T-B1").get("unassign") == ["old"] and not _e(_acts, "T-B1").get("add")
       and not _e(_acts, "T-B1").get("remove") and len(_on(_acts, "T-B1", "comment")) == 1
       and _lapse in _on(_acts, "T-B1", "comment")[0]["body"])
_data3 = json.loads(json.dumps(_data))
_data3["issues"][2]["comments"].append(_c("github-actions[bot]", "lapsed\n" + _lapse, "2026-11-06T00:00:00Z"))
_data3["issues"][2]["assignees"] = ["maint"]
_data3["issues"][2]["labels"] = ["in review"]
expect("tasks sync: the lapse notice is posted once and ends the claim",
       not [a for a in _sync(_ts2, _cfg2, _data3, _card)[1] if a.get("task") == "T-B1"])
_h = lambda n, a, when: _c(a, "/claim", when)  # noqa: E731
_dc = {"now": "2026-11-07T00:00:00Z", "labels": _data["labels"], "pulls": [], "issues": [
    _iss(21, "[proof task] T-X1-P1: t", ["proof-task", "ready"], [_h(0, "gus", "2026-11-06T01:00:00Z")]),
    _iss(22, "[proof task] T-X1-P2: t", ["proof-task", "ready"], [_h(0, "gus", "2026-11-06T02:00:00Z")]),
    _iss(23, "T-X1: x", ["milestone", "ready"], [_h(0, "gus", "2026-11-06T03:00:00Z")]),
    _iss(24, "T-B1: b", ["ready"], [_h(0, "gus", "2026-11-06T04:00:00Z")])]}
_acts_c = _sync(_ts2, _cfg2, _dc, _card)[1]
_ref = [a for a in _acts_c if a["op"] == "comment" and "refused" in a["body"]]
expect("tasks sync: a person holds at most 3 open claims; the fourth is refused with a comment and no assignment",
       len(_ref) == 1 and _ref[0]["task"] == "T-B1" and "already holds 3 open claims" in _ref[0]["body"]
       and tk.MARK.format("refused gus 2026-11-06T04:00:00Z") in _ref[0]["body"]
       and not _e(_acts_c, "T-B1").get("assign")
       and all(_e(_acts_c, t).get("assign") == ["gus"] for t in ("T-X1-P1", "T-X1-P2", "T-X1")))
_dc2 = json.loads(json.dumps(_dc))
_dc2["issues"][3]["comments"].append(_c("github-actions[bot]", "no\n" + _ref[0]["body"].split("\n\n")[-1],
                                        "2026-11-06T06:00:00Z"))
_dc2["issues"][3]["assignees"] = []
_dc2["issues"][3]["labels"] = ["ready"]
_dc2["issues"][0]["assignees"], _dc2["issues"][0]["labels"] = ["gus"], ["proof-task", "claimed"]
_dc2["issues"][1]["assignees"], _dc2["issues"][1]["labels"] = ["gus"], ["proof-task", "claimed"]
_dc2["issues"][2]["assignees"], _dc2["issues"][2]["labels"] = ["gus"], ["milestone", "claimed"]
expect("tasks sync: the refusal is posted once, and the refused claim does not come back by itself",
       not [a for a in _sync(_ts2, _cfg2, _dc2, _card)[1] if a["op"] in ("comment", "edit")])
_dc2["issues"][0]["comments"].append(_c("gus", "/unclaim", "2026-11-06T07:00:00Z"))
_dc2["issues"][3]["comments"].append(_c("gus", "/claim", "2026-11-06T08:00:00Z"))
expect("tasks sync: after `/unclaim` a slot is free and a new `/claim` is accepted",
       "gus" in _e(_sync(_ts2, _cfg2, _dc2, _card)[1], "T-X1-P1").get("unassign", [])
       and _e(_sync(_ts2, _cfg2, _dc2, _card)[1], "T-B1").get("assign") == ["gus"])
_dp = json.loads(json.dumps(_dc))
_dp["issues"] = [dict(_dp["issues"][0], comments=[_c("fay", "/claim", "2026-11-01T00:00:00Z")], assignees=["fay"],
                      labels=["proof-task", "claimed"]),
                 _iss(25, "T-X1: x", ["milestone", "claimed"], [_c("fay", "claiming", "2026-11-01T00:00:00Z")],
                      assignees=["fay"])]
_dp["pulls"] = [{"number": 9, "body": "Task: T-X1", "author": "fay", "state": "open",
                 "updatedAt": "2026-11-01T00:00:00Z"}]
_acts_p = _sync(_ts2, _cfg2, _dp, _card)[1]
expect("tasks sync: a claim past 48 hours is kept while a pull request naming the task is open, and released "
       "when there is none; a claim never lapses by comments alone",
       not _on(_acts_p, "T-X1", "comment") and not _e(_acts_p, "T-X1").get("remove")
       and len(_on(_acts_p, "T-X1-P1", "comment")) == 1
       and _e(_acts_p, "T-X1-P1").get("unassign") == ["fay"])
_dt = json.loads(json.dumps(_dc))
_dt["issues"] = [_iss(31, "T-X1: x", ["milestone", "claimed"],
                      [_c("amy", "/claim", "2026-11-06T10:00:00Z"), _c("ben", "/claim", "2026-11-06T11:00:00Z"),
                       _c("cat", "claiming", "2026-11-06T12:00:00Z")], assignees=["amy"])]
_acts_t = _sync(_ts2, _cfg2, _dt, _card)[1]
_tk = [a for a in _acts_t if a["op"] == "comment"]
expect("tasks sync: a second `/claim` on a held task is answered once with the holder and the expiry, and not recorded",
       len(_tk) == 2 and all("claimed by @amy" in a["body"] and "expires 2026-11-08T10:00:00Z" in a["body"] for a in _tk)
       and tk.MARK.format("taken ben 2026-11-06T11:00:00Z") in _tk[0]["body"] and not _e(_acts_t, "T-X1").get("assign"))
_dt["issues"][0]["comments"] += [_c("bot", "x\n" + a["body"].split("\n\n")[-1], "2026-11-06T13:00:00Z") for a in _tk]
expect("tasks sync: the taken notices are posted once; the holder keeps the task",
       not [a for a in _sync(_ts2, _cfg2, _dt, _card)[1] if a["op"] in ("comment", "edit")])
expect("tasks: the commands `/claim` and `/unclaim` and their old words are recognized, `/claimed` is not",
       all(tk.CLAIM.search(x) for x in ("/claim", "  /Claim please", "claiming", "attempting via 1"))
       and all(tk.RELEASE.search(x) for x in ("/unclaim", "stopping", "Unclaiming", "no longer attempting"))
       and not tk.CLAIM.search("/claimed") and not tk.CLAIM.search("I am claiming") and not tk.RELEASE.search("/unclaimed"))
expect("tasks sync: a closed milestone issue loses its claim labels (only) and makes its task done; a "
       "duplicate is ignored",
       _e(_acts, "T-X2").get("remove") == ["claimed"] and _st["T-X2"][0] == "done"
       and not _on(_acts, "T-B2", "create") and not [a for a in _acts if a.get("issue") == 9])
expect("tasks sync: a task that becomes ready gets an issue; a blocked one does not; a commented-out Task line is ignored",
       [a["labels"] for a in _on(_acts, "T-X1-P2", "create")] == [["proof-task", "area: alpha", "size: S",
                                                                   "intermediate", "ready"]]
       and not _on(_acts, "T-X4", "create") and not _on(_acts, "T-X3", "create"))
expect("tasks sync control: labels that exist are not created again",
       not [a for a in _acts if a["op"] == "label"])
_seed = {"closed": {"X4": "done (older work)"}, "notes": {"X3": "in progress"}}
_s1 = _sync(_ts2, _cfg2, _data, _card, _seed)[1]
expect("tasks sync: the seed opens and closes no milestone issue (scripts/sync_github.py opens and closes "
       "them)",
       not [a for a in _s1 if a.get("task") in ("T-X3", "T-X4")])
_data2 = json.loads(json.dumps(_data))
_data2["issues"] += [_iss(10, "T-X4: f", [], [_c("bot", tk.MARK.format("seed"), "2026-11-06T00:00:00Z")],
                          state="closed", reason="completed"),
                     _iss(11, "T-X3: t", ["milestone", "blocked"],
                          [_c("bot", tk.MARK.format("seed"), "2026-11-06T00:00:00Z")])]
expect("tasks sync: a second seed run changes nothing more",
       not [a for a in _sync(_ts2, _cfg2, _data2, _card, _seed)[1] if a.get("task") in ("T-X3", "T-X4")])
_bad = []
try:
    _sync(_ts2, _cfg2, _data, _card, {"closed": {"ZZ9": "done"}})
except ValueError:
    _bad.append(True)
expect("tasks sync planted: a seed entry that is not a task is refused", _bad == [True])
_s6 = _sync(_ts6, _cfg2, _data, _card)[1]
_data6 = json.loads(json.dumps(_data))
_data6["issues"][0]["comments"].append(_c("bot", tk.MARK.format("proven"), "2026-11-06T00:00:00Z"))
expect("tasks sync: a proof task proven on main has its issue closed, once",
       len(_on(_s6, "T-X1-P1", "close")) == 1 and "has no `sorry`" in _on(_s6, "T-X1-P1", "close")[0]["body"]
       and not _on(_sync(_ts6, _cfg2, _data6, _card)[1], "T-X1-P1", "close"))
_kind = {t["id"]: t["kind"] for t in _ts2 + _ts6}
expect("tasks sync: a milestone's issue is never opened or closed by `sync`, even when all its proof tasks are proven",
       not [a for a in _acts + _s1 + _s6 if a["op"] in ("create", "close") and _kind.get(a.get("task")) == "milestone"])
_sg = subprocess.run([sys.executable, str(HERE / "sync_github.py"), "--selftest"], capture_output=True, text=True)
expect("sync_github: status labels, columns and the GitHub Milestone follow the computed status; claim labels, "
       "closing and proof-task issues are left alone; writes are paced", _sg.returncode == 0)
_cc = subprocess.run([sys.executable, str(HERE / "consistency_check.py"), "--selftest"], capture_output=True, text=True)
expect("consistency check: planted duplicate issues, early closes, double claims, planning IDs, proven entries on open "
       "hypotheses and merge-queue entries without a milestone fail", _cc.returncode == 0)
_pi = subprocess.run([sys.executable, str(HERE / "planning_ids.py"), "--selftest"], capture_output=True, text=True)
expect("planning IDs: planted gap, milestone, row and catalogue IDs in Lean folder, file and declaration names fail; "
       "SixJRow, lower case, comments and task files do not", _pi.returncode == 0)

with tempfile.TemporaryDirectory() as d:
    tmp = pathlib.Path(d)
    (tmp / "Lightlike").mkdir()
    (tmp / "Tasks").mkdir()
    (tmp / "Lightlike" / "A.lean").write_text("theorem Lightlike.A.done (n : Nat) : n + 0 = n := rfl\n")
    _dt = [{"id": "T-X1-P1", "kind": "proof", "file": "Tasks/T.lean", "decl": "Lightlike.Tasks.t"}]
    (tmp / "Tasks" / "T.lean").write_text("theorem Lightlike.Tasks.t (n : Nat) : n + 0 = n := by\n  sorry\n")
    _dup_open = tk.library_duplicates(_dt, tmp)
    (tmp / "Tasks" / "T.lean").write_text("theorem Lightlike.Tasks.t (n : Nat) : n + 0 = n := by\n  rfl\n")
    _dup_done = tk.library_duplicates(_dt, tmp)
expect("tasks check: an open proof task whose statement the library proves is a duplicate",
       list(_dup_open) == ["T-X1-P1"])
expect("tasks check: once the task's own sorry is filled it is done, not a duplicate",
       _dup_done == {})
_nofile = tk.library_duplicates([{"id": "T-X1-P2", "kind": "proof", "decl": "Lightlike.Tasks.t"},
                                 {"id": "T-X1-P3", "kind": "proof", "file": "", "decl": "Lightlike.Tasks.t"}],
                                pathlib.Path("/nonexistent"))
expect("tasks check: a proof task without a file field is skipped, not a KeyError", _nofile == {})

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
    (tmp / "docs" / "results.d").mkdir()
    (tmp / "docs" / "results.d" / "new.yaml").write_text(
        (tmp / "docs" / "results.yaml").read_text().replace("LL-0001", "LL-XXXX"))
    (tmp / "docs" / "results.yaml").write_text("[]\n")
    expect("doc refs planted: the claim is reported when the result is a new entry in docs/results.d",
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

# Selection of the Python checks on a pull request (run_python_checks.py --changed): the quick set
# always, a slow check only when its script or a scripts/ module it imports changed, everything
# when the runner, the pinned packages or the workflow change.
_slow = {c for c, sl in rp.CHECKS if sl}
_quick = {c for c, sl in rp.CHECKS if not sl}
_sel = lambda *paths: set(rp.select(set(paths))[0])
expect("changed-file selection: a Lean or docs change runs the quick set and no slow check",
       _sel("Lightlike/A.lean", "docs/x.md") == _quick)
expect("changed-file selection: a slow script runs itself, the quick set and no other slow check",
       _sel("scripts/spinfoam/gauge_cutoff_limit.py") & _slow == {"scripts/spinfoam/gauge_cutoff_limit.py"})
expect("changed-file selection: a module a slow check imports runs that check",
       "scripts/spinfoam/gauge_cutoff_limit.py" in _sel("scripts/spinfoam/exact3j.py"))
expect("changed-file selection planted: a module no slow check imports selects none",
       _sel("scripts/regge/regge3d_core.py") & _slow == set())
expect("changed-file selection: the runner, requirements.txt and ci.yml run everything",
       all(_sel(f) == _slow | _quick for f in ("scripts/run_python_checks.py", "requirements.txt", ".github/workflows/ci.yml")))

# comparator_run.py: which task files are judged, and against which challenge
import comparator_run as cr  # noqa: E402
with tempfile.TemporaryDirectory() as _d:
    _r = pathlib.Path(_d)
    _g = lambda *a: subprocess.run(["git", "-C", str(_r), "-c", "user.name=t", "-c", "user.email=t@x", *a],
                                   check=True, capture_output=True, text=True).stdout.strip()
    _g("init", "-q", "-b", "main")
    (_r / "Tasks").mkdir(); (_r / "docs/tasks").mkdir(parents=True)
    _t = lambda n, k="proof": f'  - id: "T-{n}"\n    kind: "{k}"\n    file: "Tasks/{n}.lean"\n    decl: "Lightlike.{n}"\n'
    (_r / "docs/tasks/tasks.yaml").write_text("tasks:\n" + _t("A") + _t("B") + _t("C") + _t("D") + _t("M", "milestone"))
    for n in "ABCM":
        (_r / f"Tasks/{n}.lean").write_text(f"theorem {n} : True := by\n  sorry\n")
    (_r / "Tasks/D.lean").write_text("theorem D : True := trivial\n")
    _g("add", "-A"); _g("commit", "-q", "-m", "lock"); _lock = _g("rev-parse", "HEAD")
    (_r / "Tasks/A.lean").write_text("theorem A : True := by\n  trivial\n")
    (_r / "Tasks/B.lean").write_text("theorem B : True := by\n  sorry -- still open\n")
    (_r / "Tasks/M.lean").write_text("theorem M : True := trivial\n")
    (_r / "Tasks/D.lean").write_text("theorem D : True := trivial -- edited\n")
    (_r / "Tasks/E.lean").write_text("theorem E : True := trivial\n")
    _g("add", "-A"); _g("commit", "-q", "-m", "proofs"); _head = _g("rev-parse", "HEAD")
    _ch, _left = cr.select(_lock, _head, root=_r)
    _why = dict(_left)
    _src = ("namespace A\nnamespace B\ndef f : Nat := 0\nprotected abbrev g := 1\nprivate def h := 2\nend B\n"
            "-- def c := 3\n/- def d := 4 -/\nstructure S where\n  x : Nat\nend A\ndef _root_.top := 5\n"
            "theorem t : True := by sorry\n")
    expect("comparator definitions: namespaces, protected, private, comments, _root_",
           cr.definition_names(_src) == ["A.B.f", "A.B.g", "A.S", "top"])
    expect("comparator definitions: none declared gives an empty list (flag off)",
           cr.definition_names("theorem t : True := by sorry\n") == [])
    expect("comparator definitions: the configuration carries them (flag on) and defaults to none",
           cr.config("T", defs=["A.f"])["definition_names"] == ["A.f"] and cr.config("T")["definition_names"] == [])
    expect("comparator: a newly proved task file is judged, the challenge is the locked file with its sorry",
           [c[0] for c in _ch] == ["Tasks/A.lean"] and cr.has_sorry(_ch[0][2]) and not cr.has_sorry(_ch[0][3])
           and _ch[0][1] == "Lightlike.A")
    expect("comparator planted: a task file that still has sorry is not judged", _why.get("Tasks/B.lean") == "still has sorry")
    expect("comparator planted: a non-proof task and an unlisted file are not judged",
           "Tasks/M.lean" in _why and "Tasks/E.lean" in _why)
    expect("comparator planted: a file whose first version had no sorry has no challenge and is not judged",
           "Tasks/D.lean" in _why and "nothing to compare" in _why["Tasks/D.lean"])
    expect("comparator: an unchanged file is not judged without --all",
           "Tasks/C.lean" not in _why and "Tasks/C.lean" not in [c[0] for c in _ch])
    expect("comparator: --all judges every proved task file",
           [c[0] for c in cr.select(None, _head, root=_r, everything=True)[0]] == ["Tasks/A.lean"])
    expect("comparator: the config names the standard three axioms and the declaration",
           cr.config("Lightlike.A")["permitted_axioms"] == ["propext", "Quot.sound", "Classical.choice"]
           and cr.config("Lightlike.A")["theorem_names"] == ["Lightlike.A"])
    # a statement corrected while the task was open (statement-fix): the proof is judged against it
    (_r / "Tasks/C.lean").write_text("theorem C (h : True) : True := by\n  sorry\n")
    _g("add", "-A"); _g("commit", "-q", "-m", "statement fix"); _fixed = _g("rev-parse", "HEAD")
    (_r / "Tasks/C.lean").write_text("theorem C (h : True) : True := h\n")
    _g("add", "-A"); _g("commit", "-q", "-m", "proof"); _proved = _g("rev-parse", "HEAD")
    _ch2 = cr.select(_fixed, _proved, root=_r)[0]
    expect("comparator: after a statement fix the challenge is the corrected statement, not the first one",
           [c[0] for c in _ch2] == ["Tasks/C.lean"] and "(h : True)" in _ch2[0][2] and cr.has_sorry(_ch2[0][2]))
    (_r / "Tasks/B.lean").write_text("theorem B (x : Nat) : True := trivial\n")
    _g("add", "-A"); _g("commit", "-q", "-m", "statement change with proof"); _both = _g("rev-parse", "HEAD")
    _ch3 = cr.select(_proved, _both, root=_r)[0]
    expect("comparator planted: a statement changed together with its proof is compared with the base version",
           [c[0] for c in _ch3] == ["Tasks/B.lean"] and "(x : Nat)" not in _ch3[0][2] and "(x : Nat)" in _ch3[0][3])

# Shared slots of the Python checks (LL_CHECK_SLOTS): at most n scripts at a time over all runs
import tempfile as _tf, os
_sd = os.path.join(_tf.mkdtemp(), "slots")
_s1 = rp.take_slot(_sd, 2); _s2 = rp.take_slot(_sd, 2)
expect("check slots: two slots are two different directories, owned by this process",
       _s1 != _s2 and open(os.path.join(_s1, "pid")).read() == str(os.getpid()))
try:
    subprocess.run([sys.executable, "-I", "-c",
                    f"import sys; sys.path.insert(0, {str(HERE)!r}); import run_python_checks as r; r.take_slot({_sd!r}, 2)"],
                   capture_output=True, text=True, timeout=5)
    _waited = False
except subprocess.TimeoutExpired:
    _waited = True
expect("check slots planted: a third taker waits while both slots are held by live processes", _waited)
open(os.path.join(_s1, "pid"), "w").write("999999")
expect("check slots: a slot whose owner process is gone is taken over", rp.take_slot(_sd, 2) == _s1)

# Book locations in a full text (sources.py, `fulltext:` with `edition:`): the label where the
# result is stated, not where it is cited, and the stated page its printed page. A planted book
# of 12 PDF pages: two unnumbered front pages, then printed pages 1-10 (offset 2); Theorem 1.2 is
# stated on printed p. 4 and cited on p. 7, equation (1.5) set on p. 5 and cited on p. 8.
import contextlib, hashlib, io, json as _json  # noqa: E402
import sources as src  # noqa: E402


def _bk_pages(numbered=True):
    pages = ["A Planted Book on Compact Operators\n\n   by A. Author\n", "Contents\n  1. Operators   3\n"]
    for n in range(1, 11):
        body = [f"   {'Some filler text about operators.':<60}"] * 3
        if n == 4:
            body += ["Theorem 1.2 (Planted spectral theorem). Let K be compact. Then K has a basis."]
        if n == 5:
            body += ["          (Kx, y) = (x, K*y)                                  (1.5)"]
        if n == 7:
            body += ["   As Theorem 1.2 shows, every compact K has a basis of eigenvectors."]
        if n == 8:
            body += ["   We use (1.5) here, and a compact operator again."]
        head = f"{n}          1. Operators" if numbered and n % 2 == 0 else f"1. Operators          {n}"
        pages.append("\n".join([head if numbered else "1. Operators", ""] + body + [""]))
    return pages


_bp = _bk_pages()
_off, _how = src.page_offset(_bp)
expect("sources fulltext: the page offset is the one the printed page numbers agree on (the contents page's '3' "
       "is outvoted)", _off == 2 and "10 of 11" in _how)


def _bkl(loc, kws=(), pages=_bp, off=_off, why=_how):
    return src.check_fulltext_location(pages, loc, list(kws), off, why)


_r = _bkl("Theorem 1.2, p. 7", ["compact"])
expect("sources fulltext planted: a theorem cited on the stated page, stated on another, fails naming the printed "
       "page where it is stated", not _r[0] and _r[2] == "stated on printed p. 4, not p. 7")
expect("sources fulltext planted: the arXiv rule (the label anywhere) would have accepted that location",
       src.check_location("\n".join(_bp[8:]), "Theorem 1.2", ["compact"])[0])
expect("sources fulltext control: the theorem on the page where it is stated passes, with that printed page",
       _bkl("Theorem 1.2, p. 4", ["compact"])[0::3] == (True, 4)
       and _bkl("Theorem 1.2, pp. 3-4")[0] and _bkl("Theorem 1.2")[0::3] == (True, 4))
expect("sources fulltext planted: the label stated without a check word near it fails",
       _bkl("Theorem 1.2, p. 4", ["Hilbert-Schmidt"])[2] == "label not found where it is stated with a check word near it")
expect("sources fulltext planted: an equation cited on the stated page fails; control: the page where it is set passes",
       _bkl("eq. (1.5), p. 8")[2] == "stated on printed p. 5, not p. 8" and _bkl("eq. (1.5), p. 5")[0::3] == (True, 5))
_bu = _bk_pages(numbered=False)
_uo = src.page_offset(_bu)
expect("sources fulltext planted: pages without printed numbers fail a page, naming page_offset; control: "
       "page_offset in sources.yaml",
       _uo[0] is None and not _bkl("Theorem 1.2, p. 4", pages=_bu, off=None, why=_uo[1])[0]
       and "page_offset" in _bkl("Theorem 1.2, p. 4", pages=_bu, off=None, why=_uo[1])[2]
       and _bkl("Theorem 1.2, p. 4", pages=_bu, off=2)[0])
expect("sources fulltext: the page is split off the location", src.split_page("Theorem 6.6, p. 136") == ("Theorem 6.6", (136, 136))
       and src.split_page("eq. (2.10), pp. 50-51") == ("eq. (2.10)", (50, 51)) and src.split_page("Section 4") == ("Section 4", None))


# A scanned book's text layer: OCR reads the label word with confused letters, m as two or three
# of its strokes (MEASURED in Loomis-Sternberg's scan: 'Theorelll' 34 times, 'TheoreIn', 'TheoreDl',
# 'TheorelD', 'TheorelU', 'LeDlDla', 'Lelllllla'), so the statement on p. 4 is planted as OCR gives it.
def _ocr(word, num=" 1.2"):
    return [p.replace("Theorem 1.2 (Planted", word + num + " (Planted") for p in _bp]


_ocr_ok = ("Theorelll", "TheoreIn", "TheoreDl", "TheorelD", "TheoreD1", "TheorelU", "Theorern", "Thcorem", "The0rem",
           "THEOREIN")
expect("sources fulltext planted (OCR): the label word read with OCR's letter confusions (m as two or three strokes; "
       "e as c; o as 0) passes on the page where it is stated: " + ", ".join(_ocr_ok),
       all(_bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr(w))[0::3] == (True, 4) for w in _ocr_ok))
expect("sources fulltext planted (OCR): a lemma read with l as 1, I or |, m as strokes passes ('LeDlDla', "
       "'Lelllllla', '1emrna', 'Iemma', '|emma')",
       all(src.check_fulltext_location(["x\n" + w + " 3.1. Let K be compact.\n"], "Lemma 3.1", ["compact"], None)[0]
           for w in ("LeDlDla", "Lelllllla", "1emrna", "Iemma", "|emma")))
expect("sources fulltext control (OCR): a misspelling OCR does not make fails ('Theoram', 'Theoren' (m as one "
       "stroke), 'Tbeorem', 'Theorellll' (four strokes), 'Theo rem')",
       not any(_bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr(w))[0]
               for w in ("Theoram", "Theoren", "Tbeorem", "Theorellll", "Theo rem")))
expect("sources fulltext planted (OCR): a stroke read as 1 is never the number's first digit ('TheoreD11.2' is not "
       "Theorem 1.2); control: 'TheoreD1 1.2' is",
       not _bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr("TheoreD1", "1.2"))[0]
       and _bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr("TheoreD1"))[0])
expect("sources fulltext control (OCR): the cited occurrence is still not the statement",
       _bkl("Theorem 1.2, p. 7", ["compact"], pages=_ocr("Theorelll"))[2] == "stated on printed p. 4, not p. 7")
# A full stop the OCR put after the word (MEASURED in the same scan: 'Theorem. 3.1.' five times).
expect("sources fulltext planted (OCR): a full stop after the label word passes ('Theorem. 1.2', 'Theorelll. 1.2'); "
       "control: two full stops fail, 'Theorem. 11.2' is not Theorem 1.2",
       all(_bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr(w))[0::3] == (True, 4) for w in ("Theorem.", "Theorelll."))
       and not _bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr("Theorem.."))[0]
       and not _bkl("Theorem 1.2, p. 4", ["compact"], pages=_ocr("Theorem.", " 11.2"))[0])

# verify and check end to end, offline: the PDF is already in the cache under its URL, the
# publisher record and the citations are stubbed, and any other network call fails the test.
_bt = pathlib.Path(tempfile.mkdtemp())
_bdata = b"%PDF-1.4 planted book"
_burl = "https://example.org/planted-book.pdf"
_bpdf = _bt / "cache" / ("url-" + hashlib.sha256(_burl.encode()).hexdigest()[:20] + ".pdf")
_bpdf.parent.mkdir()
_bpdf.write_bytes(_bdata)
_bpdf.with_suffix(".pages.txt").write_text("\f".join(_bp) + "\f")
(_bt / "docs/tasks").mkdir(parents=True)
_bsaved = {k: getattr(src, k) for k in ("get", "openlibrary", "citations", "arxiv_meta", "location_uses", "CACHE",
                                         "SOURCES", "VERIFIED", "ROOT")}
_bnet = []


def _bk_run(ref, cmd):
    (_bt / "docs/tasks/sources.yaml").write_text(_json.dumps({"references": {"planted-book": ref}, "milestones": {
        "B1": {"class": "sourced", "refs": [{"ref": "planted-book", "location": "Theorem 1.2, p. 4", "check": "compact"},
                                            {"ref": "planted-book", "location": "Theorem 1.2, p. 7", "check": "compact"}]}}}))
    out = io.StringIO()
    with contextlib.redirect_stdout(out):
        rc = src.cmd_verify({"planted-book"}) if cmd == "verify" else src.cmd_check()
    return rc, out.getvalue(), _json.loads(src.VERIFIED.read_text()).get("planted-book") if src.VERIFIED.exists() else None


try:
    src.get = lambda url, *a, **k: _bnet.append(url)
    src.openlibrary = lambda isbn: {"title": "A Planted Book on Compact Operators", "authors": [], "year": "2009"}
    src.citations = lambda ref: (None, "stub")
    src.arxiv_meta = lambda ids: {}
    src.CACHE, src.ROOT = _bt / "cache", _bt
    src.SOURCES, src.VERIFIED = _bt / "docs/tasks/sources.yaml", _bt / "docs/tasks/sources-verified.json"
    src.location_uses = _bsaved["location_uses"]
    _bref = {"cite": "A. Author, A Planted Book (2009)", "title": "A Planted Book on Compact Operators", "isbn": "9780000000000",
             "fulltext": _burl, "edition": "the author's online edition of the printed book"}
    _rc, _o, _rec = _bk_run({**_bref, "sha256": hashlib.sha256(_bdata).hexdigest()}, "verify")
    _locs = _rec["locations"]
    expect("sources verify control: the cached full text is used, its hashes recorded, the stated page verified with its "
           "printed page; planted: the cited page is not",
           _rc == 0 and not _bnet and _rec["fulltext"]["sha256"] == hashlib.sha256(_bdata).hexdigest()
           and _rec["fulltext"]["md5"] == hashlib.md5(_bdata).hexdigest() and _rec["fulltext"]["page_offset"] == 2
           and _locs["Theorem 1.2, p. 4"]["verified"] and _locs["Theorem 1.2, p. 4"]["page"] == 4
           and not _locs["Theorem 1.2, p. 7"]["verified"] and _locs["Theorem 1.2, p. 7"]["why"] == "stated on printed p. 4, not p. 7")
    _rc2, _o2, _ = _bk_run({**_bref, "sha256": hashlib.sha256(_bdata).hexdigest()}, "check")
    expect("sources check: the planted cited page is reported as not verified, the stated page is not",
           _rc2 == 1 and "location 'Theorem 1.2, p. 7' in planted-book not verified" in _o2
           and "'Theorem 1.2, p. 4'" not in _o2 and "full text" not in _o2)
    _rc3, _o3, _ = _bk_run({**_bref, "sha256": "0" * 64}, "check")
    expect("sources check planted: a pinned sha256 other than the verified file's asks for verify again",
           _rc3 == 1 and "the full text in sources-verified.json is not the one sources.yaml names" in _o3)
    _rc4, _o4, _rec4 = _bk_run({**_bref, "sha256": "0" * 64}, "verify")
    expect("sources verify planted: a fetched file whose sha256 is not the pinned one fails verify, every location unverified",
           _rc4 == 1 and "is not sources.yaml's " + "0" * 64 in _o4 and "FAIL planted-book" in _o4
           and not any(v["verified"] for v in _rec4["locations"].values()))
    _rc5, _o5, _rec5 = _bk_run({k: v for k, v in _bref.items() if k != "edition"}, "verify")
    _rc6, _o6, _ = _bk_run({k: v for k, v in _bref.items() if k != "edition"}, "check")
    expect("sources planted: fulltext without edition fails verify (nothing fetched) and check",
           _rc5 == 1 and not _bnet and "fulltext needs edition" in _rec5["fulltext"]["why"]
           and _rc6 == 1 and "planted-book: fulltext needs edition" in _o6)
    _rc7, _o7, _ = _bk_run({k: v for k, v in _bref.items() if k != "fulltext"}, "check")
    expect("sources check planted: edition without fulltext is refused", "planted-book: edition belongs to a fulltext" in _o7)
finally:
    for _k, _v in _bsaved.items():
        setattr(src, _k, _v)

# The same check on a real book, only with LIGHTLIKE_NET=1 (it downloads 1.5 MB): G. Teschl,
# Mathematical Methods in Quantum Mechanics, the author's online edition of GSM 99 (AMS 2009).
if os.environ.get("LIGHTLIKE_NET") == "1":
    _tr = {"title": "Mathematical Methods in Quantum Mechanics", "edition": "online edition of GSM 99 (AMS 2009)",
           "fulltext": "https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf",
           "sha256": "8dc8de0b58aa0a3fedfe594a345f9b5875322e5526ea581cb640a98d55b82818"}
    _tft, _tpages = src.fulltext_record(_tr, pathlib.Path(tempfile.mkdtemp()))
    _tl = lambda loc, kws=(): src.check_fulltext_location(_tpages or [], loc, list(kws), _tft["page_offset"], _tft["pages_from"])
    expect("sources fulltext network: Teschl's PDF has the pinned sha256 and md5, printed page = PDF page - 12",
           _tft["why"] is None and _tft["md5"] == "e7b3488759cfa229d2d145b96eb9828b" and _tft["page_offset"] == 12)
    expect("sources fulltext network: Theorem 6.6 p. 136, Theorem 6.7 p. 137 and Lemma 6.12 p. 141 pass",
           _tl("Theorem 6.6, p. 136", ["compact"])[0::3] == (True, 136) and _tl("Theorem 6.7, p. 137")[0]
           and _tl("Lemma 6.12, p. 141")[0])
    expect("sources fulltext network planted: Theorem 6.6 at p. 137 fails, naming p. 136",
           _tl("Theorem 6.6, p. 137", ["compact"])[2] == "stated on printed p. 136, not p. 137")
else:
    print("skip sources fulltext network (LIGHTLIKE_NET=1 runs it)")

# The contributors list and the weekly leaderboard.
import contributors as ct  # noqa: E402
import datetime as _dt  # noqa: E402
_now = _dt.datetime(2026, 11, 20, tzinfo=_dt.timezone.utc)
_pr2 = lambda a, when, body="Task: T-A-P1": {"author": a, "mergedAt": when, "body": body}  # noqa: E731
_rows, _wk = ct.tally([_pr2("ann", "2026-11-19T00:00:00Z"), _pr2("ann", "2026-11-18T00:00:00Z", "Task: T-A-P2\nTask: T-A-P3"),
                       _pr2("bob", "2026-11-01T00:00:00Z"), _pr2("cy", "2026-11-19T00:00:00Z", "Task: T-A\n"),
                       _pr2("bot[bot]", "2026-11-19T00:00:00Z"), _pr2("dee", None), _pr2("eve", "2026-11-19T00:00:00Z",
                                                                                         "<!-- Task: T-A-P9 -->")], _now)
expect("contributors: merged pull requests and proof tasks per account; the week counts only the last 7 days, "
       "bots, unmerged pull requests, milestone tasks and commented-out lines do not count",
       _rows == [("ann", 2, 3), ("bob", 1, 1), ("cy", 1, 0), ("eve", 1, 0)] and _wk == [("ann", 3)])
_body = ct.render(_rows, _wk, _now)
expect("contributors: the rendered body has the marker, the leaderboard and the list",
       _body.startswith(ct.MARK) and "| 1 | @ann | 3 |" in _body and "| @bob | 1 | 1 |" in _body)
expect("contributors: the issue is found by its marker, and no other issue",
       ct.find_issue([{"number": 3, "body": "x"}, {"number": 5, "body": "a " + ct.MARK}, {"number": 9, "body": ct.MARK}]) == 5
       and ct.find_issue([{"number": 3, "body": "x"}, {"number": 4, "body": None}]) is None)
# Auto-merge of proof-task pull requests: the decision is made from the body and the API file list only.
import automerge as am  # noqa: E402
_pf = {"T-X1-P1": "Tasks/X/T_X1_P1.lean", "T-X1-P2": "Tasks/X/T_X1_P2.lean"}
_pr = lambda body="Task: T-X1-P1\n", **kw: dict(  # noqa: E731
    dict(state="open", draft=False, base={"ref": "main"}, body=body, labels=[]), **kw)
_fl = lambda *names, status="modified": [{"filename": n, "status": status} for n in names]  # noqa: E731
_own = "Tasks/X/T_X1_P1.lean"
expect("automerge: a proof-task pull request that changes exactly its own task file is eligible",
       am.decide(_pr(), _fl(_own), _pf)[0] and am.plan(True, []) == ["label", "auto"]
       and am.plan(True, ["automerge"]) == ["auto"])
expect("automerge planted: any other file, an added, renamed or removed file, a second task file is not eligible",
       not am.decide(_pr(), _fl(_own, "Lightlike/A.lean"), _pf)[0]
       and not am.decide(_pr(), _fl(_own, "Tasks/X/T_X1_P2.lean"), _pf)[0]
       and not am.decide(_pr(), _fl(_own, status="added"), _pf)[0]
       and not am.decide(_pr(), _fl(_own, status="renamed"), _pf)[0]
       and not am.decide(_pr(), _fl("Tasks/X/T_X1_P2.lean"), _pf)[0] and not am.decide(_pr(), [], _pf)[0])
expect("automerge planted: no Task line, `Task: none`, a milestone task, two task lines, or a task line only in a "
       "comment is not eligible",
       not am.decide(_pr("text"), _fl(_own), _pf)[0] and not am.decide(_pr("Task: none"), _fl(_own), _pf)[0]
       and not am.decide(_pr("Task: T-X1\n"), _fl(_own), _pf)[0]
       and not am.decide(_pr("Task: T-X1-P1\nTask: T-X1-P2\n"), _fl(_own), _pf)[0]
       and not am.decide(_pr("Task: T-X1-P1\nTask: none\n"), _fl(_own), _pf)[0]
       and not am.decide(_pr("<!-- Task: T-X1-P1 -->"), _fl(_own), _pf)[0]
       and am.decide(_pr("<!-- Task: T-X1-P2 -->\nTask: T-X1-P1\n"), _fl(_own), _pf)[0])
expect("automerge planted: a closed, draft or non-main pull request is not eligible",
       not am.decide(_pr(state="closed"), _fl(_own), _pf)[0] and not am.decide(_pr(draft=True), _fl(_own), _pf)[0]
       and not am.decide(_pr(base={"ref": "dev"}), _fl(_own), _pf)[0])
expect("automerge: a pull request that stops being eligible loses the label and auto-merge; others are left alone",
       am.plan(False, ["automerge", "x"]) == ["unlabel", "noauto"] and am.plan(False, ["x"]) == []
       and am.plan(False, []) == [])
with tempfile.TemporaryDirectory() as _d:
    _fx = pathlib.Path(_d) / "f.json"
    _fx.write_text(json.dumps({"pr": _pr(labels=[{"name": "automerge"}]), "files": _fl(_own, "scripts/x.py"),
                               "proof_files": _pf}))
    _o = subprocess.run([sys.executable, str(HERE / "automerge.py"), "--selftest-data", str(_fx)],
                        capture_output=True, text=True)
    expect("automerge: the command line decides on a fixture and shows the steps",
           json.loads(_o.stdout)["steps"] == ["unlabel", "noauto"] and not json.loads(_o.stdout)["eligible"])
expect("automerge: proof_files reads the proof tasks of tasks.yaml",
       am.proof_files(HERE.parent).get("T-GE2-P1", "").endswith("T_GE2_P1.lean")
       and not any(k.count("-P") == 0 for k in am.proof_files(HERE.parent)))
# The review gate (a commit status): pull requests carry no review label and merge when their checks pass.
import review_gate as rg  # noqa: E402
_prr = lambda author="ann", body="": dict(state="open", base={"ref": "main"}, body=body, user={"login": author},  # noqa: E731
                                          head={"sha": "s1"}, labels=[])
expect("review gate: every pull request passes, a Lean change of Lightlike/ or Tasks/ included",
       all(rg.evaluate(_prr(), f)[0] == "success" for f in (
           [], [{"filename": "docs/a.md", "status": "modified"}], [{"filename": "Lightlike/A.lean", "status": "modified"}],
           [{"filename": "Tasks/X/T_X1_P1.lean", "status": "added"}, {"filename": "Lightlike/N.lean", "status": "added"}])))
expect("review gate: the old label needs-review is removed where present and never added",
       rg.label_plan(["needs-review", "x"]) == ["unlabel"] and rg.label_plan([]) == [] and rg.label_plan(["claimed"]) == [])
expect("review gate planted: no code path of the script adds a label",
       "labels[]=" not in (HERE / "review_gate.py").read_text() and '"POST", "-f", f"labels' not in (HERE / "review_gate.py").read_text())
print("selftest:", "OK" if not fails else f"FAILED ({len(fails)})")
sys.exit(1 if fails else 0)
