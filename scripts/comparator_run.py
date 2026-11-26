#!/usr/bin/env python3
"""Runs `lake comparator` on the proof tasks that a change has just proved.

    python3 scripts/comparator_run.py --before <sha> --after <sha> [--paranoid] [--dry-run]
    python3 scripts/comparator_run.py --all [--paranoid] [--dry-run]

For each task file under Tasks/ (docs/tasks/tasks.yaml gives its declaration) that the change
(`--before`..`--after`: a pull request's merge commit against its base, a merge-queue run against the
queue's base, or a push to main against the previous main) changed
and that no longer contains `sorry`, the challenge is the file as first committed (the locked
statement, with its `sorry`) and the solution is the file now. `lake comparator` then establishes
that the solution proves the same statement as the challenge (kernel type equality of the theorem,
and of every definition the task file declares itself: `definition_names`, see definition_names()), uses only the standard axioms and
is accepted by the kernel; `--paranoid` also runs the external kernels. `--all` takes every proved
task file (the weekly run).

It extends, not replaces, scripts/proof_task_check.py (statement text unchanged, in a pull
request) and the axiom audit (audited theorems only). .github/workflows/comparator.yml runs it as the
required check `comparator` of pull requests and merge-queue runs, and, without blocking, after a push to
main and weekly. `--dry-run` prints the selection and each
comparator configuration and runs nothing; without it the script needs `lake` and `bwrap` and edits the
working copy (two scratch modules and their lean_lib entries in the root lakefile), so run it only on a
disposable CI checkout. Exit 0 all accepted or nothing to judge, 1 a rejection, 2 could not run."""
import argparse
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import leansrc  # noqa: E402

TASKS_YAML = "docs/tasks/tasks.yaml"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
SORRY = re.compile(r"\bsorry\b")
ZERO = "0" * 40
LIB = '\n[[lean_lib]]\nname = "{}"\n'


def git(*args, root=ROOT, check=True):
    r = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout


def show(rev, path, root=ROOT):
    r = subprocess.run(["git", "-C", str(root), "show", f"{rev}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def has_sorry(text):
    code = "".join(ch if c else " " for ch, c in zip(text, leansrc.code_mask(text)))
    return bool(SORRY.search(code))


def task_decls(rev, root=ROOT):
    """{file: declaration} for the proof tasks of docs/tasks/tasks.yaml at `rev`."""
    import yaml
    text = show(rev, TASKS_YAML, root)
    data = yaml.safe_load(text) if text else {}
    items = data.get("tasks", data) if isinstance(data, dict) else data
    return {t["file"]: t["decl"] for t in items or [] if isinstance(t, dict) and t.get("kind") == "proof"
            and t.get("file") and t.get("decl")}


def lock_text(path, rev, root=ROOT):
    """The task file as last locked: the newest committed version that still carries its sorry.
    This is the file as first committed unless the statement was corrected while the task was open
    (a statement-fix pull request): the proof is then judged against the corrected statement. A
    pull request that fills the sorry and changes the statement together is still compared with the
    version in the base (`rev` is the base of the change), so the change is rejected."""
    for commit in git("log", "--format=%H", rev, "--", path, root=root).split():
        text = show(commit, path, root)
        if text is not None and has_sorry(text):
            return text
    return None


def select(before, after, root=ROOT, everything=False):
    """[(file, decl, challenge text, solution text)] and [(file, why)] for the files left out."""
    decls = task_decls(after, root)
    base = after
    if everything:
        files = sorted(f for f in git("ls-tree", "-r", "--name-only", after, "--", "Tasks", root=root).split()
                       if f.endswith(".lean"))
    else:
        base = before if before and before != ZERO else f"{after}^"
        files = sorted(f for f in git("diff", "--name-only", base, after, "--", "Tasks", root=root).split()
                       if f.endswith(".lean"))
    chosen, left = [], []
    for f in files:
        now = show(after, f, root)
        if now is None:
            left.append((f, "deleted"))
        elif f not in decls:
            left.append((f, "not a proof task in tasks.yaml"))
        elif has_sorry(now):
            left.append((f, "still has sorry"))
        else:
            lock = lock_text(f, base, root)
            if lock is None or not has_sorry(lock):
                left.append((f, "no locked version with a sorry: nothing to compare against"))
            else:
                chosen.append((f, decls[f], lock, now))
    return chosen, left


DEF_LINE = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:protected|noncomputable|unsafe)[ \t]+)*"
                      r"(?:def|abbrev|structure|inductive|class)[ \t]+([^\s:({\[⦃]+)", re.M)
SCOPE = re.compile(r"^[ \t]*(namespace|section|end)\b[ \t]*([^\s]*)", re.M)


def definition_names(text):
    """Full names of the definitions (def, abbrev, structure, inductive, class) that a task file
    declares itself, with the enclosing namespaces: the ones a solution could change to make the
    statement easier. Definitions of imported modules are the same on both sides. Comments and
    strings are ignored; `private` ones are skipped (mangled names, not reachable by name)."""
    code = "".join(ch if c else " " for ch, c in zip(text, leansrc.code_mask(text)))
    events = sorted([(m.start(), "scope", m) for m in SCOPE.finditer(code)]
                    + [(m.start(), "def", m) for m in DEF_LINE.finditer(code)])
    stack, names = [], []
    for _, kind, m in events:
        if kind == "def":
            n = m.group(1)
            ns = [x for k, nm in stack if k == "namespace" for x in nm.split(".")]
            names.append(n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n]))
        elif m.group(1) == "end":
            if stack:
                stack.pop()
        else:
            stack.append((m.group(1), m.group(2)))
    return names


def config(decl, challenge="ComparatorChallenge", solution="ComparatorSolution", defs=()):
    return {"challenge_module": challenge, "solution_module": solution,
            "theorem_names": [decl], "definition_names": list(defs), "permitted_axioms": AXIOMS}


def run_one(f, decl, lock, now, paranoid, dry, root=ROOT):
    ch, so = (root / "ComparatorChallenge").with_suffix(".lean"), (root / "ComparatorSolution").with_suffix(".lean")
    cfg = (root / "comparator").with_suffix(".json")
    print(f"== {f}: {decl}")
    if dry:
        print(json.dumps(config(decl, defs=definition_names(lock)), indent=2))
        return 0
    lake = (root / "lakefile").with_suffix(".toml")
    orig = lake.read_text()
    try:
        ch.write_text(lock)
        so.write_text(now)
        cfg.write_text(json.dumps(config(decl, defs=definition_names(lock))))
        lake.write_text(orig + LIB.format("ComparatorChallenge") + LIB.format("ComparatorSolution"))
        cmd = ["lake", "comparator"] + (["--paranoid"] if paranoid else [])
        r = subprocess.run(cmd, cwd=root)
        return r.returncode
    finally:
        lake.write_text(orig)
        for p in (ch, so, cfg):
            p.unlink(missing_ok=True)


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--before")
    ap.add_argument("--after", default="HEAD")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--paranoid", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    if not a.all and not a.before:
        ap.error("give --before <sha> (the push's previous main) or --all")
    after = git("rev-parse", "--verify", f"{a.after}^{{commit}}").strip()
    chosen, left = select(a.before, after, everything=a.all)
    for f, why in left:
        print(f"skip {f}: {why}")
    if not chosen:
        print("comparator: no newly proved task file; nothing to judge")
        return 0
    worst, rows = 0, []
    for f, decl, lock, now in chosen:
        rc = run_one(f, decl, lock, now, a.paranoid, a.dry_run)
        rows.append((f, decl, "dry run" if a.dry_run else {0: "accepted", 1: "REJECTED"}.get(rc, f"could not run (exit {rc})")))
        worst = max(worst, 1 if rc == 1 else 2 if rc else 0)
    summary = "\n".join(["| task file | declaration | comparator |", "|---|---|---|"]
                        + [f"| {f} | `{d}` | {v} |" for f, d, v in rows])
    print(summary)
    out = os.environ.get("GITHUB_STEP_SUMMARY")
    if out:
        with open(out, "a") as fh:
            fh.write("## lake comparator" + (" (paranoid)" if a.paranoid else "") + "\n\n" + summary + "\n")
    return worst


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
