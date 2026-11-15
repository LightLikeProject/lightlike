#!/usr/bin/env python3
"""Checks that a proof-task pull request changes only the proof of its task's declaration.

    python3 scripts/proof_task_check.py --base <ref> --head <ref> --body-file pr_body.txt [--proof-label]
    python3 scripts/proof_task_check.py --base <ref> --head <ref> --task T-DT4-P1
    python3 scripts/proof_task_check.py --base <ref> --head <ref> --file F.lean --decl name

A pull request is a proof task if it has the `proof-task` label (`--proof-label`) or its `Task:`
line is a proof-task ID `T-<task>-P<n>`; only then is it checked. A `Task:` line with a milestone or
upstream ID (T-RC6, T-UP-1) and no label is not a proof task: nothing to check, exit 0. The label
without one proof-task ID, a malformed proof-task ID (T-DT4-P, T-DT4-P1-b) or two different ones
fail with exit 2.

The task (from `--task`, or the body's `Task: T-...-P<n>` line) is looked up in
docs/tasks/tasks.yaml for its file and declaration. The check fails unless:
- the task file is the only file changed;
- in that file, everything outside the declaration's proof is unchanged: the text before the
  declaration, its docstring, attributes and statement (up to the top-level `:=`), and the text
  after its block (which ends at the next line that starts a command at column 0, so new
  top-level lemmas count as a change);
- the statement matches the locked hash in tasks.yaml, when the task has one;
- the new proof contains no sorry, admit, native_decide, axiom, implemented_by or extern.
Helper lemmas belong inside the proof (`have`), or in a separate pull request without the
proof-task label. Exit 0 = pass or not a proof task, 1 = fail, 2 = usage error or a bad task ID."""
import argparse, hashlib, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import leansrc  # noqa: E402

TASKS = "docs/tasks/tasks.yaml"
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|axiom|implemented_by|extern)\b")
NEW_DECL = re.compile(r"^[ \t]*(@\[|(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|"
                      r"instance|example|axiom|opaque|structure|inductive|class|macro|syntax|"
                      r"elab|notation|irreducible_def)\b)", re.M)
TASK_LINE = re.compile(r"^\s*Task:\s*(T-[A-Za-z0-9-]+)", re.M)
PROOF_ID = re.compile(r"T-[A-Za-z0-9]+-P\d+")
# a third segment that starts with P: meant as a proof-task ID (T-PL5, a milestone, has none)
P_SEGMENT = re.compile(r"T-[A-Za-z0-9]+-[Pp]")


def statement_hash(header: str) -> str:
    """Hash of a declaration's statement (docstring through `:=`), ignoring whitespace."""
    return hashlib.sha256(" ".join(header.split()).encode()).hexdigest()[:16]


def git(*args, root=ROOT) -> str:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True).stdout


def show(ref: str, path: str, root=ROOT):
    r = subprocess.run(["git", "-C", str(root), "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def task_ids(body: str) -> list:
    """The IDs on the body's `Task:` lines, outside HTML comments (the template's examples)."""
    return TASK_LINE.findall(re.sub(r"<!--.*?-->", "", body, flags=re.S))


def task_from_body(body: str):
    """The body's one proof-task ID, or None (none, or two different ones)."""
    ids = {i for i in task_ids(body) if PROOF_ID.fullmatch(i)}
    return ids.pop() if len(ids) == 1 else None


def lookup(task_id: str, root=ROOT):
    import yaml
    data = yaml.safe_load((root / TASKS).read_text())
    for t in data.get("tasks", []):
        if t.get("id") == task_id:
            return t
    return None


def split_block(text: str, short: str):
    """(before, header, proof, after) of the declaration `short`, or None."""
    loc = leansrc.find_decl(text, short)
    if loc is None:
        return None
    lines = text.split("\n")
    s, e = loc
    block = "\n".join(lines[s:e])
    parts = leansrc.split_header(block)
    if parts is None:
        return None
    return "\n".join(lines[:s]), parts[0], parts[1], "\n".join(lines[e:])


def check(base: str, head: str, file: str, decl: str, lock=None, root=ROOT) -> list[str]:
    problems = []
    changed = [l for l in git("diff", "--name-only", f"{base}...{head}", root=root).splitlines() if l]
    others = [c for c in changed if c != file]
    if others:
        problems.append("files other than the task file changed: " + ", ".join(others))
    if file not in changed:
        problems.append(f"the task file {file} is unchanged")
    old, new = show(base, file, root), show(head, file, root)
    if old is None or new is None:
        return problems + [f"{file} is missing at the base or the head"]
    short = decl.split(".")[-1]
    a, b = split_block(old, short), split_block(new, short)
    if a is None:
        return problems + [f"declaration {short} not found exactly once in {file} at the base"]
    if b is None:
        return problems + [f"declaration {short} not found exactly once in {file} at the head"]
    if a[0] != b[0]:
        problems.append("the text before the declaration changed")
    if a[1] != b[1]:
        problems.append("the statement changed (docstring, attributes or the part before `:=`)")
    if a[3] != b[3]:
        problems.append("the text after the proof changed (new top-level declarations belong in a "
                        "separate pull request)")
    if lock and statement_hash(b[1]) != lock:
        problems.append(f"the statement does not match its locked hash {lock}")
    code = "".join(ch if c else " " for ch, c in zip(b[2], leansrc.code_mask(b[2])))
    m = FORBIDDEN.search(code)
    if m:
        problems.append(f"the proof still uses `{m.group(1)}`")
    if NEW_DECL.search(code):
        problems.append("the proof contains a new declaration or command (indented commands are "
                        "still top-level in Lean)")
    return problems


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", required=True)
    ap.add_argument("--head", required=True)
    ap.add_argument("--task")
    ap.add_argument("--body-file")
    ap.add_argument("--file")
    ap.add_argument("--decl")
    ap.add_argument("--proof-label", action="store_true", help="the pull request has the proof-task label")
    a = ap.parse_args(argv)
    lock = None
    if a.file and a.decl:
        file, decl, tid = a.file, a.decl, a.task or "(no task ID)"
    else:
        tid = a.task
        if not tid:
            if not a.body_file:
                print("proof-task check: give --task, --body-file, or --file and --decl")
                return 2
            body = pathlib.Path(a.body_file).read_text()
            ids = task_ids(body)
            bad = [i for i in ids if P_SEGMENT.match(i) and not PROOF_ID.fullmatch(i)]
            if bad:
                print(f"proof-task check: malformed proof-task ID {bad[0]} (the form is T-<task>-P<n>, "
                      "such as T-DT4-P1)")
                return 2
            if not a.proof_label and not any(PROOF_ID.fullmatch(i) for i in ids):
                print(f"not a proof task: {ids[0]}, nothing to check" if ids else
                      "not a proof task: no Task line and no proof-task label, nothing to check")
                return 0
            tid = task_from_body(body)
            if not tid:
                print("proof-task check: no task ID (the proof-task label or a proof-task ID needs one "
                      "line `Task: T-...-P<n>` in the body"
                      + (f"; found {', '.join(dict.fromkeys(ids))})" if ids else ")"))
                return 2
        t = lookup(tid)
        if t is None or t.get("kind") != "proof" or not t.get("file"):
            print(f"proof-task check: {tid} is not a proof task with a task file in {TASKS}")
            return 2
        file, decl, lock = t["file"], t["decl"], t.get("lock")
    problems = check(a.base, a.head, file, decl, lock)
    if problems:
        print(f"proof-task check FAILED for {tid} ({file}, {decl}):")
        for p in problems:
            print("  - " + p)
        return 1
    print(f"proof-task check OK for {tid}: only the proof of {decl} in {file} changed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
