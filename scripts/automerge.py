#!/usr/bin/env python3
"""Decide whether a pull request is a proof-task pull request that may merge by itself, and set the
label `automerge` and GitHub's auto-merge to match.

A pull request is eligible exactly when
  * it is open, targets `main` and is not a draft;
  * its body names one task (a line `Task: T-...`, outside HTML comments) and that task is a proof task;
  * the files it changes, read from the GitHub API, are exactly the task's own file, modified (not added,
    renamed or removed).
Eligible: add the label `automerge` and run `gh pr merge --auto --squash` (the pull request enters the merge
queue once the required checks pass). Not eligible while it carries the label: remove the label and disable
auto-merge, so that a changed file list stops the merge. Any other pull request is left alone.

This runs from the `pull_request_target` workflow (.github/workflows/automerge.yml) as it is on `main`; it
never checks out or runs the code of a pull request: the body and the file list are data read through the
API and are never put into a shell command.

    python3 scripts/automerge.py --repo OWNER/REPO --pr N [--apply]     print the decision; --apply acts
    python3 scripts/automerge.py --selftest-data FILE.json              decide on a fixture (no GitHub)
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LABEL = "automerge"
TASK_LINE = re.compile(r"^\s*Task:\s*(T-[A-Za-z0-9]+(?:-[A-Za-z0-9]+)?)\s*$", re.M)
ANY_TASK_LINE = re.compile(r"^\s*Task:", re.M)


def task_ids(body):
    """The task IDs named by the `Task:` lines of a pull request body, comments left out."""
    text = re.sub(r"<!--.*?-->", "", body or "", flags=re.S)
    return sorted(set(TASK_LINE.findall(text))), len(ANY_TASK_LINE.findall(text))


def decide(pr, files, proof_files):
    """(eligible, reason). `pr`: the API object of the pull request (state, draft, base.ref, body);
    `files`: the API list of its changed files (filename, status); `proof_files`: {task id: file} of the
    proof tasks of `main`."""
    if pr.get("state") != "open":
        return False, "not open"
    if pr.get("draft"):
        return False, "draft"
    if (pr.get("base") or {}).get("ref") != "main":
        return False, "does not target main"
    ids, lines = task_ids(pr.get("body"))
    if len(ids) != 1 or lines != 1:
        return False, "the body must have exactly one `Task: T-...` line"
    tid = ids[0]
    if tid not in proof_files:
        return False, f"{tid} is not a proof task"
    names = [f.get("filename") for f in files]
    if names != [proof_files[tid]] or any(f.get("status") != "modified" for f in files):
        return False, f"the changed files are not exactly {proof_files[tid]}, modified"
    return True, f"proof task {tid}: only {proof_files[tid]} changed"


def proof_files(root=ROOT):
    """{task id: file} of the proof tasks in docs/tasks/tasks.yaml of the checkout (`main`)."""
    import yaml
    data = yaml.safe_load((root / "docs/tasks/tasks.yaml").read_text())
    return {t["id"]: t["file"] for t in data["tasks"] if t["kind"] == "proof" and t.get("file")}


def plan(eligible, labels):
    """The `gh` steps for a decision: a list of ('label'|'unlabel'|'auto'|'noauto')."""
    has = LABEL in labels
    if eligible:
        return ([] if has else ["label"]) + ["auto"]
    return ["unlabel", "noauto"] if has else []


def gh(args, stdin=None):
    r = subprocess.run(["gh", *args], capture_output=True, text=True, input=stdin)
    if r.returncode:
        sys.exit(f"automerge: gh {' '.join(args[:3])} failed: {r.stderr.strip()[:300]}")
    return r.stdout


def fetch(repo, n):
    pr = json.loads(gh(["api", f"repos/{repo}/pulls/{n}"]))
    files = json.loads(gh(["api", "--paginate", "--slurp", f"repos/{repo}/pulls/{n}/files?per_page=100"]))
    return pr, [f for page in files for f in page]


def apply(repo, n, steps):
    for s in steps:
        if s == "label":
            gh(["api", f"repos/{repo}/issues/{n}/labels", "-X", "POST", "-f", f"labels[]={LABEL}"])
        elif s == "unlabel":
            gh(["api", f"repos/{repo}/issues/{n}/labels/{LABEL}", "-X", "DELETE"])
        elif s == "auto":
            gh(["pr", "merge", str(n), "--repo", repo, "--auto", "--squash"])
        elif s == "noauto":
            gh(["pr", "merge", str(n), "--repo", repo, "--disable-auto"])


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--repo")
    ap.add_argument("--pr", type=int)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--selftest-data")
    a = ap.parse_args(argv)
    if a.selftest_data:
        d = json.loads(pathlib.Path(a.selftest_data).read_text())
        ok, why = decide(d["pr"], d["files"], d["proof_files"])
        print(json.dumps({"eligible": ok, "reason": why, "steps": plan(ok, [x["name"] for x in d["pr"].get("labels", [])])}))
        return 0
    if not a.repo or not a.pr:
        ap.error("--repo and --pr are required")
    pr, files = fetch(a.repo, a.pr)
    ok, why = decide(pr, files, proof_files())
    steps = plan(ok, [x["name"] for x in pr.get("labels", [])])
    print(f"automerge: #{a.pr}: {'eligible' if ok else 'not eligible'}: {why}; steps: {steps or 'none'}")
    if a.apply:
        apply(a.repo, a.pr, steps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
