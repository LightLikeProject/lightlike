#!/usr/bin/env python3
"""The required check `review-gate`, and the label `needs-review`.

A pull request passes the gate in three cases:
  1. it is an auto-merge proof-task pull request (scripts/automerge.py: its only changed file is its own
     task file);
  2. its author is an administrator of the repository (the batch pull requests of the maintainers);
  3. otherwise: at least 2 APPROVED reviews of the current head commit from 2 distinct accounts other than the
     author, each with at least one merged pull request in this repository.
GitHub's own required reviews count only reviewers with write access; this check exists to count
outside reviewers who have contributed. It never merges anything. On a merge-queue run it passes (the pull
request passed it to enter the queue).

The label `needs-review` goes on every pull request that is not an auto-merge proof-task pull request and
changes Lean statements or definitions: a changed or added line that starts a declaration (theorem, lemma,
def, structure, ...) in a `.lean` file, a new `.lean` file, or a diff GitHub does not show. The review
rubric is docs/review-rubric.md.

It runs from .github/workflows/review-gate.yml with the checkout of `main`, never the pull request's code;
the pull request is data read through the API.

    python3 scripts/review_gate.py --repo OWNER/REPO --pr N [--labels]   evaluate; --labels sets the label
    python3 scripts/review_gate.py --event merge_group                    pass
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import automerge  # noqa: E402

LABEL = "needs-review"
NEED = 2
DECL = re.compile(r"^[+-]\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom|opaque|example|"
                  r"notation|macro|syntax)\b")


def needs_review(files):
    """True when the changed `files` (API objects: filename, status, patch) change Lean statements or definitions."""
    for f in files:
        name = f.get("filename") or ""
        if not name.endswith(".lean"):
            continue
        if f.get("status") in ("added", "renamed", "removed"):
            return True
        patch = f.get("patch")
        if patch is None:  # a diff GitHub does not show is a large one
            return True
        if any(DECL.match(line) for line in patch.splitlines() if not line.startswith(("+++", "---"))):
            return True
    return False


def approvals(reviews, head_sha, author):
    """The accounts whose latest review of the head commit approves it (author, bots and comments excluded)."""
    latest = {}
    for r in sorted(reviews, key=lambda r: r.get("submitted_at") or ""):
        user = (r.get("user") or {})
        login = user.get("login")
        if not login or user.get("type") == "Bot" or login == author:
            continue
        if r.get("state") in ("COMMENTED", "PENDING"):
            continue
        latest[login] = r
    return sorted(u for u, r in latest.items() if r.get("state") == "APPROVED" and r.get("commit_id") == head_sha)


def evaluate(pr, files, reviews, is_admin, merged, proof_files):
    """(passes, reason). `is_admin(login)`: whether the account administers the repository; `merged(login)`:
    the number of merged pull requests of the account in the repository."""
    if automerge.decide(pr, files, proof_files)[0]:
        return True, "an auto-merge proof-task pull request"
    author = (pr.get("user") or {}).get("login")
    if author and is_admin(author):
        return True, f"the author {author} administers the repository"
    head = (pr.get("head") or {}).get("sha")
    got = approvals(reviews, head, author)
    ok = [u for u in got if merged(u) >= 1]
    if len(ok) >= NEED:
        return True, f"approved by {', '.join(ok[:NEED])}"
    return False, (f"needs {NEED} approvals of the current commit from distinct accounts other than the author, each "
                   f"with a merged pull request here; has {len(ok)} ({len(got)} approvals, of which {len(got) - len(ok)} "
                   "from accounts without a merged pull request)")


def label_plan(pr, files, proof_files, labels):
    """['label'] or ['unlabel'] or []: what to do about `needs-review`."""
    want = (not automerge.decide(pr, files, proof_files)[0]) and needs_review(files)
    has = LABEL in labels
    return ["label"] if want and not has else ["unlabel"] if has and not want else []


def gh(args, fatal=True):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode:
        if fatal:
            sys.exit(f"review-gate: gh {' '.join(args[:3])} failed: {r.stderr.strip()[:300]}")
        return None
    return r.stdout


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--repo")
    ap.add_argument("--pr", type=int)
    ap.add_argument("--event", default="")
    ap.add_argument("--labels", action="store_true", help="also add or remove the label needs-review")
    a = ap.parse_args(argv)
    if a.event == "merge_group":
        print("review-gate: passes on a merge-queue run (the pull request passed it to enter the queue)")
        return 0
    if not a.repo or not a.pr:
        ap.error("--repo and --pr are required")
    api = lambda path: json.loads(gh(["api", "--paginate", "--slurp", path]))  # noqa: E731
    flat = lambda pages: [x for p in pages for x in (p if isinstance(p, list) else [p])]  # noqa: E731
    pr = json.loads(gh(["api", f"repos/{a.repo}/pulls/{a.pr}"]))
    files = flat(api(f"repos/{a.repo}/pulls/{a.pr}/files?per_page=100"))
    reviews = flat(api(f"repos/{a.repo}/pulls/{a.pr}/reviews?per_page=100"))
    pf = automerge.proof_files()

    def is_admin(login):
        out = gh(["api", f"repos/{a.repo}/collaborators/{login}/permission", "--jq", ".role_name"], fatal=False)
        return (out or "").strip() == "admin"

    def merged(login):
        out = gh(["api", "search/issues", "-X", "GET", "-f", f"q=repo:{a.repo} is:pr is:merged author:{login}",
                  "-f", "per_page=1", "--jq", ".total_count"], fatal=False)
        return int((out or "0").strip() or 0)

    ok, why = evaluate(pr, files, reviews, is_admin, merged, pf)
    print(f"review-gate: #{a.pr}: {'passes' if ok else 'fails'}: {why}")
    if a.labels:
        steps = label_plan(pr, files, pf, [x["name"] for x in pr.get("labels", [])])
        for s in steps:
            if s == "label":
                gh(["api", f"repos/{a.repo}/labels", "-X", "POST", "-f", f"name={LABEL}", "-f", "color=d93f0b",
                    "-f", "description=A Lean statement or definition changes; needs two reviews"], fatal=False)
                gh(["api", f"repos/{a.repo}/issues/{a.pr}/labels", "-X", "POST", "-f", f"labels[]={LABEL}"])
            else:
                gh(["api", f"repos/{a.repo}/issues/{a.pr}/labels/{LABEL}", "-X", "DELETE"])
        print(f"review-gate: label {LABEL}: {steps or 'unchanged'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
