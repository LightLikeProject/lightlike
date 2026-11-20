#!/usr/bin/env python3
"""The required check `review-gate` (a commit status), and the label `needs-review`.

`needs-review` goes on every pull request that is not an auto-merge proof-task pull request (scripts/automerge.py)
and adds, changes or removes a `.lean` file under `Lightlike/` or `Tasks/`: a statement can change on any line of
a signature, so the rule is the file, and a proof-only library pull request is over-flagged on purpose.

The status `review-gate` on the pull request's head commit is
  * success, with no review needed, for a pull request without the label's trigger (no such Lean file changes);
  * success for an auto-merge proof-task pull request, and for one whose author administers the repository;
  * otherwise success only with at least 2 APPROVED reviews of the current head commit from 2 distinct accounts
    other than the author, each with at least one merged pull request in this repository; pending until then.
GitHub's own required reviews count only reviewers with write access; this status counts outside reviewers who
have contributed. It never merges anything: a maintainer merges a pull request that needs review.

A status is posted through the API on the head commit, so that it satisfies a required status check whatever
event computed it. It is posted from runs of `main`'s code only (.github/workflows/review-gate.yml: pull_request_target
and workflow_run); the pull request is data read through the API, never checked out.

    python3 scripts/review_gate.py --repo OWNER/REPO --pr N [--labels] [--post-status]
    python3 scripts/review_gate.py --repo OWNER/REPO --head-sha SHA --post-status      (find the pull request by its head)
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import automerge  # noqa: E402

LABEL = "needs-review"
CONTEXT = "review-gate"
NEED = 2
WATCHED = ("Lightlike/", "Tasks/")


def needs_review(files):
    """True when the changed `files` (API objects: filename, status) add, change or remove a `.lean` file under
    `Lightlike/` or `Tasks/`."""
    return any((f.get("filename") or "").endswith(".lean") and (f.get("filename") or "").startswith(WATCHED)
               for f in files) or any((f.get("previous_filename") or "").endswith(".lean")
                                      and (f.get("previous_filename") or "").startswith(WATCHED) for f in files)


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
    """(state, reason): state is "success" or "pending". `is_admin(login)`: whether the account administers the
    repository; `merged(login)`: the number of merged pull requests of the account in the repository."""
    if automerge.decide(pr, files, proof_files)[0]:
        return "success", "an auto-merge proof-task pull request"
    if not needs_review(files):
        return "success", "no Lean file of Lightlike/ or Tasks/ changes; no review needed"
    author = (pr.get("user") or {}).get("login")
    if author and is_admin(author):
        return "success", f"the author {author} administers the repository"
    head = (pr.get("head") or {}).get("sha")
    got = approvals(reviews, head, author)
    ok = [u for u in got if merged(u) >= 1]
    if len(ok) >= NEED:
        return "success", f"approved by {', '.join(ok[:NEED])}"
    return "pending", (f"needs {NEED} approvals of this commit from accounts other than the author, each with a merged "
                       f"pull request here; has {len(ok)}")


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
    ap.add_argument("--repo", required=True)
    ap.add_argument("--pr", type=int, default=0)
    ap.add_argument("--head-sha", default="")
    ap.add_argument("--labels", action="store_true", help="also add or remove the label needs-review")
    ap.add_argument("--post-status", action="store_true", help="post the commit status review-gate on the head")
    a = ap.parse_args(argv)
    flat = lambda pages: [x for p in pages for x in (p if isinstance(p, list) else [p])]  # noqa: E731
    api = lambda path: flat(json.loads(gh(["api", "--paginate", "--slurp", path])))  # noqa: E731
    if not a.pr:
        if not a.head_sha:
            ap.error("--pr or --head-sha is required")
        cands = [p for p in api(f"repos/{a.repo}/commits/{a.head_sha}/pulls?per_page=100")
                 if p.get("state") == "open" and (p.get("head") or {}).get("sha") == a.head_sha
                 and (p.get("base") or {}).get("ref") == "main"]
        if not cands:
            print(f"review-gate: no open pull request for {a.head_sha}; nothing to do")
            return 0
        a.pr = cands[0]["number"]
    pr = json.loads(gh(["api", f"repos/{a.repo}/pulls/{a.pr}"]))
    files = api(f"repos/{a.repo}/pulls/{a.pr}/files?per_page=100")
    reviews = api(f"repos/{a.repo}/pulls/{a.pr}/reviews?per_page=100")
    pf = automerge.proof_files()

    def is_admin(login):
        out = gh(["api", f"repos/{a.repo}/collaborators/{login}/permission", "--jq", ".role_name"], fatal=False)
        return (out or "").strip() == "admin"

    def merged(login):
        out = gh(["api", "search/issues", "-X", "GET", "-f", f"q=repo:{a.repo} is:pr is:merged author:{login}",
                  "-f", "per_page=1", "--jq", ".total_count"], fatal=False)
        return int((out or "0").strip() or 0)

    state, why = evaluate(pr, files, reviews, is_admin, merged, pf)
    print(f"review-gate: #{a.pr}: {state}: {why}")
    if a.labels:
        steps = label_plan(pr, files, pf, [x["name"] for x in pr.get("labels", [])])
        for st in steps:
            if st == "label":
                gh(["api", f"repos/{a.repo}/labels", "-X", "POST", "-f", f"name={LABEL}", "-f", "color=d93f0b",
                    "-f", "description=A Lean file under Lightlike/ or Tasks/ changes; needs two reviews"], fatal=False)
                gh(["api", f"repos/{a.repo}/issues/{a.pr}/labels", "-X", "POST", "-f", f"labels[]={LABEL}"])
            else:
                gh(["api", f"repos/{a.repo}/issues/{a.pr}/labels/{LABEL}", "-X", "DELETE"])
        print(f"review-gate: label {LABEL}: {steps or 'unchanged'}")
    if a.post_status:
        sha = (pr.get("head") or {}).get("sha")
        gh(["api", f"repos/{a.repo}/statuses/{sha}", "-X", "POST", "-f", f"state={state}", "-f", f"context={CONTEXT}",
            "-f", f"description={why[:140]}"])
        print(f"review-gate: status {CONTEXT} {state} posted on {sha[:10]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
