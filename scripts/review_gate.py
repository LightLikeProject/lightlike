#!/usr/bin/env python3
"""The check `review-gate` (a commit status). It always passes: pull requests carry no review label, and a pull
request merges when its gates and checks pass.

Reviews are of milestones, not of pull requests: a milestone whose items are all ticked is reviewed by an agent
session other than the one that did the work (CONTRIBUTING.md, "Reviews"). An expert's review is optional: a
catalogue entry counts as reviewed by a person once an expert's review issue is linked to it, and nothing waits for
that.

The check name stays because the repository's ruleset requires it. A status is posted through the API on the head
commit, so that it satisfies the required check whatever event computed it. It is posted from runs of `main`'s code
only (.github/workflows/review-gate.yml: pull_request_target); the pull request is data read through the API, never
checked out. With --labels, the label `needs-review`, which an earlier version of this check set, is removed from
the pull request where it is still present; nothing adds it.

    python3 scripts/review_gate.py --repo OWNER/REPO --pr N [--labels] [--post-status]
    python3 scripts/review_gate.py --repo OWNER/REPO --head-sha SHA --post-status      (find the pull request by its head)
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys

OLD_LABEL = "needs-review"
CONTEXT = "review-gate"
REASON = "no review label: a pull request merges when its gates and checks pass"


def evaluate(pr, files):
    """(state, reason) for the pull request `pr` with the changed `files`: always success."""
    return "success", REASON


def label_plan(labels):
    """['unlabel'] when the old label `needs-review` is on the pull request, else []. Nothing adds it."""
    return ["unlabel"] if OLD_LABEL in labels else []


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
    ap.add_argument("--labels", action="store_true", help="remove the old label needs-review where it is present")
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
    state, why = evaluate(pr, [])
    print(f"review-gate: #{a.pr}: {state}: {why}")
    if a.labels:
        steps = label_plan([x["name"] for x in pr.get("labels", [])])
        for _ in steps:
            gh(["api", f"repos/{a.repo}/issues/{a.pr}/labels/{OLD_LABEL}", "-X", "DELETE"], fatal=False)
        print(f"review-gate: label {OLD_LABEL}: {steps or 'unchanged'}")
    if a.post_status:
        sha = (pr.get("head") or {}).get("sha")
        gh(["api", f"repos/{a.repo}/statuses/{sha}", "-X", "POST", "-f", f"state={state}", "-f", f"context={CONTEXT}",
            "-f", f"description={why[:140]}"])
        print(f"review-gate: status {CONTEXT} {state} posted on {sha[:10]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
