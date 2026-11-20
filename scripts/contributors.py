#!/usr/bin/env python3
"""The contributors list and the weekly leaderboard, written into one pinned issue.

Actions cannot push to `main`, so the list lives in an issue: the one whose body has the marker
`<!-- lightlike-contributors -->` (created once, with the label `leaderboard`, when none exists). This script reads the
merged pull requests through the API and rewrites the body of that issue; it never touches any other issue.
The maintainers pin the issue once.

  * Contributors: every account with at least one merged pull request, with the number of merged pull requests and
    of proof tasks (a pull request with the line `Task: T-...-P<n>`).
  * Leaderboard: proof tasks merged per account in the last 7 days.

    python3 scripts/contributors.py --repo OWNER/REPO [--apply]      print the body; --apply writes the issue
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import subprocess
import sys

MARK = "<!-- lightlike-contributors -->"
TITLE = "Contributors and weekly leaderboard"
LABEL = "leaderboard"
TASK = re.compile(r"^\s*Task:\s*(T-[A-Za-z0-9]+(?:-[A-Za-z0-9]+)?)\s*$", re.M)
PROOF = re.compile(r"-P\d+$")
BOTS = ("[bot]",)


def proof_tasks(body):
    """The proof task IDs named by the `Task:` lines of a pull request body (comments left out)."""
    text = re.sub(r"<!--.*?-->", "", body or "", flags=re.S)
    return sorted({t for t in TASK.findall(text) if PROOF.search(t)})


def tally(prs, now, days=7):
    """(rows, week): `prs`: merged pull requests (author login, mergedAt, body). rows: [(login, merged, proof tasks)]
    for all time, by proof tasks and then merged pull requests; week: [(login, proof tasks)] of the last `days`."""
    allt, week = {}, {}
    cutoff = now - datetime.timedelta(days=days)
    for p in prs:
        a = p.get("author") or ""
        if not a or a.endswith(BOTS) or not p.get("mergedAt"):
            continue
        n = len(proof_tasks(p.get("body")))
        m, t = allt.get(a, (0, 0))
        allt[a] = (m + 1, t + n)
        when = datetime.datetime.fromisoformat(p["mergedAt"].replace("Z", "+00:00"))
        if when >= cutoff and n:
            week[a] = week.get(a, 0) + n
    rows = sorted(((a, m, t) for a, (m, t) in allt.items()), key=lambda r: (-r[2], -r[1], r[0].lower()))
    return rows, sorted(week.items(), key=lambda kv: (-kv[1], kv[0].lower()))


def render(rows, week, now):
    lines = [MARK, "", "Rewritten every week by `.github/workflows/contributors.yml`; do not edit it by hand.",
             f"Updated {now.strftime('%Y-%m-%d')} (UTC).", "", "## Leaderboard: proof tasks merged in the last 7 days", ""]
    lines += (["| Rank | Account | Proof tasks |", "|---|---|---|"] + [f"| {i} | @{a} | {n} |" for i, (a, n) in
                                                                      enumerate(week, 1)]) if week else ["No proof task merged this week."]
    lines += ["", "## Contributors", "", "Every account with a merged pull request.", "",
              "| Account | Merged pull requests | Proof tasks |", "|---|---|---|"]
    lines += [f"| @{a} | {m} | {t} |" for a, m, t in rows]
    return "\n".join(lines) + "\n"


def gh(args, fatal=True):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode:
        if fatal:
            sys.exit(f"contributors: gh {' '.join(args[:3])} failed: {r.stderr.strip()[:300]}")
        return None
    return r.stdout


def find_issue(issues):
    """The number of the issue with the marker in its body, or None."""
    for i in sorted(issues, key=lambda i: i["number"]):
        if MARK in (i.get("body") or ""):
            return i["number"]
    return None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--repo", required=True)
    ap.add_argument("--apply", action="store_true")
    a = ap.parse_args(argv)
    prs = json.loads(gh(["pr", "list", "--repo", a.repo, "--state", "merged", "--limit", "5000", "--json",
                         "author,mergedAt,body"]) or "[]")
    prs = [{"author": (p.get("author") or {}).get("login", ""), "mergedAt": p.get("mergedAt"), "body": p.get("body")}
           for p in prs]
    now = datetime.datetime.now(datetime.timezone.utc)
    body = render(*tally(prs, now), now)
    if not a.apply:
        print(body)
        return 0
    issues = json.loads(gh(["issue", "list", "--repo", a.repo, "--label", LABEL, "--state", "all", "--limit", "20",
                            "--json", "number,body"]) or "[]")
    num = find_issue(issues)
    if num is None:
        gh(["label", "create", LABEL, "--repo", a.repo, "--color", "0e8a16", "--description",
            "The contributors list and weekly leaderboard"], fatal=False)
        gh(["issue", "create", "--repo", a.repo, "--title", TITLE, "--label", LABEL, "--body", body])
        print("contributors: issue created")
    else:
        gh(["issue", "edit", str(num), "--repo", a.repo, "--body", body])
        print("contributors: issue updated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
