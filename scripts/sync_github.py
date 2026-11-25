#!/usr/bin/env python3
"""Bring the milestone issues and the Project board in line with the computed status.

Status is computed, never typed. This script reads
the status that scripts/milestone_status.py computed (OUT/status.json) and the live issues, and for
every milestone of docs/tasks/milestones.md:

  - finds its issue: the number in docs/tasks/checklists.yaml; else the lowest-numbered issue
    titled `T-<ID>: ...` that is not closed as not planned or as a duplicate; else it opens one,
    and writes its number into checklists.yaml at once, so a second run never opens a second issue;
  - writes its title and its body (the body only when more than its first, generated-by line
    changed);
  - writes the labels of its own families: the plan labels (milestone, area, size, difficulty,
    upstream), not-scheduled and help-wanted for the milestones outside v1.0, and one status label
    for a v1.0 milestone (status: ready, status: in-progress, status: review, status: done). It
    removes the old status labels ready, blocked and in review from milestone issues;
  - puts each v1.0 milestone in the GitHub Milestone "v1.0", and takes the others out of it;
  - sets its column on the Project board: Ready, In progress, In review, Done or Not scheduled,
    and, for an open v1.0 milestone, the board's number field Rank to its `ranking:`.

It never closes or reopens an issue (the merger closes a milestone's issue after a passing review),
never touches a proof-task issue, and never writes the claim labels claimed and attempting: the
claim Action (scripts/tasks.py sync, .github/workflows/tasks.yml) writes those from comments. This
script reads them, to show an outside contributor's claim.

The status of a v1.0 milestone: done when its issue is closed; review when every item of its
checklist but the review items is ticked (the review ticks those); in-progress when a stream (status
file at most a day old) or an outside contributor (claim label) holds it; ready otherwise. A milestone outside v1.0 is in the column Not
scheduled until its issue is closed, then in Done.

Usage, from the repository root:

    python3 scripts/sync_github.py plan --status OUT/status.json [--only ID,ID] [--fixture F.json]
        print what would change; nothing is written (reads GitHub unless --fixture)
    python3 scripts/sync_github.py apply --status OUT/status.json --stop-file PATH [--only ID,ID]
                                         [--per-10min N] [--board-per-10min N]
        make the changes. Paced: at most N (default 20) issue creations, issue edits and label
        creations per 10 minutes, and at most 60 board changes per 10 minutes. Before every write
        it stops if PATH exists (the kill switch). It stops at once on any gh error, on a warning
        and on a rate limit, and says what was done.
    python3 scripts/sync_github.py adopt [--fixture F.json]
        write into checklists.yaml the issue number of every milestone that already has an issue
        (no GitHub write)
    python3 scripts/sync_github.py --selftest
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import milestone_status as MS  # noqa: E402
import tasks as T  # noqa: E402

V1_MILESTONE = "v1.0"
STATUS = {"ready": "Ready", "in-progress": "In progress", "review": "In review", "done": "Done"}
COLUMNS = [*STATUS.values(), "Not scheduled"]
NOT_SCHEDULED, HELP_WANTED = "not-scheduled", "help-wanted"
CLAIM_LABELS = {"claimed", "attempting"}  # the claim Action's; never written here
OLD_STATUS = {"ready", "blocked", "in review"}  # the claim Action set these on milestone issues before 25 Nov
TIERS = {"good first issue", "intermediate", "advanced", "research-level"}
WARN = re.compile(r"rate limit|secondary|abuse|warning|error|forbidden", re.I)
MIN_REMAINING = 300  # stop before starting when fewer API calls than this remain


class Stop(Exception):
    pass


def ours(label):
    """Whether `label` belongs to a family this script writes on milestone issues."""
    return (label.startswith(("area: ", "size: ", "status: ", "upstream: "))
            or label in {"milestone", "upstream", NOT_SCHEDULED, HELP_WANTED} | TIERS | OLD_STATUS)


# --- Reading -------------------------------------------------------------------------------------

def gh(args, check=True):
    """Run gh: (stdout, stderr). With check, a failure, a warning or a rate limit raises Stop."""
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if check and (r.returncode or WARN.search(r.stderr or "")):
        raise Stop(f"gh {' '.join(args[:3])}: exit {r.returncode}: {(r.stderr or r.stdout).strip()[:300]}")
    return r.stdout, r.stderr


def gh_json(args):
    out, _ = gh(args)
    return json.loads(out) if out.strip() else None


def live(conf):
    """The issues, labels, GitHub Milestones and Project board of the repository, as a fixture."""
    repo, org, board = conf["repo"], conf.get("org") or conf["repo"].split("/")[0], conf.get("project") or {}
    iss = gh_json(["issue", "list", "--repo", repo, "--state", "all", "--limit", "5000", "--json",
                   "number,title,state,stateReason,labels,assignees,milestone,body,url"]) or []
    labels = gh_json(["label", "list", "--repo", repo, "--limit", "1000", "--json", "name"]) or []
    gms = gh_json(["api", f"repos/{repo}/milestones?state=all&per_page=100"]) or []
    data = dict(issues=[dict(number=i["number"], title=i["title"], state=i["state"].lower(),
                             reason=(i.get("stateReason") or "").lower(), labels=[x["name"] for x in i["labels"]],
                             assignees=[x["login"] for x in i["assignees"]],
                             milestone=(i.get("milestone") or {}).get("title"), body=i.get("body") or "",
                             url=i.get("url")) for i in iss],
                labels=[x["name"] for x in labels], milestones=[m["title"] for m in gms], board=None)
    projs = (gh_json(["project", "list", "--owner", org, "--format", "json", "--limit", "100"]) or {}).get("projects") or []
    p = next((x for x in projs if x.get("title") == board.get("title", "Lightlike")), None)
    if p:
        fields = (gh_json(["project", "field-list", str(p["number"]), "--owner", org, "--format", "json",
                           "--limit", "100"]) or {}).get("fields") or []
        fname, rname = board.get("field", "Status"), board.get("rank_field", "Rank")
        f = next((x for x in fields if x.get("name") == fname), None)
        r = next((x for x in fields if x.get("name") == rname), None)
        items = (gh_json(["project", "item-list", str(p["number"]), "--owner", org, "--format", "json",
                          "--limit", "5000"]) or {}).get("items") or []
        data["board"] = dict(
            id=p["id"], number=p["number"], field_id=(f or {}).get("id"), rank_id=(r or {}).get("id"),
            options={o["name"]: o["id"] for o in (f or {}).get("options") or []},
            items={str(x["content"]["number"]): dict(id=x["id"], column=x.get(fname.lower(), x.get(fname)),
                                                     rank=x.get(rname.lower(), x.get(rname)))
                   for x in items if (x.get("content") or {}).get("number")
                   and (x["content"].get("repository") or repo) == repo})
    return data


def same_rank(a, b):
    """Whether two board ranks are equal (the board gives numbers as floats, and none as absent)."""
    if a is None or b is None:
        return a is None and b is None
    try:
        return float(a) == float(b)
    except (TypeError, ValueError):
        return False


def remaining():
    out, _ = gh(["api", "rate_limit", "--jq", "[.resources.core.remaining, .resources.graphql.remaining]"])
    return min(json.loads(out))


# --- The plan ------------------------------------------------------------------------------------

def status_of(st, iss, outside):
    if iss and iss["state"] == "closed":
        return "done"
    if not st["v1"]:
        return None
    if st["done"]:
        return "review"
    if st["claimed_by"] or outside:
        return "in-progress"
    return "ready"


def find_issues(ms_tasks, data, stored):
    """({milestone: issue}, problems): the stored number first, else the lowest-numbered `T-<ID>:` issue."""
    by_num = {i["number"]: i for i in data["issues"]}
    titled = T.task_issues(ms_tasks, data["issues"])
    out, probs = {}, []
    for t in ms_tasks:
        mid, num = t["milestone"], stored.get(t["milestone"])
        if num is not None:
            i = by_num.get(num)
            m = T.ISSUE_TITLE.match(i["title"]) if i else None
            if not i or not m or m.group(1) != t["id"]:
                probs.append(f"{mid}: the issue #{num} of checklists.yaml is not a `{t['id']}:` issue")
                continue
            out[mid] = i
        elif t["id"] in titled:
            out[mid] = titled[t["id"]]
    return out, probs


def strip_mark(text):
    lines = (text or "").replace("\r\n", "\n").strip().split("\n")
    return "\n".join(lines[1:] if lines and lines[0].startswith(MS.MARK) else lines).strip()


def plan(status, tasks, data, stored, spec, only=None):
    """(actions, problems). `status`: status.json; `tasks`: of tasks.build; `data`: live() or a
    fixture; `stored`: {milestone: issue number} of checklists.yaml; `spec`: label colours of
    board.yaml."""
    ms_tasks = [t for t in tasks if t["kind"] == "milestone" and t["milestone"] in status["milestones"]]
    proofs = [t for t in tasks if t["kind"] == "proof"]
    issues, probs = find_issues(ms_tasks, data, stored)
    issue_of = {tid: i["number"] for tid, i in T.task_issues(proofs, data["issues"]).items()}
    board = data.get("board")
    if V1_MILESTONE not in (data.get("milestones") or []):
        probs.append(f'the GitHub Milestone "{V1_MILESTONE}" does not exist')
    if not board:
        probs.append("the Project board does not exist")
    else:
        missing = [c for c in COLUMNS if c not in board["options"]]
        if not board.get("field_id") or missing:
            probs.append("the board's Status field lacks the columns " + ", ".join(missing or ["(no field)"]))
        if not board.get("rank_id"):
            probs.append("the board has no number field Rank (the ranking of the v1.0 milestones)")
    sha, date = status["main"], (status.get("computed_at") or "")[:10]
    acts, need = [], set()
    for t in ms_tasks:
        mid = t["milestone"]
        if only and mid not in only:
            continue
        st, iss = status["milestones"][mid], issues.get(mid)
        outside = [u for u in (iss or {}).get("assignees") or []] if "claimed" in (iss or {}).get("labels", []) else []
        s = status_of(st, iss, outside)
        want = list(t["labels"]) + ([f"status: {s}"] if st["v1"] and s else []) + (
            [] if st["v1"] else [NOT_SCHEDULED] + ([HELP_WANTED] if s != "done" else []))
        need |= set(want)
        title = T.short_title(f"{t['id']}: {st['title']}")
        body = MS.body(st, sha, date, outside, issue_of)
        column = STATUS[s] if s == "done" or (st["v1"] and s) else "Not scheduled"
        # The ranking orders the open v1.0 milestones on the board (what is next); done ones lose it.
        rank = st.get("ranking") if st["v1"] and s != "done" else None
        if iss is None:
            acts.append(dict(op="create", mid=mid, title=title, body=body, labels=want,
                             milestone=V1_MILESTONE if st["v1"] else None, column=column, rank=rank))
            continue
        e = dict(op="edit", mid=mid, issue=iss["number"], title=None, body=None,
                 add=[x for x in want if x not in iss["labels"]],
                 remove=[x for x in iss["labels"] if ours(x) and x not in want], milestone=None)
        if iss["title"].strip() != title:
            e["title"] = title
        if strip_mark(iss.get("body")) != strip_mark(body):
            e["body"] = body
        if st["v1"] and iss.get("milestone") != V1_MILESTONE:
            e["milestone"] = V1_MILESTONE
        elif not st["v1"] and iss.get("milestone") == V1_MILESTONE:
            e["milestone"] = ""
        if e["title"] or e["body"] or e["add"] or e["remove"] or e["milestone"] is not None:
            acts.append(e)
        item = (board or {}).get("items", {}).get(str(iss["number"]))
        if not item or item.get("column") != column or not same_rank(item.get("rank"), rank):
            acts.append(dict(op="board", mid=mid, issue=iss["number"], url=iss.get("url"),
                             item=(item or {}).get("id"), column=column, rank=rank,
                             set_column=not item or item.get("column") != column,
                             had_rank=(item or {}).get("rank") is not None))
    have = set(data.get("labels") or [])
    labels = [dict(op="label", name=n, color=c, description=d) for n in sorted(need - have)
              for c, d in [label_spec(spec, n)]]
    return labels + acts, probs


def label_spec(spec, name):
    s = T.label_spec(spec, name)
    return (str(s.get("color") or "ededed"), s.get("description") or "")


def describe(a):
    if a["op"] == "label":
        return f'label: create "{a["name"]}"'
    if a["op"] == "create":
        return (f'{a["mid"]}: open issue "{a["title"][:70]}" [{", ".join(a["labels"])}]'
                + (f' in {a["milestone"]}' if a["milestone"] else "") + f'; board {a["column"]}')
    if a["op"] == "board":
        return (f'{a["mid"]} #{a["issue"]}: board {"add, " if not a["item"] else ""}column {a["column"]}'
                + f', rank {a["rank"] if a.get("rank") is not None else "(none)"}')
    parts = (["title"] if a["title"] else []) + (["body"] if a["body"] else [])
    parts += [f"+{x}" for x in a["add"]] + [f"-{x}" for x in a["remove"]]
    if a["milestone"] is not None:
        parts.append(f"milestone {a['milestone'] or '(none)'}")
    return f'{a["mid"]} #{a["issue"]}: ' + ", ".join(parts)


# --- Writing -------------------------------------------------------------------------------------

class Pacer:
    """At most `n` writes per `window` seconds, and one per second at most."""

    def __init__(self, n, window=600):
        self.n, self.window, self.done = n, window, collections.deque()

    def wait(self):
        while True:
            now = time.monotonic()
            while self.done and now - self.done[0] >= self.window:
                self.done.popleft()
            if len(self.done) < self.n:
                break
            pause = self.window - (now - self.done[0]) + 1
            print(f"sync_github: pacing, {len(self.done)} writes in the last {self.window // 60} minutes; "
                  f"waiting {int(pause)} s", flush=True)
            time.sleep(pause)
        if self.done:
            time.sleep(max(0.0, 1 - (time.monotonic() - self.done[-1])))
        self.done.append(time.monotonic())


def record_issue(path, mid, num):
    """Write `issue: num` into the block of `mid` in checklists.yaml (adding the block at the end of
    `milestones:`, which is the last top-level key), keeping every other line."""
    lines = path.read_text().split("\n")
    top = [i for i, x in enumerate(lines) if x and not x.startswith((" ", "#"))]
    if not top or lines[top[-1]] != "milestones:":
        raise Stop(f"{path}: `milestones:` must be its last top-level key")
    start = next((i for i in range(top[-1] + 1, len(lines)) if lines[i] == f"  {mid}:"), None)
    if start is None:
        while lines and lines[-1] == "":
            lines.pop()
        lines += [f"  {mid}:", f"    issue: {num}", ""]
    else:
        end = next((i for i in range(start + 1, len(lines))
                    if lines[i].strip() and not lines[i].startswith("    ")), len(lines))
        at = next((i for i in range(start + 1, end) if lines[i].startswith("    issue:")), None)
        if at is None:
            lines.insert(start + 1, f"    issue: {num}")
        else:
            lines[at] = f"    issue: {num}"
    path.write_text("\n".join(lines))


def apply(acts, conf, board, stop_file, per, board_per, record):
    """Make the changes in order. Returns the number made; raises Stop on the first problem."""
    repo, org = conf["repo"], conf.get("org") or conf["repo"].split("/")[0]
    issues, boards, made = Pacer(per), Pacer(board_per), 0

    def guard(pacer):
        pacer.wait()
        if pathlib.Path(stop_file).exists():
            raise Stop(f"kill switch {stop_file} is set")

    def to_board(a, url):
        nonlocal made
        item = a.get("item")
        if not item:
            guard(boards)
            out, _ = gh(["project", "item-add", str(board["number"]), "--owner", org, "--url", url, "--format", "json"])
            item = json.loads(out)["id"]
            made += 1
        if a.get("set_column", True):
            guard(boards)
            gh(["project", "item-edit", "--id", item, "--project-id", board["id"], "--field-id", board["field_id"],
                "--single-select-option-id", board["options"][a["column"]]])
            made += 1
        if a.get("rank") is not None or a.get("had_rank"):
            guard(boards)
            gh(["project", "item-edit", "--id", item, "--project-id", board["id"], "--field-id", board["rank_id"],
                *(["--number", str(a["rank"])] if a.get("rank") is not None else ["--clear"])])
            made += 1

    for a in acts:
        print("sync_github:", describe(a), flush=True)
        if a["op"] == "label":
            guard(issues)
            gh(["label", "create", a["name"], "--repo", repo, "--color", a["color"], "--description", a["description"]])
        elif a["op"] == "create":
            guard(issues)
            with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as f:
                f.write(a["body"])
            args = ["issue", "create", "--repo", repo, "--title", a["title"], "--body-file", f.name]
            args += [x for lab in a["labels"] for x in ("--label", lab)]
            args += ["--milestone", a["milestone"]] if a["milestone"] else []
            try:
                out, _ = gh(args)
            finally:
                pathlib.Path(f.name).unlink()
            m = re.search(r"/issues/(\d+)", out)
            if not m:
                raise Stop(f"{a['mid']}: gh issue create gave no issue URL: {out.strip()[:200]}")
            record(a["mid"], int(m.group(1)))
            made += 1
            to_board(dict(a, item=None), out.strip().splitlines()[-1])
            continue
        elif a["op"] == "edit":
            guard(issues)
            args = ["issue", "edit", str(a["issue"]), "--repo", repo]
            tmp = None
            if a["title"]:
                args += ["--title", a["title"]]
            if a["body"]:
                with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as f:
                    f.write(a["body"])
                tmp = f.name
                args += ["--body-file", tmp]
            args += ["--add-label", ",".join(a["add"])] if a["add"] else []
            args += ["--remove-label", ",".join(a["remove"])] if a["remove"] else []
            if a["milestone"] is not None:
                args += ["--milestone", a["milestone"]] if a["milestone"] else ["--remove-milestone"]
            try:
                gh(args)
            finally:
                if tmp:
                    pathlib.Path(tmp).unlink()
        elif a["op"] == "board":
            to_board(a, a["url"])
            continue
        made += 1
    return made


# --- Commands ------------------------------------------------------------------------------------

def load(a):
    conf = T.yaml_load((ROOT / T.BOARD).read_text())
    _, tasks = MS.load_plan(ROOT)[:2]
    data = json.loads(pathlib.Path(a.fixture).read_text()) if getattr(a, "fixture", None) else live(conf)
    entries = (T.yaml_load((ROOT / MS.CHECKLISTS).read_text()) or {}).get("milestones") or {}
    stored = {k: (v or {}).get("issue") for k, v in entries.items() if (v or {}).get("issue")}
    return conf, tasks, data, stored


def cmd_plan(a, do_apply=False):
    if do_apply and a.fixture:
        sys.exit("sync_github: apply writes to GitHub; it does not take --fixture")
    status = json.loads(pathlib.Path(a.status).read_text())
    conf, tasks, data, stored = load(a)
    only = set(a.only.split(",")) if a.only else None
    acts, probs = plan(status, tasks, data, stored, conf.get("labels") or {}, only)
    for p in probs:
        print("problem:", p)
    if not do_apply:
        for x in acts:
            print(describe(x))
        print(f"sync_github: {len(acts)} changes planned against main {status['main'][:7]}; "
              f"{len(probs)} problems (dry run; nothing written)")
        return 1 if probs else 0
    if probs:
        print("sync_github: nothing written: fix the problems first")
        return 1
    if pathlib.Path(a.stop_file).exists():
        print(f"sync_github: nothing written: the kill switch {a.stop_file} is set")
        return 1
    try:
        left = remaining()
        if left < MIN_REMAINING:
            raise Stop(f"only {left} API calls remain before the rate limit")
        made = apply(acts, conf, data["board"], a.stop_file, a.per_10min, a.board_per_10min,
                     lambda mid, n: record_issue(ROOT / MS.CHECKLISTS, mid, n))
    except Stop as e:
        print(f"sync_github: STOPPED: {e}")
        print("sync_github: issue numbers of new issues are in docs/tasks/checklists.yaml; a re-run continues")
        return 2
    print(f"sync_github: done, {made} writes")
    return 0


def cmd_adopt(a):
    conf, tasks, data, stored = load(a)
    ms_tasks = [t for t in tasks if t["kind"] == "milestone"]
    issues, probs = find_issues(ms_tasks, data, stored)
    for p in probs:
        print("problem:", p)
    new = {mid: i["number"] for mid, i in issues.items() if mid not in stored}
    for mid, n in sorted(new.items(), key=lambda x: x[1]):
        record_issue(ROOT / MS.CHECKLISTS, mid, n)
    print(f"sync_github adopt: {len(new)} issue numbers written, {len(stored)} were there, "
          f"{len(ms_tasks) - len(issues)} milestones without an issue; {len(probs)} problems")
    return 1 if probs else 0


def selftest():
    fails = []

    def expect(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        if not cond:
            fails.append(name)

    def task(mid, v1=True):
        return dict(id=f"T-{mid}", kind="milestone", milestone=mid, labels=["milestone", "area: geometry", "size: M", "intermediate"])

    def st(mid, v1=True, done=False, claimed=()):
        return dict(id=mid, title=f"Title {mid}", area="geometry", size="M", v1=v1, ranking=None, issue=None,
                    done_when="x", trust=[], needs=[], proof_tasks=[], claimed_by=list(claimed), stale_claims=[],
                    last_step=None, items=[], ticked=0, total=0, done=done,
                    review=dict(state="none", why="not yet"), closable=False)

    status = dict(main="abc1234", computed_at="2026-11-25T08:00Z",
                  milestones={"A1": st("A1"), "A2": st("A2", claimed=["regge"]), "A3": st("A3", done=True),
                              "B1": st("B1", v1=False), "A4": st("A4")})
    tasks = [task(m) for m in status["milestones"]] + [dict(id="T-A1-P1", kind="proof", milestone="A1", labels=[])]
    board = dict(id="P", number=1, field_id="F", rank_id="R", options={c: c for c in [*STATUS.values(), "Not scheduled"]},
                 items={"1": dict(id="I1", column="Ready", rank=None)})
    iss = lambda n, mid, labels, **k: dict(dict(number=n, title=f"T-{mid}: Title {mid}", state="open", reason="",  # noqa: E731
                                                labels=labels, assignees=[], milestone=None, body="", url=f"u/{n}"), **k)
    data = dict(issues=[iss(1, "A1", ["milestone", "area: geometry", "size: M", "intermediate", "ready", "status: ready"],
                            milestone="v1.0", body=MS.body(status["milestones"]["A1"], "zzz9999", "1 November 2026", [], {})),
                        iss(2, "A2", ["milestone", "claimed", "blocked"]),
                        iss(3, "A3", ["milestone", "area: geometry", "size: M", "intermediate"], state="closed", reason="completed"),
                        iss(4, "B1", ["milestone", "area: geometry", "size: M", "intermediate", "claimed"],
                            milestone="v1.0", assignees=["someone"]),
                        iss(9, "A1", ["milestone"]),
                        dict(number=5, title="T-A1-P1: a proof task", state="open", reason="", labels=["ready"],
                             assignees=[], milestone=None, body="", url="u/5")],
                labels=["milestone", "area: geometry", "size: M", "intermediate", "status: ready"],
                milestones=["v1.0"], board=board)
    acts, probs = plan(status, tasks, data, {}, {})
    by = collections.defaultdict(list)
    for a in acts:
        by[(a["op"], a.get("mid"))].append(a)
    e = lambda mid: (by[("edit", mid)] or [None])[0]  # noqa: E731
    expect("no problems on a complete fixture", probs == [])
    expect("adopts the lowest-numbered issue; one changed generated-by line is not an edit; the old ready label goes",
           e("A1") and e("A1")["issue"] == 1 and e("A1")["body"] is None and e("A1")["remove"] == ["ready"])
    expect("a stream's claim gives status: in-progress; the claim label is not touched; blocked goes",
           e("A2")["add"][-1] == "status: in-progress" and "claimed" not in e("A2")["remove"] and "blocked" in e("A2")["remove"])
    expect("a closed issue gives status: done and the column Done; it is not reopened",
           "status: done" in e("A3")["add"] and by[("board", "A3")][0]["column"] == "Done"
           and not any(a["op"] in ("close", "reopen") for a in acts))
    expect("outside v1.0: not-scheduled and help-wanted, out of the GitHub Milestone, column Not scheduled; "
           "the outside claim is shown", e("B1")["milestone"] == "" and {NOT_SCHEDULED, HELP_WANTED} <= set(e("B1")["add"])
           and by[("board", "B1")][0]["column"] == "Not scheduled" and "@someone" in e("B1")["body"])
    expect("a milestone without an issue is opened once, in v1.0, with its labels",
           len(by[("create", "A4")]) == 1 and by[("create", "A4")][0]["milestone"] == "v1.0")
    expect("missing labels are created, the claim labels never",
           {a["name"] for a in acts if a["op"] == "label"} >= {"status: in-progress", NOT_SCHEDULED}
           and not any(a["op"] == "label" and a["name"] in CLAIM_LABELS for a in acts))
    expect("an issue in the right column is not moved", not by[("board", "A1")])
    ranked = dict(status, milestones=dict(status["milestones"], A1=dict(status["milestones"]["A1"], ranking=2),
                                          A3=dict(status["milestones"]["A3"], ranking=5)))
    acts4, _ = plan(ranked, tasks, data, {}, {})
    b4 = {a["mid"]: a for a in acts4 if a["op"] == "board"}
    expect("a new ranking sets the board's Rank without moving the column; a done milestone gets no rank",
           b4.get("A1", {}).get("rank") == 2 and b4["A1"]["set_column"] is False and b4.get("A3", {}).get("rank") is None
           and same_rank(2.0, 2) and not same_rank(None, 2) and same_rank(None, None))
    expect("the proof task is linked from its milestone",
           "T-A1-P1 (#5)" in MS.body(dict(status["milestones"]["A1"], proof_tasks=["T-A1-P1"]), "a", "d", [], {"T-A1-P1": 5}))
    acts2, probs2 = plan(status, tasks, data, {"A1": 9, "A2": 5}, {})
    expect("a stored number is used, and one that is not the milestone's issue is a problem",
           (by2 := {(a["op"], a.get("mid")): a for a in acts2}) and by2.get(("edit", "A1"), {}).get("issue") == 9
           and any("A2" in p for p in probs2))
    _, probs3 = plan(status, tasks, dict(data, milestones=[], board=None), {}, {})
    expect("a missing GitHub Milestone or board is a problem (apply then writes nothing)", len(probs3) == 2)
    expect("the families: status, area and old status labels are ours; claimed, review and upstream labels of others are not",
           ours("status: done") and ours("area: x") and ours("blocked") and not ours("claimed")
           and not ours("review") and not ours("trust-check"))
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "c.yaml"
        p.write_text("# c\nv1.0:\n  count: 1\n\nmilestones:\n  A1:\n    ranking: null\n    items:\n      - id: m1\n\n  A2:\n    issue: 3\n")
        record_issue(p, "A1", 7)
        record_issue(p, "A2", 8)
        record_issue(p, "B1", 9)
        y = T.yaml_load(p.read_text())
        expect("record_issue writes, replaces and appends issue numbers and keeps the rest",
               y["milestones"]["A1"] == {"issue": 7, "ranking": None, "items": [{"id": "m1"}]}
               and y["milestones"]["A2"] == {"issue": 8} and y["milestones"]["B1"] == {"issue": 9}
               and p.read_text().startswith("# c\n"))
    pc = Pacer(2, window=1)
    t0 = time.monotonic()
    for _ in range(3):
        pc.wait()
    expect("the pacer waits once the window is full", time.monotonic() - t0 >= 1)
    print("sync_github selftest:", "OK" if not fails else f"FAILED ({len(fails)})")
    return 1 if fails else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    sub = ap.add_subparsers(dest="cmd")
    for name in ("plan", "apply"):
        p = sub.add_parser(name)
        p.add_argument("--status", required=True)
        p.add_argument("--only")
        p.add_argument("--fixture")
        if name == "apply":
            p.add_argument("--stop-file", required=True)
            p.add_argument("--per-10min", type=int, default=20)
            p.add_argument("--board-per-10min", type=int, default=60)
    p = sub.add_parser("adopt")
    p.add_argument("--fixture")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if a.cmd == "plan":
        return cmd_plan(a)
    if a.cmd == "apply":
        return cmd_plan(a, do_apply=True)
    if a.cmd == "adopt":
        return cmd_adopt(a)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
