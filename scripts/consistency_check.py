#!/usr/bin/env python3
"""Check that the task management agrees with itself (owner, 25 Nov 2026). Run after every merge
(after scripts/sync_github.py) and daily. It checks:

  issues      every milestone has exactly one issue, with the labels, GitHub Milestone, body and
              board column that scripts/sync_github.py would give it (so a body that differs from
              the computed checklist is a failure);
  checklists  every v1.0 milestone has a checklist in the format of docs/tasks/checklists.yaml;
  closed      no v1.0 milestone's issue is closed while an item is unticked or before a passing
              review; a closed issue with the label review-pending is a transitional state, not a
              failure (its review runs, and it is reopened if the review fails);
  claims      every claimed milestone has a fresh stream status file; no two streams claim the
              same milestone, no stream claims two, and no stream claims a milestone outside v1.0;
  names       no planning ID (a gap, milestone, row or catalogue ID) in a Lean folder name, file
              name, namespace or declaration name: scripts/planning_ids.py, which CI runs too;
  catalogue   no entry of docs/results.yaml is `proven` while listing hypotheses, or while one of
              its declarations takes a proposition that another entry lists as an open hypothesis
              (with --lake or --audit: read from the hypotheses that scripts/AxiomAudit.lean
              reports);
  queue       every waiting entry of the merge queue (--mq) names a milestone of the plan.

A check whose input is not given is reported as not run, never as passed. With --report FILE the
failures replace the generated section of FILE (the maintainers' decisions file, outside
the repository), so it always shows the failures of the last run.

Usage, from the repository root:

    python3 scripts/consistency_check.py --status OUT/status.json [--main DIR] [--fixture F.json]
        [--mq merge-queue.yaml] [--lake LAKE | --audit decls.jsonl] [--report FILE]
    python3 scripts/consistency_check.py --selftest

Exit status: 0 when every check that ran passed, 1 when one failed.
"""
from __future__ import annotations

import argparse
import collections
import datetime
import json
import pathlib
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import milestone_status as MS  # noqa: E402
import sync_github as SG  # noqa: E402
import planning_ids as PI  # noqa: E402
import tasks as T  # noqa: E402

WAITING = {"ready", "taken", "held"}
START, END = "<!-- consistency_check: start -->", "<!-- consistency_check: end -->"
SHOW = 8  # examples listed per failure


def some(xs):
    xs = list(xs)
    return ", ".join(map(str, xs[:SHOW])) + (f" and {len(xs) - SHOW} more" if len(xs) > SHOW else "")


# --- The checks ----------------------------------------------------------------------------------

def check_issues(status, tasks, data, stored, spec):
    out = []
    ms_tasks = [t for t in tasks if t["kind"] == "milestone" and t["milestone"] in status["milestones"]]
    issues, probs = SG.find_issues(ms_tasks, data, stored)
    out += probs
    ids = {t["id"]: t["milestone"] for t in ms_tasks}
    held = collections.defaultdict(list)
    for i in data["issues"]:
        m = T.ISSUE_TITLE.match(i["title"])
        if m and m.group(1) in ids and not (i["state"] == "closed" and i.get("reason") in ("not_planned", "duplicate")):
            held[ids[m.group(1)]].append(i["number"])
    for mid, nums in sorted(held.items()):
        if len(nums) > 1:
            out.append(f"{mid} has {len(nums)} issues: " + ", ".join(f"#{n}" for n in sorted(nums))
                       + " (close the others as duplicates)")
    missing = sorted((t["milestone"] for t in ms_tasks if t["milestone"] not in issues), key=T.natural)
    if missing:
        out.append(f"{len(missing)} milestones have no issue: {some(missing)}")
    acts, probs = SG.plan(status, tasks, data, stored, spec)
    out += probs
    for a in acts:
        if a["op"] in ("edit", "board"):
            out.append(f"{a['mid']} #{a['issue']} is not as the computed status says: "
                       + SG.describe(a).split(": ", 1)[1])
    return out


def check_checklists(root):
    ms, _, data, v1 = MS.load_plan(root)
    return MS.schema_problems(ms, data, v1)


def check_closed(status, tasks, data, stored):
    ms_tasks = [t for t in tasks if t["kind"] == "milestone" and t["milestone"] in status["milestones"]]
    issues, _ = SG.find_issues(ms_tasks, data, stored)
    out = []
    for mid, i in sorted(issues.items(), key=lambda x: T.natural(x[0])):
        st = status["milestones"][mid]
        if i["state"] != "closed" or not st["v1"] or st["closable"] or SG.REVIEW_PENDING in i.get("labels", []):
            continue
        why = [f"{st['ticked']} of {st['total']} items ticked"] if not st["done"] else []
        why.append(f"review: {st['review']['state']}")
        out.append(f"{mid} #{i['number']} is closed, but " + "; ".join(why) + " (reopen it)")
    return out


def check_claims(status):
    out, by_stream = [], collections.defaultdict(list)
    for mid, st in status["milestones"].items():
        for s in st["claimed_by"]:
            by_stream[s].append(mid)
            if not st["v1"]:
                out.append(f"the stream {s} claims {mid}, which is not in v1.0")
        if len(st["claimed_by"]) > 1:
            out.append(f"{mid} is claimed by {len(st['claimed_by'])} streams: " + ", ".join(st["claimed_by"]))
        for s in st.get("stale_claims") or []:
            out.append(f"the stream {s} claims {mid}, but its status file is more than {MS.FRESH_HOURS} hours old")
    for s, mids in sorted(by_stream.items()):
        if len(mids) > 1:
            out.append(f"the stream {s} claims {len(mids)} milestones: " + ", ".join(sorted(mids)))
    return out


def check_names(main):
    hits = PI.check(main)
    return [f"{len(hits)} Lean folder, file or declaration names have a planning ID: {some(hits)}"] if hits else []


def catalogue(main):
    data = T.yaml_load((main / "docs/results.yaml").read_text())
    return data if isinstance(data, list) else (data or {}).get("results") or []


def check_catalogue(entries, aud):
    """`aud`: {declaration: audit line with `hyps`}, or None when the audit did not run."""
    out = []
    for e in entries:
        if e.get("status") == "proven" and e.get("hypotheses"):
            out.append(f"{e['id']} is proven but lists hypotheses: " + ", ".join(e["hypotheses"]))
    if aud is None:
        return out, False
    open_h = collections.defaultdict(list)
    for e in entries:
        if e.get("status") == "conditional":
            for h in e.get("hypotheses") or []:
                open_h[h].append(e["id"])
    for e in entries:
        if e.get("status") != "proven":
            continue
        for d in e.get("decls") or []:
            for h in (aud.get(d) or {}).get("hyps") or []:
                if h in open_h:
                    out.append(f"{e['id']} is proven, but {d} takes {h}, an open hypothesis of "
                               + ", ".join(sorted(set(open_h[h]))))
    return out, True


def check_queue(queue, milestones):
    es = (queue or {}).get("entries") if isinstance(queue, dict) else queue
    loose, wrong = [], []
    for e in es or []:
        if e.get("state") not in WAITING:
            continue
        m = e.get("milestone")
        if not m:
            loose.append(f"#{e.get('id')}")
        elif str(m) not in milestones:
            wrong.append(f"#{e.get('id')} ({m})")
    out = []
    if loose:
        out.append(f"{len(loose)} waiting merge-queue entries name no milestone: {some(loose)}")
    if wrong:
        out.append(f"{len(wrong)} waiting merge-queue entries name a milestone that is not in the plan: {some(wrong)}")
    return out


# --- The run -------------------------------------------------------------------------------------

def run(status, tasks, data, stored, spec, root, main, queue, aud):
    """[(check, [failures] or None when not run)]."""
    res = []
    res.append(("issues", check_issues(status, tasks, data, stored, spec) if data is not None else None))
    res.append(("checklists", check_checklists(root)))
    res.append(("closed", check_closed(status, tasks, data, stored) if data is not None else None))
    res.append(("claims", check_claims(status)))
    res.append(("names", check_names(main)))
    cat, ran = check_catalogue(catalogue(main), aud)
    res.append(("catalogue", cat if ran or cat else None))
    res.append(("queue", check_queue(queue, set(status["milestones"])) if queue is not None else None))
    return res


def report_text(res, status, when):
    bad = sum(len(f) for _, f in res if f)
    L = [START, "## Consistency check (generated by scripts/consistency_check.py; replaced at every run)", "",
         f"Last run {when} on main {status['main'][:7]}: "
         + (f"{bad} failures." if bad else "no failures.")
         + " Each failure is either repaired or, when it needs a decision of the maintainers, listed above as one.", ""]
    for name, f in res:
        if f is None:
            L.append(f"- **{name}**: not run (its input was not given)")
        elif not f:
            L.append(f"- **{name}**: OK")
        else:
            L.append(f"- **{name}**: {len(f)} failures")
            L += [f"  - {x}" for x in f]
    return "\n".join(L + ["", END])


def write_report(path, text):
    p = pathlib.Path(path)
    old = p.read_text() if p.exists() else ""
    if START in old and END in old:
        new = old[:old.index(START)] + text + old[old.index(END) + len(END):]
    else:
        new = (old.rstrip() + "\n\n" if old.strip() else "") + text + "\n"
    p.write_text(new)


def main_cmd(a):
    status = json.loads(pathlib.Path(a.status).read_text())
    main = pathlib.Path(a.main).resolve()
    conf = T.yaml_load((ROOT / T.BOARD).read_text())
    _, tasks = MS.load_plan(ROOT)[:2]
    entries = (T.yaml_load((ROOT / MS.CHECKLISTS).read_text()) or {}).get("milestones") or {}
    stored = {k: (v or {}).get("issue") for k, v in entries.items() if (v or {}).get("issue")}
    if a.fixture:
        data = json.loads(pathlib.Path(a.fixture).read_text())
    elif a.offline:
        data = None
    else:
        try:
            data = SG.live(conf)
        except SG.Stop as e:
            print(f"consistency_check: GitHub could not be read ({e}); the issue checks do not run")
            data = None
    queue = T.yaml_load(pathlib.Path(a.mq).read_text()) if a.mq else None
    aud = None
    if a.audit or a.lake:
        names = {d for e in catalogue(main) if e.get("status") == "proven" for d in e.get("decls") or []}
        aud = MS.audit(main, names, a.lake, a.audit)
    res = run(status, tasks, data, stored, conf.get("labels") or {}, ROOT, main, queue, aud)
    when = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    text = report_text(res, status, when)
    print(text.replace(START + "\n", "").replace("\n" + END, ""))
    if a.report:
        write_report(a.report, text)
    return 1 if any(f for _, f in res) else 0


def selftest():
    fails = []

    def expect(name, cond):
        print(("ok   " if cond else "FAIL ") + name)
        if not cond:
            fails.append(name)

    st = lambda mid, **k: dict(dict(id=mid, title=f"Title {mid}", area="geometry", size="M", v1=True,  # noqa: E731
                                     ranking=None, issue=None, done_when="x", trust=[], needs=[], proof_tasks=[],
                                     claimed_by=[], stale_claims=[], last_step=None, items=[], ticked=1, total=2,
                                     done=False, review=dict(state="none", why="not yet"), closable=False), **k)
    status = dict(main="abc1234", computed_at="2026-11-25T08:00Z", milestones={
        "A1": st("A1", claimed_by=["regge", "opalg"]), "A2": st("A2", stale_claims=["oscillatory"]),
        "A3": st("A3", ticked=2, done=True, review=dict(state="pass"), closable=True), "B1": st("B1", v1=False, claimed_by=["regge"]), "A4": st("A4")})
    tasks = [dict(id=f"T-{m}", kind="milestone", milestone=m, labels=["milestone"]) for m in status["milestones"]]
    iss = lambda n, mid, **k: dict(dict(number=n, title=f"T-{mid}: Title {mid}", state="open", reason="",  # noqa: E731
                                        labels=["milestone"], assignees=[], milestone=None, body="", url=f"u/{n}"), **k)
    data = dict(issues=[iss(1, "A1", state="closed", reason="completed"), iss(2, "A1"), iss(3, "A3", state="closed", reason="completed"),
                        iss(4, "B1"), iss(5, "A4", state="closed", reason="completed", labels=["milestone", "review-pending"])],
                labels=[], milestones=["v1.0"],
                board=dict(id="P", number=1, field_id="F", options={c: c for c in SG.COLUMNS}, items={}))
    iss_f = check_issues(status, tasks, data, {}, {})
    expect("issues: a milestone with two issues, one with none, and issues that differ from the computed status fail",
           any("A1 has 2 issues" in x for x in iss_f) and any("milestones have no issue: A2" in x for x in iss_f)
           and any(x.startswith("B1 #4 is not as") for x in iss_f))
    cl = check_closed(status, tasks, data, {})
    expect("closed: an issue closed with unticked items fails; one closed after a passing review, and one closed "
           "with the label review-pending (transitional), do not",
           len(cl) == 1 and cl[0].startswith("A1 #1 is closed, but 1 of 2 items ticked"))
    cc = check_claims(status)
    expect("claims: two streams on one milestone, a stale status file, a stream on two milestones and one outside v1.0 fail",
           any("A1 is claimed by 2 streams" in x for x in cc) and any("oscillatory claims A2" in x for x in cc)
           and any("regge claims 2 milestones" in x for x in cc) and any("B1, which is not in v1.0" in x for x in cc))
    with tempfile.TemporaryDirectory() as d:
        m = pathlib.Path(d)
        (m / "Lightlike/Rows/G1_007").mkdir(parents=True)
        (m / "Lightlike/Rows/G1_007/A.lean").write_text("namespace Lightlike.Rows.G1_007\ntheorem t : True := trivial\n")
        (m / "Lightlike/Geometry").mkdir(parents=True)
        (m / "Lightlike/Geometry/B.lean").write_text("namespace Lightlike.Geometry\ntheorem gap_G2_015_ok : True := trivial\n"
                                                     "theorem G12 : True := trivial\n-- see G1-007\n")
        (m / "Tasks/GE").mkdir(parents=True)
        (m / "Tasks/GE/T_GE2_P1.lean").write_text("theorem Lightlike.Tasks.t : True := trivial\n")
        nm = check_names(m)
    expect("names: a Rows path, a gap ID in a namespace and in a declaration name fail; a comment, a task file and G12 do not",
           len(nm) == 1 and nm[0].startswith("4 Lean folder, file or declaration names") and "Lightlike/Rows/" in nm[0]
           and "gap_G2_015_ok" in nm[0] and "G12 " not in nm[0] and "T_GE2_P1" not in nm[0])
    ents = [dict(id="LL-1", status="proven", decls=["a"], hypotheses=["H"]),
            dict(id="LL-2", status="conditional", decls=["b"], hypotheses=["Lightlike.Q"]),
            dict(id="LL-3", status="proven", decls=["c"]), dict(id="LL-4", status="proven", decls=["d"])]
    ca, ran = check_catalogue(ents, {"c": dict(hyps=["Lightlike.Q"]), "d": dict(hyps=["Lightlike.Other"])})
    expect("catalogue: proven with hypotheses, and proven while taking an open hypothesis, fail; other hypotheses do not",
           ran and len(ca) == 2 and "LL-1 is proven but lists" in ca[0] and "c takes Lightlike.Q, an open hypothesis of LL-2" in ca[1])
    expect("catalogue: without the audit only the listed hypotheses are checked, and the check says so",
           check_catalogue(ents, None) == ([ca[0]], False))
    q = dict(entries=[dict(id=1, state="ready"), dict(id=2, state="held", milestone="A1"), dict(id=3, state="taken", milestone="ZZ"),
                      dict(id=4, state="merged")])
    qq = check_queue(q, set(status["milestones"]))
    expect("queue: a waiting entry without a milestone, or with one outside the plan, fails; merged entries are not checked",
           len(qq) == 2 and "#1" in qq[0] and "#3 (ZZ)" in qq[1])
    res = [("issues", None), ("claims", []), ("queue", qq)]
    txt = report_text(res, status, "2026-11-25T09:00Z")
    expect("report: a check that did not run says so, never OK", "**issues**: not run" in txt and "**claims**: OK" in txt)
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "owner-decisions.md"
        p.write_text("# Owner decisions\n\n1. a question\n")
        write_report(p, txt)
        write_report(p, report_text([("claims", [])], status, "2026-11-25T10:00Z"))
        t = p.read_text()
    expect("report: the generated section is replaced, the rest of the file kept",
           t.startswith("# Owner decisions\n\n1. a question\n") and t.count(START) == 1 and "10:00Z" in t and "09:00Z" not in t)
    print("consistency_check selftest:", "OK" if not fails else f"FAILED ({len(fails)})")
    return 1 if fails else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--status")
    ap.add_argument("--main", default=str(ROOT))
    ap.add_argument("--fixture")
    ap.add_argument("--offline", action="store_true", help="do not read GitHub (the issue checks do not run)")
    ap.add_argument("--mq")
    ap.add_argument("--lake")
    ap.add_argument("--audit")
    ap.add_argument("--report")
    a = ap.parse_args(argv)
    if a.selftest:
        return selftest()
    if not a.status:
        ap.error("--status is required")
    return main_cmd(a)


if __name__ == "__main__":
    sys.exit(main())
