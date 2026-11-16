#!/usr/bin/env python3
"""Pull requests do not change generated files: the maintainers regenerate them after merging, in
one commit per batch, so that parallel pull requests do not conflict in them.

The generated content is docs/RESULTS.md (written by `api_map.py generate` from docs/results.yaml);
the task board docs/tasks/README.md, docs/tasks/tasks.yaml and Tasks.lean (written by
`tasks.py generate` from the plan); and the generated parts of README.md (the results summary and
the paragraph of task counts), of ROADMAP.md (the milestone counts) and of CHANGELOG.md (the counts
of its newest version). The rest of those three files is written by hand.

  python3 -I scripts/generated.py check               # against the branch point, see below
  python3 -I scripts/generated.py check --base REV    # against REV
  python3 -I scripts/generated.py reset [--base REV]  # put the branch point's generated content back
  python3 -I scripts/generated.py --selftest

`check` compares the generated content of the working tree with that of the branch point and exits
1 if a branch changed it. The branch point is, in CI on a pull request, the first parent of the
merge commit that CI checks out (the base branch; the checkout needs fetch-depth 2), and locally the
merge base of HEAD with origin/main. An integration branch of this repository (`integration/...`)
is the exception: it carries the regeneration commit of its batch, so its generated content must
instead be exactly what the generators produce from its sources. On main itself (in CI a push or a run on
demand, locally the branch main) `check` only reports whether the generated content is current.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import api_map  # noqa: E402
import tasks  # noqa: E402

WHOLE = ["docs/RESULTS.md", "docs/tasks/README.md", "docs/tasks/tasks.yaml", "Tasks.lean"]
PARTIAL = ["README.md", "ROADMAP.md", "CHANGELOG.md"]
REGEN = "python3 scripts/api_map.py generate && python3 scripts/tasks.py generate"
CHANGELOG_COUNT = re.compile(r"^- (\d+) (?:areas in \[ROADMAP|tasks on the \[task board\])", re.M)


def spans(path: str, text: str) -> list[tuple[int, int]]:
    """The character spans of the generated parts of the partly generated file `path`."""
    out: list[tuple[int, int]] = []
    if path == "README.md":
        a, b = api_map.README_SUMMARY
        if a in text and b in text:
            i = text.index(a) + len(a)
            out.append((i, text.index(b, i)))
        m = re.search(rf"^{re.escape(tasks.README_KINDS)}", text, re.M)
        if m:
            end = re.compile(r"\n[ \t]*\n").search(text, m.start())
            out.append((m.start(), end.start() if end else len(text)))
    elif path == "ROADMAP.md":
        out += [m.span() for m in re.finditer(rf"^{re.escape(tasks.ROADMAP_COUNT)}.*$", text, re.M)]
    elif path == "CHANGELOG.md":
        heads = [m.start() for m in re.finditer(r"^## \[", text, re.M)]
        if heads:
            a, b = heads[0], heads[1] if len(heads) > 1 else len(text)
            out += [m.span(1) for m in CHANGELOG_COUNT.finditer(text, a, b)]
    return sorted(out)


def pieces(path: str, text: str | None) -> list[str] | None:
    """The generated content of `path`: the whole text, or the list of its generated parts."""
    if text is None:
        return None
    return [text] if path in WHOLE else [text[a:b] for a, b in spans(path, text)]


def transplant(path: str, text: str, base: str) -> str:
    """`text` with its generated parts replaced by those of `base`."""
    mine, theirs = spans(path, text), pieces(path, base)
    if len(mine) != len(theirs):
        raise SystemExit(f"generated: cannot reset {path}: it has {len(mine)} generated parts, "
                         f"the base {len(theirs)}; restore them by hand")
    for (a, b), new in reversed(list(zip(mine, theirs))):
        text = text[:a] + new + text[b:]
    return text


def git(*a: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True, check=check)


def at(rev: str, path: str) -> str | None:
    r = git("show", f"{rev}:{path}", check=False)
    return r.stdout if r.returncode == 0 else None


def here(path: str) -> str | None:
    f = ROOT / path
    return f.read_text(encoding="utf-8") if f.is_file() else None


def context(base: str | None) -> tuple[str, str | None]:
    """('branch', base), ('integration', None) or ('main', None), and why, for `check`."""
    if base:
        return "branch", base
    if os.environ.get("GITHUB_ACTIONS") == "true":
        if os.environ.get("GITHUB_EVENT_NAME") != "pull_request":
            return "main", None
        event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text(encoding="utf-8"))
        pr = event["pull_request"]
        if (pr["head"]["ref"].startswith("integration/")
                and pr["head"]["repo"]["full_name"] == os.environ.get("GITHUB_REPOSITORY")):
            return "integration", None
        parents = git("rev-list", "--parents", "-n", "1", "HEAD").stdout.split()[1:]
        if len(parents) != 2:
            raise SystemExit("generated: CI did not check out the merge commit of the pull request "
                             "with its parents (actions/checkout needs fetch-depth: 2)")
        return "branch", parents[0]
    branch = git("rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
    if branch == "main":
        return "main", None
    if branch.startswith("integration/"):
        return "integration", None
    for ref in ("origin/main", "main"):
        r = git("merge-base", "HEAD", ref, check=False)
        if r.returncode == 0:
            return "branch", r.stdout.strip()
    raise SystemExit("generated: no origin/main or main to compare with; pass --base REV")


def stale() -> list[str]:
    """The generated files whose content is not what the generators produce from the sources."""
    want: dict[str, list[str]] = {}
    reg = api_map.load(ROOT)
    want["docs/RESULTS.md"] = [api_map.render(reg, ROOT)]
    readme = here("README.md")
    if readme is not None:
        want["README.md"] = [api_map.readme_summary(readme, reg)]
    _, ms, ts = tasks.build(ROOT)
    for path, text in tasks.outputs(ts, ms, ROOT).items():
        want.setdefault(path, []).append(text)
    return sorted(p for p, texts in want.items() if any(t != here(p) for t in texts))


def changed(base: str) -> list[str]:
    return [p for p in WHOLE + PARTIAL if pieces(p, here(p)) != pieces(p, at(base, p))]


def cmd_check(base: str | None) -> int:
    kind, base = context(base)
    if kind == "main":
        old = stale()
        print("generated: on main; " + (f"to regenerate after the merges ({REGEN}): {', '.join(old)}"
                                         if old else "all generated content is current"))
        return 0
    if kind == "integration":
        old = stale()
        for p in old:
            print(f"  - {p} is not what the generators produce: the batch's regeneration commit "
                  f"runs `{REGEN}`")
        print(f"generated: integration branch, {'FAILED' if old else 'OK (all current)'}")
        return 1 if old else 0
    bad = changed(base)
    for p in bad:
        print(f"  - {p}: this branch changes its generated content, which the maintainers "
              f"regenerate after merging; undo with `python3 scripts/generated.py reset`")
    short = git("rev-parse", "--short", base).stdout.strip()
    print(f"generated: {'FAILED' if bad else 'OK'} (against {short}; "
          f"{len(WHOLE)} generated files, the generated parts of {len(PARTIAL)} more)")
    return 1 if bad else 0


def cmd_reset(base: str | None) -> int:
    kind, base = context(base)
    if kind != "branch":
        print(f"generated: nothing to reset on {'an integration branch' if kind == 'integration' else 'main'}")
        return 0
    for p in changed(base):
        old, new = at(base, p), here(p)
        f = ROOT / p
        if old is None:
            f.unlink()
        elif p in WHOLE or new is None:
            f.write_text(old, encoding="utf-8")
        else:
            f.write_text(transplant(p, new, old), encoding="utf-8")
        print(f"reset {p}")
    return 0


def _tasks_and_milestones():
    _, ms, ts = tasks.build(ROOT)
    return ts, ms


def selftest() -> int:
    fails = []

    def expect(name: str, ok: bool) -> None:
        print(f"{'ok  ' if ok else 'FAIL'} {name}")
        if not ok:
            fails.append(name)

    a, b = api_map.README_SUMMARY
    readme = (f"# Title\n\nIntro.\n\n{a}\nThe catalog has 3 entries.\n{b}\n\n"
              f"{tasks.README_KINDS}9 tasks, and\nmore.\n\nOutro.\n")
    expect("README: the summary and the paragraph of task counts are the generated parts",
           pieces("README.md", readme) == ["\nThe catalog has 3 entries.\n",
                                           f"{tasks.README_KINDS}9 tasks, and\nmore."])
    expect("README: a hand-written change is not a generated change",
           pieces("README.md", readme.replace("Intro.", "A new intro.")) == pieces("README.md", readme))
    expect("README planted: a changed count is a generated change",
           pieces("README.md", readme.replace("3 entries", "4 entries")) != pieces("README.md", readme))
    expect("README planted: a changed task count is a generated change",
           pieces("README.md", readme.replace("9 tasks", "10 tasks")) != pieces("README.md", readme))
    mixed = readme.replace("Intro.", "A new intro.").replace("3 entries", "4 entries")
    expect("README: reset keeps the hand-written change and restores the counts",
           transplant("README.md", mixed, readme) == readme.replace("Intro.", "A new intro."))
    road = f"## A\n### Area\n{tasks.ROADMAP_COUNT} 3 · [x](y)\nText.\n"
    expect("ROADMAP planted: a changed milestone count is a generated change",
           pieces("ROADMAP.md", road.replace(" 3 ", " 4 ")) != pieces("ROADMAP.md", road)
           and pieces("ROADMAP.md", road.replace("Text.", "Other.")) == pieces("ROADMAP.md", road))
    log = ("# Changelog\n\n## [Unreleased]\n- 12 areas in [ROADMAP](ROADMAP.md)\n"
           "- 300 tasks on the [task board](b)\n\n## [0.1.0]\n- 5 areas in [ROADMAP](ROADMAP.md)\n")
    expect("CHANGELOG: only the counts of the newest version are generated",
           pieces("CHANGELOG.md", log) == ["12", "300"])
    expect("CHANGELOG planted: a changed count of the newest version is a generated change",
           pieces("CHANGELOG.md", log.replace("- 300", "- 301")) != pieces("CHANGELOG.md", log)
           and pieces("CHANGELOG.md", log.replace("- 5 areas", "- 6 areas")) == pieces("CHANGELOG.md", log))
    expect("a generated file is generated as a whole",
           pieces("docs/RESULTS.md", "x\ny\n") == ["x\ny\n"])
    expect("the generated files are those the generators write",
           set(WHOLE + PARTIAL) == {"docs/RESULTS.md"} | {"README.md"}
           | set(tasks.outputs(*_tasks_and_milestones(), ROOT)))
    print(f"generated selftest: {'OK' if not fails else 'FAILED'}")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("cmd", nargs="?", choices=["check", "reset"])
    ap.add_argument("--base", help="the revision to compare with (default: the branch point)")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return selftest()
    if a.cmd == "reset":
        return cmd_reset(a.base)
    if a.cmd == "check":
        return cmd_check(a.base)
    ap.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
