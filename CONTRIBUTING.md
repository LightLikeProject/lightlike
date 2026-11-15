# Contributing

Contributions are welcome in every area: proofs, definitions, statements, tests against the
literature, corrections to conventions, and reviews of whether a statement says what its source
says. Every task on the [task board](docs/tasks/README.md) is open to everyone. Contributions are
welcome however you work, by hand or with AI tools; the pull request template has an optional
field for AI assistance.

## Your first proof task

A proof task is one lemma whose statement is fixed: it needs Lean but no physics. This route runs
in the browser, with nothing to install, in [GitHub Codespaces](https://docs.github.com/en/codespaces)
(usage counts toward your GitHub account's Codespaces allowance).

1. On the repository page, open **Code**, then **Codespaces**, and choose **Create codespace on
   main**. The setup in `.devcontainer/` installs Lean and downloads the compiled Mathlib; the
   terminal shows its progress.
2. Pick a [proof task labelled **ready**](https://github.com/LightlikeProject/lightlike/issues?q=is%3Aissue+is%3Aopen+label%3Aready+label%3Aproof-task), for example
   `T-DT4-P1`, comment `attempting` on its issue, and open its file, `Tasks/DT/T_DT4_P1.lean`. Its header lists the definitions the
   statement uses, with their files, and lemmas about them;
   `scripts/context-pack <declaration>` prints all of them in one block.
3. Run `lake build Tasks.DT.T_DT4_P1`. The first build compiles the parts of Physlib and Lightlike
   the task imports; later builds only what changed. The Lean panel (the ∀ icon at the top right
   of the editor) shows the goal at the cursor.
4. Replace the `sorry` with a proof, changing nothing else in the file, and run the same command
   until it reports no error.
5. Commit on a branch and push: `git checkout -b proof/T-DT4-P1`,
   `git commit -am "proof(dt): T-DT4-P1"`, `git push -u origin HEAD`. GitHub offers to create a
   fork.
6. Open the pull request from the link that `git push` prints, with the line `Task: T-DT4-P1`.
   Once it is merged, the task's issue is closed.

## Hard rules

A pull request is merged when the steps of `.github/workflows/ci.yml` marked `[hard rule]` pass.
Only these are required; everything else on this page is recommended practice. A pull request
that changes no Lean or build file (nor a file the Lean checks read, such as `docs/results.yaml`)
skips the Lean build and gets only the text checks, in a few minutes; one that does rebuilds only
the modules it changes and the modules that import them.

1. `lake build` succeeds, and every Lean file under `Lightlike/` is imported by `Lightlike.lean`,
   so that it is built and checked. After adding a file, `lake exe mk_all --lib Lightlike`
   updates `Lightlike.lean`.
2. No `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by` or `extern` in `Lightlike/`.
3. Every declaration of the library depends only on Lean's standard axioms `propext`,
   `Classical.choice` and `Quot.sound`. `scripts/AxiomAudit.lean` checks all of them, so there is
   no list of theorems to keep.
4. Nothing outside an `Exploratory/` folder imports a module inside one.
5. Every definition, and every declaration named in an API map or in `docs/results.yaml`, has a
   docstring (`scripts/DocCheck.lean`).
6. The literature sources of the catalog check out (`scripts/sources.py check`). This concerns
   the files under `docs/`, which the maintainers keep.

A pull request for a proof task must also change only the proof of its declaration, because the
statement has been reviewed and locked; the `Proof task` workflow checks this. The other CI steps
are marked `[advisory]` and only report.

## Finding a task

- **[Proof tasks](docs/tasks/README.md#proof-tasks):** a statement fixed in a file of `Tasks/`,
  with its proof open. Ready once the statement is locked.
- **[Milestones by area](docs/tasks/README.md#milestones-by-area):** every milestone of an area,
  with what it needs; its issue is labelled **ready** once those are done.
- **[Upstream](docs/tasks/README.md#upstream):** results to rework for Mathlib or Physlib.
- **Good first issues:** small and self-contained; they need no knowledge of the rest of the
  library.
- **Propose a result:** the [formalize this result](.github/ISSUE_TEMPLATE/formalize-result.yml)
  issue form takes a specific result from a specific paper, with its location in the paper.

The GitHub issue of a task opens once the task is ready, with the task's ID at the start of its
title; the board links the ID to it. The workflow `.github/workflows/tasks.yml` keeps the labels of the task issues current from their comments and from the pull requests that
name a task:

| Label | Means | Set when |
|---|---|---|
| `ready` | everything the task needs is done | its dependencies' issues are closed |
| `blocked` | it waits for another task | a task it needs is not done |
| `claimed` | one person works on it; they are the assignee | someone comments `claiming` |
| `attempting` | a proof task with attempts in flight | someone comments `attempting` |
| `in review` | a pull request for it is open | the pull request has the line `Task: <ID>` |

Nobody sets these by hand, and nothing in the repository records progress. A task is done when its
issue is closed as completed: by the pull request that finishes it (`Closes #<issue>`), or, for a
proof task, by the workflow once the proof is on `main`. The background of a milestone is in its
area's [milestone table](docs/tasks/milestones.md) and its sources; the
[conventions](docs/CONVENTIONS.md) apply to every task.

## Working on the same problem

The work is split into small tasks so that many people can work at once, several of them on the
same problem.

- **Claims.** Definition, statement and upstream tasks work best with one person at a time:
  comment `claiming` on the issue, and `stopping` to release it. A claim lapses after 14 days
  without a comment or pull request; the workflow then says so on the issue and removes the
  assignee. This avoids two competing definitions of the same notion.
- **Statements first.** Each result is first written as a Lean statement with `sorry`. Once it is
  reviewed and locked, its proof becomes a proof task with its own file in `Tasks/`. Large proofs
  are split into intermediate lemmas, each its own statement and proof task.
- **Ready** means every task it depends on is done, except proof tasks, which count once their
  statement is locked: you may use a lemma whose proof is still open.
- **Attempting.** Proof tasks are non-exclusive. Commenting `attempting` on the issue labels it
  `attempting` (`stopping` withdraws it); sharing your approach in the thread helps others.
- **First valid proof wins.** The first pull request that passes CI is merged. A later proof of
  the same statement is merged as an alternative only if it is clearly shorter, faster to check
  or more general.
- **Partial progress counts.** Helper lemmas that others can build on can go in their own pull
  request.
- **Routes.** Hard tasks list several routes on their card; attempts by different routes are
  welcome.

## Review

The [README](README.md#review) gives what a statement is checked for: conventions, quantifier
ranges, junk values and non-vacuity. To review a result, compare its statement and definitions
with the cited source and post your findings on its issue; a maintainer then records it as
**human-reviewed** in `docs/results.yaml`, with a link to that issue. A statement under review is
locked once it passes, or returned with reasons. A surprising result in an `Exploratory/` folder
is reviewed first and flagged to the maintainers; work on it continues meanwhile.

## Checking locally

```
lake exe cache get
lake build
lake build Tasks
```

The toolchain is pinned in `lean-toolchain` and the dependencies in `lake-manifest.json`. To check
a single file, `lake env lean -DautoImplicit=false path/File.lean`. Before opening a pull request,
commit and run `python3 scripts/gate.py`: it executes the steps of `.github/workflows/ci.yml` in
order. It needs Python 3.9 to 3.12 and the packages pinned in `requirements.txt`:
`python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt` (on Windows the
venv is activated with `.venv\Scripts\activate`). No script in `scripts/` is bash-only, but `gate.py`
runs each CI step with bash and the POSIX tools the steps call, so on Windows run it in WSL.

Each folder's `Lightlike/<Folder>/API-map.md` lists what it contains and marks what is missing
with `[TODO]`. To collect everything one declaration depends on into a single block, run
`scripts/context-pack <declaration>` (needs a built library; `--max-chars` caps the output).

## Recommended practice

Each of these makes a result easier to trust or to reuse. None blocks a merge.

- **Reuse first.** Before adding a definition, check whether Mathlib or Physlib has it, and use
  it. [docs/CONVENTIONS.md](docs/CONVENTIONS.md) lists the definitions taken from Physlib.
- **Trust checks.** A new definition reproduces a published value or known identity, and a
  deliberately wrong model or input is shown to give a different result. A definition can
  type-check and still mean something other than the literature's notion; this is the cheapest
  way to catch it.
- **Non-vacuity examples.** A concrete case satisfies the hypotheses of each main theorem. With
  unsatisfiable hypotheses, any conclusion is provable.
- **Junk values.** Lean's `a / 0 = 0` and similar conventions
  ([docs/CONVENTIONS.md](docs/CONVENTIONS.md#leans-junk-values)) can make a statement true for a
  degenerate reason; state the domain and assume it.
- **Conventions.** Follow [docs/CONVENTIONS.md](docs/CONVENTIONS.md), or say in the docstring where
  and why a definition departs from them, so that results compose.
- **Style.** Follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html).
  Give every main theorem a docstring and every file a module docstring: readers find results
  through them.
- **Lean files only.** A pull request changes Lean files. The catalog (`docs/results.yaml` and
  `docs/RESULTS.md`, the API maps, the milestone and task pages, the source list) is kept by the
  maintainers, who add a new result to it after merging; say in the pull request what it should
  record. To rename a declaration the catalog names, keep a `@[deprecated]` alias under the old
  name, as Mathlib does.
- **Outside readers.** Write code comments, docstrings and pull requests for someone who has not
  seen how they were produced.

## Pull requests

Work on a branch and keep each pull request to one topic. Commit messages use
`type(scope): summary`, followed by a body that says why. A maintainer merges.

## For maintainers

- **Results.** After merging a result, add it to `docs/results.yaml` and to the API map of its
  folder, then run `python3 scripts/api_map.py generate` (writes `docs/RESULTS.md` and the
  counts in `README.md`) and `python3 scripts/api_map.py check`.
- **Tasks.** `docs/tasks/milestones.md` and `docs/tasks/decomposition.yaml` are the plan, and the
  sources of the board. `python3 scripts/tasks.py generate` writes the board,
  `docs/tasks/tasks.yaml`, `Tasks.lean` and the milestone counts in `ROADMAP.md`; `tasks.py deps`
  writes the header of each proof-task file: the statement, a hint, what the statement uses and
  the references; `tasks.py lock
  <ID>` locks a reviewed statement. `tasks.py sync` prints what it would change on the task
  issues; the workflow `.github/workflows/tasks.yml` runs it with `--apply` once the repository
  variable `TASK_SYNC` is `on`. A change of scope is a pull request to the plan, after an issue.
- **Sources.** `python3 scripts/sources.py verify` looks up every reference at its publisher and
  writes `docs/tasks/sources-verified.json`, which the offline CI check reads; `verify` needs
  Poppler's `pdftotext`.
- **Upgrading Mathlib or Physlib.** On its own branch: bump the pins, run the gate, and fix what
  breaks. The risk is concentrated in the files that import `PhyslibAlpha` directly
  (`grep -rl 'import PhyslibAlpha' Lightlike`) and in names deprecated at the new version.
- **Scripts.** [scripts/README.md](scripts/README.md) lists the tools and the numerical
  cross-checks that Lean docstrings cite.

## Conduct and contact

Everyone who takes part follows the [code of conduct](CODE_OF_CONDUCT.md). Questions about a task
go on its issue, other questions and proposals in
[GitHub Discussions](https://github.com/LightlikeProject/lightlike/discussions). For anything else,
including a conduct report, write to the project address, lightlike.project@gmail.com.

## License

By contributing you agree that your contributions are licensed under the Apache License 2.0
(see [LICENSE](LICENSE)).
