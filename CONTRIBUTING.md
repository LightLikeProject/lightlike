# Contributing

Contributions are welcome in every area: proofs, definitions, statements, tests against the
literature, corrections to conventions, and reviews of whether a statement says what its source
says. The [Project board](https://github.com/orgs/LightlikeProject/projects) is the plan, and every
task on it is open to everyone ([how work is tracked](#how-work-is-tracked)). Contributions are
welcome however you work, by hand or with AI tools; the pull request template has an optional
field for AI assistance, and [AGENTS.md](AGENTS.md) holds the instructions for coding agents.

## Your first proof task

A proof task is one lemma whose statement is fixed: it needs Lean but no physics. Two routes lead
to the same file and the same checks: in the browser with nothing to install
([GitHub Codespaces](https://docs.github.com/en/codespaces); usage counts toward your account's
Codespaces allowance), or on your own machine.

**Route A: Codespaces.** On the repository page open **Code**, then **Codespaces**, and choose
**Create codespace on main**. The setup in `.devcontainer/` installs Lean and downloads the compiled
Mathlib; the terminal shows its progress.

**Route B: your machine** (macOS, Linux or WSL; the same steps are in [AGENTS.md](AGENTS.md#set-up)):

```bash
curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
. ~/.elan/env
git clone https://github.com/LightlikeProject/lightlike && cd lightlike
lake exe cache get
python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt
```

Then, on either route:

1. Pick a [proof task labelled **ready**](https://github.com/LightlikeProject/lightlike/issues?q=is%3Aissue+is%3Aopen+label%3Aready+label%3Aproof-task),
   comment `/claim` on its issue, and open its file, for example `Tasks/QU/T_QU1_P5.lean` for
   `T-QU1-P5`. Its header lists the definitions the statement uses, with their files, and lemmas
   about them; `scripts/context-pack <declaration>` prints all of them in one block.
2. Run `lake build Tasks.QU.T_QU1_P5`. The first build compiles the parts of Physlib and Lightlike
   the task imports; later builds only what changed. In Codespaces the Lean panel (the ∀ icon at
   the top right of the editor) shows the goal at the cursor.
3. Replace the `sorry` with a proof, changing nothing else in the file, and run the same command
   until it reports no error.
4. Commit on a branch and check it: `git checkout -b proof/T-QU1-P5`,
   `git commit -am "proof(tv): T-QU1-P5"`, then `python3 -I scripts/gate.py --task T-QU1-P5`. This
   fast mode builds only the task file and checks that no `sorry` is left, that only the proof
   changed and the statement still matches its lock, and that the proof uses only the standard
   axioms. It does not build the rest of the library; CI does.
5. Push: `git push -u origin HEAD`. GitHub offers to create a fork.
6. Open the pull request from the link that `git push` prints, with the line `Task: T-QU1-P5`.
   Once it is merged, the task's issue is closed.

## Working with an AI agent

Paste this into your coding agent, started in a clone set up as above. It follows the same steps.

```text
You are contributing one proof to Lightlike, a Lean 4 library; this folder is a clone of it.
1. Read AGENTS.md and CONTRIBUTING.md before anything else, and follow them.
2. Pick one open proof task labelled `ready` (CONTRIBUTING.md, "Your first proof task"). Tell me
   which, and comment `/claim` on its issue (or ask me to) before you start.
3. Work on a branch `proof/<task ID>`, one task per pull request.
4. Change only the proof in the task's file. Never edit the locked statement, and never add
   `sorry`, `admit`, `axiom`, `native_decide` or `maxHeartbeats 0`.
5. Build the task with `lake build Tasks.<Area>.<File>` until it reports no error.
6. Run `python3 -I scripts/gate.py --task <task ID>` and fix everything it reports.
7. Push and open the pull request with the template filled in: the `Task:` line, the AI-assistance
   field, and the last lines of the gate's output quoted in the summary.
8. If you are stuck, stop and tell me what you tried. Never weaken the statement to make it pass.
```

## Hard rules

A pull request is merged when the steps of `.github/workflows/ci.yml` marked `[hard rule]` pass.
Only these are required; everything else on this page is recommended practice. A pull request
that changes no Lean or build file (nor a file the Lean checks read, such as `docs/results.yaml`)
skips the Lean build and gets only the text checks, in a few minutes; one that does rebuilds only
the modules it changes and the modules that import them.

1. `lake build` succeeds, and every Lean file under `Lightlike/` is imported by `Lightlike.lean`,
   so that it is built and checked. After adding a file, `lake exe mk_all --lib Lightlike`
   updates `Lightlike.lean`. The task library builds too (`lake build Tasks`): every file under
   `Tasks/` compiles, with `sorry` allowed only in the proof of its task declaration.
2. No `sorry`, `admit`, `native_decide`, `axiom`, `implemented_by` or `extern` in `Lightlike/`,
   and no new `maxHeartbeats 0`: a heavy proof gets a finite limit for that declaration only,
   `set_option maxHeartbeats 400000 in` (`scripts/ci_check.py`, `scripts/heartbeats_baseline.txt`).
3. Every declaration of the library depends only on Lean's standard axioms `propext`,
   `Classical.choice` and `Quot.sound`. `scripts/AxiomAudit.lean` checks all of them, so there is
   no list of theorems to keep.
4. Nothing outside an `Exploratory/` folder imports a module inside one.
5. Every definition, and every declaration named in an API map or in `docs/results.yaml`, has a
   docstring (`scripts/DocCheck.lean`). Each name such an entry lists must be a declaration: a
   bound variable such as `η` fails the check too.
6. The literature sources of the catalog check out (`scripts/sources.py check`).
7. No local path, private e-mail address, token or key in a tracked file (`scripts/leak_check.py`).
8. No change to a generated file: `docs/RESULTS.md`, the task board (`docs/tasks/README.md`,
   `docs/tasks/tasks.yaml`, `Tasks.lean`) and the generated counts in `README.md`, `ROADMAP.md` and
   `CHANGELOG.md`. The maintainers regenerate them after merging, in one commit per batch, so
   that pull requests do not conflict in them (`scripts/generated.py check`;
   `python3 scripts/generated.py reset` undoes such a change and keeps the rest).
9. No planning ID in a Lean name: folders, files, namespaces and declarations under `Lightlike/`
   are named by their mathematics and sit in subject folders, never named by a milestone, gap,
   row or catalogue ID (`GE3`, `G1_007`, `HARow055`, `LL0031`) (`scripts/planning_ids.py`). The
   proof-task files of `Tasks/` keep their task IDs.

A proof-task pull request must also change only the proof of its declaration: the statement was
reviewed and locked (the `Proof task` workflow checks this). Other CI steps are `[advisory]`.

## Finding a task

- **[Proof tasks](docs/tasks/README.md#proof-tasks):** a statement fixed in a file of `Tasks/`,
  with its proof open. Ready once the statement is locked.
- **[Milestones](https://github.com/orgs/LightlikeProject/projects):** every milestone of
  [docs/tasks/milestones.md](docs/tasks/milestones.md) has one issue, which holds its checklist. The
  v1.0 milestones (the GitHub Milestone
  [v1.0](https://github.com/LightlikeProject/lightlike/issues?q=is%3Aissue+milestone%3Av1.0)) are
  worked in ranking order: take the lowest Rank in the Ready column of the Project board. The others
  carry the labels `not-scheduled` and `help-wanted`: open to you, not worked on by the maintainers'
  agents.
- **[Upstream](docs/tasks/README.md#upstream):** results to rework for Mathlib or Physlib.
- **Good first issues:** small and self-contained, needing no knowledge of the rest of the library.
- **Propose a result:** the [formalize this result](.github/ISSUE_TEMPLATE/formalize-result.yml)
  issue form takes a specific result from a specific paper, with its location in the paper.

An issue's title starts with its task's ID (`T-HA4`, `T-QU1-P5`); the task board links the ID to
it. A proof task's issue opens once the task is ready. The workflow `.github/workflows/tasks.yml`
keeps the labels of the proof-task issues current from their comments and from the pull requests
that name a task:

| Label | Means | Set when |
|---|---|---|
| `ready` | everything the task needs is done | its dependencies' issues are closed |
| `blocked` | it waits for another task | a task it needs is not done |
| `claimed` | one person works on it; they are the assignee | someone comments `/claim`; it ends after 48 hours unless a pull request naming the task is open, or on `/unclaim` |
| `in review` | a pull request for it is open | the pull request has the line `Task: <ID>` |

On a milestone's issue the workflow writes only `claimed` and the assignee. The rest is written by
`scripts/sync_github.py` after every merge: the body (the checklist, computed from `main` by
`scripts/milestone_status.py`), the area and size labels, the GitHub Milestone, the column and Rank
on the Project board, and one status label:

| Label (v1.0 only) | Means | Column |
|---|---|---|
| `status: ready` | free to take | Ready |
| `status: in-progress` | claimed, by a contributor (`/claim`) or by one of the maintainers' agents | In progress |
| `status: review` | every checklist item but the review items is ticked; it waits for its review, which ticks the review items | In review |
| `status: done` | reviewed and closed | Done |

Nobody sets these by hand. A proof task is done when the workflow closes its issue, once the proof
is on `main`. A milestone is done when every item of its checklist is ticked and a review by someone
who did not do the work passes, against its done-when (the file `docs/tasks/reviews/<ID>.md`); then
the maintainer closes its issue. A pull request never closes a milestone's issue: it names the
milestone with the line `Task: T-<ID>`. The background of a milestone is in its area's
[milestone table](docs/tasks/milestones.md) and its sources; the
[conventions](docs/CONVENTIONS.md) apply to every task.

## Working on the same problem

The work is split into small tasks so that many people can work at once, several on one problem.

- **Claims.** A task has one holder at a time:
  comment `/claim` on the issue, and `/unclaim` to release it. A claim lasts 48 hours, or as long as
  a pull request naming the task (`Task: <ID>`) is open; the workflow then says so on the issue and
  removes the assignee. A person holds at most 3 open claims; a fourth is refused with a comment.
  This avoids two competing definitions of the same notion. The old words `claiming`, `attempting`
  and `stopping` still work as aliases.
- **Statements first.** Each result is first written as a Lean statement with `sorry`. Once it is
  reviewed and locked, its proof becomes a proof task with its own file in `Tasks/`. Large proofs
  are split into intermediate lemmas, each its own statement and proof task.
- **Ready**, for a proof task, means every task it depends on is done, except proof tasks, which
  count once their statement is locked: you may use a lemma whose proof is still open. A v1.0
  milestone is `status: ready` when nobody holds it; the milestones it needs do not have to be
  closed first.
- **Claiming a proof task.** Claims are exclusive for every kind of task. Commenting `/claim` on the
  issue labels it `claimed` and assigns you (`/unclaim` withdraws it); a second `/claim` on a claimed
  task is answered with the holder and the expiry. Claims are advisory: if two pull requests arrive,
  the first that passes CI is merged. Sharing your approach in the thread helps others.
- **First valid proof wins.** The first pull request that passes CI is merged. A later proof of
  the same statement is merged as an alternative only if it is clearly shorter, faster to check
  or more general.
- **Partial progress counts.** Helper lemmas others can build on can go in their own pull request.
- **Routes.** Hard tasks list several routes on their card; attempts by different ones are welcome.

## Review

Pull requests carry no review label: a pull request merges when its gates and checks pass. A proof-task
pull request that changes only its own task file merges by itself; a maintainer merges any other pull
request once its checks pass. The check `review-gate` always passes; it stays because the repository's
ruleset names it.

Reviews are of milestones, not of pull requests. When every work item of a milestone is ticked, an agent
session other than the one that did the work reviews the finished milestone against the
[review rubric](docs/review-rubric.md): source match, hypotheses, conventions, quantifier ranges, junk
values and non-vacuity. The milestone's issue closes when every item is ticked and the review passes.

A review by an expert is welcome, optional, and nothing waits for it. To review a result, compare its
statement and definitions with the cited source and post your findings on an issue; once that issue is
linked from the result's entry in `docs/results.yaml`, the entry is **human-reviewed**. A surprising
result in an `Exploratory/` folder is flagged to the maintainers; work on it continues meanwhile.

The kernel cannot check that a definition or a statement means what its source means, so each
statement is compared with its cited source for conventions (signature, units, normalisations),
quantifier ranges and hypotheses, junk values of partial operations (such as `ℕ` subtraction and
`x / 0 = 0`) and non-vacuity (an example satisfies the hypotheses of each main theorem).

To review an entry, or to report a mismatch, open an [issue](https://github.com/LightlikeProject/lightlike/issues/new)
with the entry's ID, the place in its source, and what differs.

## Checking locally

```
lake exe cache get
lake build
lake build Tasks
```

The toolchain is pinned in `lean-toolchain` and the dependencies in `lake-manifest.json`. To check
a single file, `lake env lean -DautoImplicit=false path/File.lean`. Before opening a pull request,
commit and run `python3 scripts/gate.py`: it executes the steps of `.github/workflows/ci.yml` in
order. It needs Python 3.9 to 3.14 and the packages pinned in `requirements.txt`:
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
  deliberately wrong model or input is shown to give a different result. A definition can type-check
  and still mean something other than the literature's notion; this is the cheapest way to catch it.
- **Non-vacuity examples.** A concrete case satisfies the hypotheses of each main theorem. With
  unsatisfiable hypotheses, any conclusion is provable.
- **Junk values.** Lean's `a / 0 = 0` and similar [conventions](docs/CONVENTIONS.md#leans-junk-values)
  can make a statement true for a degenerate reason; state the domain and assume it.
- **Conventions.** Follow [docs/CONVENTIONS.md](docs/CONVENTIONS.md), or say in the docstring where
  and why a definition departs from them, so that results compose.
- **Style.** Follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html).
  Give every main theorem a docstring and every file a module docstring: readers find results
  through them. A module docstring starts with `# Title` in words and a summary paragraph, then
  `## Main results` (the main declarations, one line each) and `## References` (keys of
  [docs/tasks/sources.yaml](docs/tasks/sources.yaml)) when the file has them. Other sections are
  named `## Conventions` or `## Implementation notes`. A short file keeps the title and prose.
- **Lean files only.** A pull request changes Lean files. The catalog (`docs/results.yaml` and
  `docs/RESULTS.md`, the API maps, the milestone and task pages, the source list) is kept by the
  maintainers, who add a new result to it after merging; say in the pull request what it should
  record. To rename a declaration the catalog names, keep a `@[deprecated]` alias under the old
  name, as Mathlib does.

## Pull requests

One route for everyone, agents and maintainers included. Work on a branch, in a fork or, with write
access, here; keep each pull request to one task or topic, with its `Task:` line.

Commit messages (the same format as in [AGENTS.md](AGENTS.md#commits)): `type(scope): summary`, a
blank line, then a body that says why. `type` is one of `feat`, `fix`, `proof`, `docs`, `test`,
`refactor`, `ci`, `chore`; `scope` is the area folder in lower case (`regge`, `pl`, `sixj`). A
proof-task commit is `proof(<area>): T-<ID>`, for example `proof(tv): T-QU1-P5`. Examples:
`feat(regge): define deficit angles`, `fix(curvature): sign of the Ricci term`.

To update a pushed branch, merge `main` into it; never force-push. A maintainer squash-merges once
every CI check is green; the commit on `main` takes the pull request's title, number and
description: write them for outsiders.

## For maintainers

Adding results, keeping the task board and the sources, upgrading Mathlib or Physlib, and the
scripts: [docs/MAINTAINERS.md](docs/MAINTAINERS.md).

## Conduct and contact

Everyone who takes part follows the [code of conduct](CODE_OF_CONDUCT.md). Questions about a task
go on its issue, other questions and proposals in
[GitHub Discussions](https://github.com/LightlikeProject/lightlike/discussions). For anything else,
including a conduct report, write to the project address, lightlike.project@gmail.com.

## License

By contributing you agree to license your contributions under the [Apache License 2.0](LICENSE).

## What Lightlike is

- **It is** a library of definitions, statements and proofs about the mathematics of physical
  models. Every result has a tier: **established** (standard mathematics and physics),
  **frontier** (published proposals) or **exploratory** (new or unpublished models). Exploratory
  work goes in `Exploratory/` folders, which the rest of the library may not import.
- **It is not** a claim that a model describes nature. A theorem says what follows from a model's
  definitions, under the hypotheses and limits stated with it.
- **It does not** prefer one approach to quantum gravity. Competing approaches sit side by side,
  each formalized from its own literature.

## How work is tracked

- **The Project board is the plan.** The [Project board](https://github.com/orgs/LightlikeProject/projects)
  "Lightlike" has one issue per milestone, in the columns Ready, In progress, In review, Done and
  Not scheduled; the v1.0 milestones are worked in the order of the board's Rank. Proof tasks are
  separate issues, each linked to its milestone.
- **Status is computed, never typed.** A milestone's issue holds its checklist (from
  [docs/tasks/checklists.yaml](docs/tasks/checklists.yaml)): the main theorem, the pieces, the trust
  checks, the catalogue entry and the review items, each naming the declarations that satisfy it.
  A script ticks an item when its declarations are on `main` with no `sorry` and only the standard
  axioms, and writes the issue and the board. Nobody edits a status by hand.
- **Every task is taken by one person at a time.** Comment `/claim` to take
  one (you are assigned) and `/unclaim` to release it. A claim lasts 48 hours, or while a pull request
  naming the task is open; a person holds at most 3 claims. Claims are advisory: if two pull requests
  arrive for one task, the first that passes CI is merged.
- **Done.** A proof task is done once its proof is on `main`; the workflow closes its issue. A
  milestone is done when every item is ticked and a review by someone who did not do the work has
  passed; the maintainer then closes its issue. Pull requests name a milestone with `Task: T-<ID>`
  and never close its issue.

## Help wanted, community, license and citation

Lightlike has one maintainer. Help is especially welcome with repository and CI maintenance, Lean
infrastructure, domain review, and leading an area: open an issue labelled
[**help wanted**](https://github.com/LightlikeProject/lightlike/labels/help%20wanted). Discussion
and coordination on [Discord](https://discord.gg/Eyx3zTx9JW); questions and proposals in
[GitHub Discussions](https://github.com/LightlikeProject/lightlike/discussions). Everyone follows
the [code of conduct](CODE_OF_CONDUCT.md); contact: lightlike.project@gmail.com. Apache License 2.0,
copyright The Lightlike contributors ([LICENSE](LICENSE)); cite it via [CITATION.cff](CITATION.cff).

## Building

Install Lean's version manager [elan](https://github.com/leanprover/elan) (see the [official
instructions](https://lean-lang.org/install/)). The versions are pinned: Lean and Mathlib `v4.35.0`,
Physlib at commit `cdfa609`. On Windows, install elan by those instructions, or run the commands
below in WSL, or use [Codespaces](CONTRIBUTING.md#your-first-proof-task). On Linux and macOS:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
git clone https://github.com/LightlikeProject/lightlike && cd lightlike
lake exe cache get
lake build
lake build Tasks
```

`lake exe cache get` downloads Mathlib's prebuilt files; the first `lake build` compiles Physlib and
Lightlike. On GitHub's 4-core Linux runner, Lightlike alone took about 42 minutes (Physlib comes on
top). Later builds compile only what changed. A full build needs about 38 GB of disk (`.lake/build`
about 24 GB, `.lake/packages` about 14 GB), and some modules up to about 6 GB of RAM per Lean process (16 GB is recommended; 8 GB machines may build very slowly).
`lake build Tasks` builds the proof-task files in `Tasks/`, which are not part of the library. The
checks in `scripts/` need Python 3.9 to 3.14 and the packages in `requirements.txt`:
`python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt` (on Windows the
venv is activated with `.venv\Scripts\activate`; `scripts/gate.py` runs the CI steps with bash).

To use Lightlike in a project with the same Lean version, add to its `lakefile.toml`:

```toml
[[require]]
name = "lightlike"
git = "https://github.com/LightlikeProject/lightlike"
rev = "v0.3.0"
```

Then, in a Lean file of that project:

```lean
import Lightlike

open Lightlike

#check @IsCoordMetric.bianchi_first   -- LL-0001, the first Bianchi identity in coordinates
```
