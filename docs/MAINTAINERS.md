# For maintainers

How the catalog, the task board and the sources are kept. Contributing a proof needs none of this:
see [CONTRIBUTING.md](../CONTRIBUTING.md).

- **Results.** Add a result to the API map of its folder and to the end of `docs/results.yaml` with
  the draft ID `LL-XXXX` (`LL-XXXX-a`, `-b`, ... for several; the merge assigns the numbers), then
  run `python3 scripts/api_map.py generate` (`docs/RESULTS.md`, the `README.md` counts) and `check`.
  A proven result that is the main theorem of a cited paper or book, or a named theorem, gets
  `main: true`; it is then listed again under Main results at the top of `docs/RESULTS.md`.
  An entry is a result that a paper or book would state as a theorem. Supporting lemmas stay
  in the code with docstrings and get no entry; the review of a catalogue change checks every
  new entry against this.
- **Tasks.** `docs/tasks/milestones.md` and `docs/tasks/decomposition.yaml` are the plan, and the
  sources of the board. `python3 scripts/tasks.py generate` writes the board,
  `docs/tasks/tasks.yaml`, `Tasks.lean` and the milestone counts in `ROADMAP.md`; `tasks.py deps`
  writes the header of each proof-task file: the statement, a hint, what the statement uses and the
  references; `tasks.py lock <ID>` locks a reviewed statement. `tasks.py sync` prints what it would
  change on the task issues; the workflow `.github/workflows/tasks.yml` runs it with `--apply` once
  the repository variable `TASK_SYNC` is `on`. A change of scope is a pull request to the plan,
  after an issue.
- **Sources.** `python3 scripts/sources.py verify` looks up every reference at its publisher and
  writes `docs/tasks/sources-verified.json`, which the offline CI check reads; `verify` needs
  Poppler's `pdftotext`.
- **Upgrading Mathlib or Physlib.** On its own branch: bump the pins, run the gate, and fix what
  breaks. The risk is concentrated in the files that import `PhyslibAlpha` directly
  (`grep -rl 'import PhyslibAlpha' Lightlike`) and in names deprecated at the new version.
- **Scripts.** [scripts/README.md](../scripts/README.md) lists the tools and the numerical
  cross-checks that Lean docstrings cite.
