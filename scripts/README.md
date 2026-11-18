# scripts

Two kinds of files live here: the tools that check and maintain the repository, and numerical
cross-checks. Neither is part of the library, and nothing in `Lightlike/` depends on them.

## Checks run by CI

| File | What it checks |
|---|---|
| `AxiomAudit.lean` | every declaration of the library uses only the standard axioms |
| `ci_check.py` | no `sorry` and similar in `Lightlike/`; every file imported by `Lightlike.lean`; nothing imports `Exploratory/` |
| `DocCheck.lean` | docstrings of definitions and of the declarations the catalog names |
| `NameCheck.lean` | every name in an API map or in `docs/results.yaml` exists, in the file it is cited with |
| `doc_refs_check.py` | every file path in a Lean comment or a numerical cross-check exists; no comment calls a proven theorem open |
| `proof_task_check.py` | a proof-task pull request changes only the proof of its declaration |
| `tooling_selftest.py` | each check above fails on a planted bad case |
| `run_python_checks.py` | runs the numerical cross-checks below |

`gate.py` runs the steps of `.github/workflows/ci.yml` locally, in order.

## Maintainer tools

| File | What it does |
|---|---|
| `tasks.py` | the task list and its dependencies; writes the task board, `Tasks.lean` and the counts in `ROADMAP.md`; `sync` keeps the task issues' labels current (run by `.github/workflows/tasks.yml`) |
| `api_map.py` | checks the API maps and the results registry (`docs/results.yaml`, new entries in `docs/results.d/`); writes `docs/RESULTS.md`; `combine` joins the new entries at merge |
| `generated.py` | refuses a pull request that changes generated content; `reset` undoes such a change |
| `sources.py` | looks up the literature sources at their publishers; the offline `check` runs in CI |
| `context-pack`, `ContextPack.lean` | print everything one declaration depends on, as a single block |
| `templates/proof-task-issue.md` | the issue text of a proof task, filled in by `tasks.py` |
| `prune_docs.py` | shrinks the generated API documentation for GitHub Pages |
| `leansrc.py`, `sixj_support.py` | helpers shared by the scripts above and the cross-checks |
| `deprecation_baseline.txt` | the deprecation warnings of the build that `ci_check.py` tolerates |

## Numerical cross-checks

The other files, at the top level and in the folders by area (`asymptotics/`, `lorentz/`,
`oscillatory/`, `pl/`, `recoupling/`, `regge/`, `spin4/`, `spinfoam/`), compute numerically what a
Lean definition or theorem says, with pinned package versions (`requirements.txt`), and a
deliberately wrong input that must fail. They are evidence, not proofs: a docstring that says a
value was "checked numerically" names the script. Run them all with
`python3 scripts/run_python_checks.py --all`.
