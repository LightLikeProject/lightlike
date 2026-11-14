# Changelog

Notable changes to Lightlike. Results are identified by stable IDs (`LL-NNNN`), listed with their
sources and review status in [docs/RESULTS.md](docs/RESULTS.md). Versions follow
[Semantic Versioning](https://semver.org/); before 1.0.0, minor versions may change the API.

## [0.1.0]

First public release.

### Library

- 44 proven results, 1 conditional result (proven under named hypotheses) and 2 stated targets,
  in eight areas: harmonic analysis on Lie groups (16 proven); Lorentzian and Riemannian geometry
  (5); oscillatory and saddle-point asymptotics (2 proven, 1 stated target); operator algebras
  and quantum information (1); PL topology (3); quantum groups and state-sum TQFTs (6 proven,
  1 conditional, 1 stated target); Regge calculus (5); spin foams (6).
- `scripts/AxiomAudit.lean` checks the axioms of every declaration of the library; CI accepts only
  `propext`, `Classical.choice` and `Quot.sound`.

### Open work

- 27 areas in [ROADMAP.md](ROADMAP.md), each divided into milestones with their canonical sources
  ([docs/tasks/milestones.md](docs/tasks/milestones.md)).
- 226 tasks on the [task board](docs/tasks/README.md), including proof tasks whose statements are
  fixed in `Tasks/`, and candidates for Mathlib and Physlib.

### Checks

- CI hard rules: build, no `sorry`, the axiom audit of every declaration, docstrings, and the
  literature sources of the catalog. Advisory: the API maps, the task board, a self-test of the
  checks and the numerical cross-checks.
