module

public import Mathlib

/-!
# Physical assumptions

The physical postulates of the models in Lightlike, and how the library encodes them. This file
declares nothing. No file of the library declares an `axiom`, this one included:
`scripts/ci_check.py` rejects an `axiom` declaration anywhere in `Lightlike/` (CONTRIBUTING.md,
hard rule 2), and `scripts/AxiomAudit.lean` checks that every declaration depends only on Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound` (hard rule 3).

A physical postulate enters the library as the definition of a model, and a theorem says what
follows from that definition:

* **Spacetime.** Spacetime is a smooth 4-manifold with a Lorentzian metric
  (`Lightlike.LorentzianMetric`). In Minkowski space, the time a free clock measures along its
  worldline is the proper time `Lightlike.properTime`.
* **Field equations.** In vacuum the metric satisfies `G_{μν} + Λ g_{μν} = 0`
  (`Lightlike.IsVacuumSolution`). The theorems say which metrics satisfy it, not that the metric of
  spacetime does.
* **Quantum postulates.** States are unit vectors, observables are self-adjoint operators,
  closed-system time evolution is `exp(-i t H)`, and the outcome `λ` of a measurement has
  probability `‖P_λ ψ‖²` (the Born rule). These are definitions; the theorems include that the Born
  probabilities of a state sum to 1 (`Lightlike.QM.sum_bornProb`) and that time evolution preserves
  the norm (`Lightlike.QM.norm_evolve`). That observed frequencies equal Born probabilities is an
  empirical claim, not a mathematical statement, and is not formalized.
* **Ponzano–Regge model.** That the Ponzano–Regge state sum is a model of 3D Euclidean quantum
  gravity is a physical interpretation (through the asymptotics of 6j symbols, which approach the
  Regge action); it is not formalized.
-/

@[expose] public section
