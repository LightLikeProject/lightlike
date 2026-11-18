import Lightlike.Spacetime.Causal.SmoothOrientation

/-!
# Task T-GE2-P17

A continuous time orientation can be replaced by a smooth one.

The statement is `Lightlike.Causal.exists_smooth_timeOrientation`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Smooth partition of unity subordinate to charts where a constant timelike field is
future-directed; convex combinations of future-directed timelike vectors stay in the cone.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`, `LorentzianMetric.g`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`,
  `Causal.TimeOrientation.X`

Lemmas about them, which a proof may use:

* `Causal.exists_smooth_field` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exists_reparam_bound` (`Lightlike/Spacetime/CausalLadder/LimitBound.lean`)
* `Causal.TimeOrientation.timelike` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)
* `Causal.exists_functional_estimate` (`Lightlike/Spacetime/CausalLadder/FunctionalEstimate.lean`)
* `Causal.isFutureCausal_of_forall_nonpos` (`Lightlike/Spacetime/CausalLadder/ChartCurve.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.TimeOrientation.mk.inj` (`Lightlike/Spacetime/Causal/TimeOrientation.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.exists_smooth_timeOrientation

## References

Milestone GE2 (Causal structure), ROADMAP section "Lorentzian and Riemannian geometry".
Source: S. W. Hawking and G. F. R. Ellis, The Large Scale Structure of Space-Time, Cambridge
University Press (1973), Chapter: Causal structure (`hawking-ellis-1973` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A continuous time orientation can be replaced by a smooth one.** -/
theorem exists_smooth_timeOrientation [T2Space M] [SecondCountableTopology M]
    [FiniteDimensional ℝ E] :
    ∃ X' : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) x (X' x)) ∧
      ∀ x, g.g x (X' x) (X' x) < 0 ∧ g.g x (X' x) (T.X x) < 0 := by
  exact exists_smooth_field T

end Lightlike.Causal
