import Lightlike.Spacetime.Causal.MinkowskiFuture

/-!
# Task T-GE2-P14

The causal future in Minkowski space is the closed light cone.

The statement is `Lightlike.Causal.minkowski_causalFuture`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. `⊇` by a straight line (`isFutureCausalCurve_line`-type lemma); `⊆` by integrating the
velocity of a Lipschitz curve (absolutely continuous) and the reverse triangle inequality of the
cone.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.causalFuture`
* `Lightlike/Spacetime/Minkowski.lean`: `minkowskiMetric`, `minkowskiForm`
* `Lightlike/Spacetime/Causal/MinkowskiCausal.lean`: `Causal.minkowskiOrientation`

Lemmas about them, which a proof may use:

* `Causal.line_mem_chronFuture` (`Lightlike/Spacetime/Causal/MinkowskiCausal.lean`)
* `Causal.isFutureTimelikeCurve_line` (`Lightlike/Spacetime/Causal/MinkowskiCausal.lean`)
* `Causal.form_e1` (`Lightlike/Spacetime/Causal/TestsMinkowski.lean`)
* `minkowski_flat` (`Lightlike/Spacetime/Curvature.lean`)
* `Causal.form_e0` (`Lightlike/Spacetime/Causal/TestsMinkowski.lean`)
* `minkowskiForm_eq` (`Lightlike/Spacetime/Minkowski.lean`)
* `minkowskiForm_apply` (`Lightlike/Spacetime/Minkowski.lean`)
* `minkowskiForm_single` (`Lightlike/Spacetime/Minkowski.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.minkowski_causalFuture

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

variable {d : ℕ}

/-- **The causal future in Minkowski space is the closed light cone.** -/
theorem minkowski_causalFuture (x : Fin (d + 1) → ℝ) :
    causalFuture (minkowskiOrientation d) x =
      {y | 0 ≤ (y - x) 0 ∧ minkowskiForm (d + 1) (y - x) (y - x) ≤ 0} := by
  exact minkowski_causalFuture_eq x

end Lightlike.Causal
