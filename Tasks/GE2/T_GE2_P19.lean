import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Task T-GE2-P19

A curve with timelike velocity almost everywhere, without a margin, still joins its endpoints in the
timelike future.

The statement is `Lightlike.Causal.mem_chronFuture_of_ae_timelike`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Open. The library's timelike curves carry a margin (the velocity stays in a closed cone
strictly inside the timelike cone on compact intervals); the textbooks ask only for timelike
velocity. The statement says the two definitions give the same chronological future. Approach:
approximate the curve by piecewise-smooth timelike curves with margin in a convex chart
neighbourhood.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`,
  `Causal.TimeOrientation.IsFutureTimelike`
* `Lightlike/Spacetime/Causal/CausalCurve.lean`: `Causal.IsCurveWith`
* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.chronFuture`

Lemmas about them, which a proof may use:

* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.chron_subset_causal` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.exists_margin_of_contMDiffOn` (`Lightlike/Spacetime/Causal/CurveMargin.lean`)
* `Causal.isFutureTimelikeCurve_of_margin` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.isFutureTimelikeCurve_of_contMDiffOn` (`Lightlike/Spacetime/Causal/CurveMargin.lean`)
* `Causal.TimeOrientation.isFutureTimelike_of_with` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.TimeOrientation.isFutureCausal_of_isFutureTimelike` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.mem_chronFuture_of_ae_timelike

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

/-- **Timelike velocity almost everywhere is enough for `I⁺`.** If a curve from `x` to `y` on
`[a, b]` has future-directed timelike velocity almost everywhere (no margin), then `y ∈ I⁺(x)`. -/
theorem mem_chronFuture_of_ae_timelike {x y : M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelike v) γ (Icc a b))
    (hx : γ a = x) (hy : γ b = y) : y ∈ chronFuture T x := by
  sorry

end Lightlike.Causal
