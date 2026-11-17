import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Task T-GE2-P19

A curve with timelike velocity almost everywhere, without a margin, still joins its endpoints in the
timelike future.

The statement is `Lightlike.Causal.mem_chronFuture_of_ae_timelike`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. This is open. The library's `IsFutureTimelikeCurve` asks, besides a timelike velocity almost
everywhere, for a margin on compact intervals (a difference of form from the textbooks, approved by
the maintainers on 17 November 2026). The statement is that dropping the margin does not change
`I⁺`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Causal/CausalCurve.lean`: `Causal.IsCurveWith`
* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.chronFuture`

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
