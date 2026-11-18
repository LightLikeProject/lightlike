import Lightlike.Spacetime.Causal.CauchyDomain
import Lightlike.Spacetime.Causal.CurveGlobal
import Lightlike.Spacetime.Causal.CurveOps

/-!
# A curve through a descending chain of timelike pieces

If `q k ∈ I⁺(q (k + 1))` for all `k`, the points `q k` lie on one future-directed timelike curve `G`:
`G (β k) = q k` for parameters `β k` decreasing from `β 0 = 0`, and `G` is timelike on each
`[β (K + 1), 0]` (`exists_chain_curve`). The pieces come from the definition of `I⁺` and are placed by
translation of the parameter (`IsFutureTimelikeCurve.shift`) on consecutive intervals, so only
translations are needed.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Translation of the parameter of a timelike curve.** -/
theorem IsFutureTimelikeCurve.shift {γ : ℝ → M} {a b : ℝ} (h : IsFutureTimelikeCurve T γ (Icc a b))
    (hab : a < b) (k : ℝ) : IsFutureTimelikeCurve T (fun t => γ (t + k)) (Icc (a - k) (b - k)) := by
  obtain ⟨ε, hε, hm⟩ := h.2 a b hab subset_rfl
  exact isFutureTimelikeCurve_of_margin T hε (hm.shift hab k)

end Lightlike.Causal
