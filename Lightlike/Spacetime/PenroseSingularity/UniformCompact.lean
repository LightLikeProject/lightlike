import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# A compactness step for local uniform bounds in a parameter (G1-012, step D4)

If at every point `t` of a compact interval a property holds for `0 < |s| < δ_t` and all `t'` near `t`, then one
`δ` works on the whole interval.
-/

open Set Filter Topology

namespace Lightlike.Penrose

/-- **Local `δ` on a neighbourhood of every point of a compact interval gives one `δ` on the interval.** -/
theorem exists_uniform_delta {P : ℝ → ℝ → Prop} {a b : ℝ}
    (h : ∀ t ∈ Icc a b, ∃ δ > 0, ∃ ε > 0, ∀ u, |u - t| < ε → ∀ s, |s| < δ → s ≠ 0 → P s u) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s, |s| < δ → s ≠ 0 → P s t := by
  choose! δ hδ ε hε hP using h
  have hopen : ∀ t ∈ Icc a b, ∃ U ∈ 𝓝 t, ∀ t' ∈ U, ∀ s, |s| < δ t → s ≠ 0 → P s t' := fun t ht =>
    ⟨Metric.ball t (ε t), Metric.ball_mem_nhds t (hε t ht), fun t' ht' s hs hs0 =>
      hP t ht t' (by simpa [Real.dist_eq] using ht') s hs hs0⟩
  -- compactness: finitely many balls cover
  have hcov : Icc a b ⊆ ⋃ t ∈ Icc a b, Metric.ball t (ε t) := fun t ht =>
    mem_iUnion₂.2 ⟨t, ht, Metric.mem_ball_self (hε t ht)⟩
  obtain ⟨T, hTsub, hTfin, hTcov⟩ := isCompact_Icc.elim_finite_subcover_image
    (fun t ht => Metric.isOpen_ball) hcov
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    exfalso
    have := hTcov ht
    simp [hT] at this
  · obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ > 0, ∀ t ∈ T, δ₀ ≤ δ t := by
      have hfin := hTfin
      refine ⟨hfin.toFinset.inf' (by simpa using hT) δ, ?_, fun t ht => ?_⟩
      · rw [gt_iff_lt, Finset.lt_inf'_iff]
        intro t ht
        exact hδ t (hTsub (by simpa using ht))
      · exact Finset.inf'_le _ (by simpa using ht)
    refine ⟨δ₀, hδ₀pos, fun t ht s hs hs0 => ?_⟩
    obtain ⟨c, hc, hct⟩ := mem_iUnion₂.1 (hTcov ht)
    exact hP c (hTsub hc) t (by simpa [Real.dist_eq] using hct) s
      (lt_of_lt_of_le hs (hδ₀ c hc)) hs0

end Lightlike.Penrose
