import Mathlib
import Lightlike.Geometry.HeatKernel.Theta

/-!
# Uniform decay of `e^{-c/t}` on `(0, 1]`

For `c > 0` and any real `s` there is `C` with `e^{-c/t} ≤ C t^s` for all `t ∈ (0, 1]`
(`exists_exp_neg_div_le_rpow`): the little-o statement `Lightlike.HeatKernel.exp_neg_div_isLittleO` near `0`, and
the bound `e^{-c/t} ≤ 1 ≤ C tˢ` on `[ε, 1]`. This makes the terms of
the heat-kernel parametrix supported away from the diagonal, where `σ ≥ c > 0`, smaller than every power of `t`.
-/

open Set Filter Asymptotics
open scoped Topology

noncomputable section

namespace Lightlike

/-- **`e^{-c/t} ≤ C tˢ` uniformly on `(0, 1]`.** -/
theorem exists_exp_neg_div_le_rpow {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, Real.exp (-c / t) ≤ C * t ^ s := by
  have ho := (HeatKernel.exp_neg_div_isLittleO hc s).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 ho)
  set ε' := min (ε / 2) 1 with hε'
  have hε'pos : 0 < ε' := lt_min (half_pos hε) one_pos
  refine ⟨max 1 (ε' ^ (-s) + ε' ^ s + 1) , by positivity, fun t ht => ?_⟩
  by_cases hts : t < ε'
  · have htb : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht.1]
      exact lt_of_lt_of_le hts ((min_le_left _ _).trans (by linarith))
    have h := hεb t htb ht.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos ht.1 s), one_mul] at h
    calc Real.exp (-c / t) ≤ t ^ s := h
      _ ≤ max 1 (ε' ^ (-s) + ε' ^ s + 1) * t ^ s :=
        le_mul_of_one_le_left (Real.rpow_pos_of_pos ht.1 s).le (le_max_left _ _)
  · push_neg at hts
    -- on `[ε', 1]`: `e^{-c/t} ≤ 1` and `t^s ≥ min(ε'^s, 1)`
    have he : Real.exp (-c / t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; exact (div_neg_of_neg_of_pos (neg_neg_of_pos hc) ht.1).le
    have hts' : 0 < t ^ s := Real.rpow_pos_of_pos ht.1 s
    have hlow : 1 ≤ (ε' ^ (-s) + ε' ^ s + 1) * t ^ s := by
      rcases le_or_gt 0 s with hs | hs
      · have h1 : ε' ^ s ≤ t ^ s := Real.rpow_le_rpow hε'pos.le hts hs
        have h2 : ε' ^ (-s) * ε' ^ s = 1 := by
          rw [← Real.rpow_add hε'pos]; simp
        have h3 : 0 ≤ ε' ^ (-s) := (Real.rpow_pos_of_pos hε'pos _).le
        nlinarith [Real.rpow_pos_of_pos hε'pos s]
      · have h1 : 1 ≤ t ^ s := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 hs.le
        nlinarith [Real.rpow_pos_of_pos hε'pos s, Real.rpow_pos_of_pos hε'pos (-s)]
    calc Real.exp (-c / t) ≤ 1 := he
      _ ≤ (ε' ^ (-s) + ε' ^ s + 1) * t ^ s := hlow
      _ ≤ max 1 (ε' ^ (-s) + ε' ^ s + 1) * t ^ s :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hts'.le

end Lightlike
