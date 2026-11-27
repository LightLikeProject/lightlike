import Mathlib
import Lightlike.Geometry.HeatKernel.FrozenGaussian

/-!
# Comparison of the cut-off parametrix with the frozen Gaussian

Pointwise, for `z = y − p`, `t ∈ (0, 1]` and `u = c‖z‖²/4t`: if the cutoff `θ` is `1` for `‖z‖ < r/2` and `0` for
`‖z‖ ≥ r`, `|θ| ≤ 1`, the world function `σ` and the frozen form `q` are both `≥ c‖z‖²` with `|σ − q| ≤ C₁‖z‖³`, and
the coefficient sum `U` satisfies `|U − 1| ≤ C₂(‖z‖ + t)` (all for `‖z‖ < r`), then

`|θ e^{-σ/4t} U − e^{-q/4t}| ≤ K √t e^{-c‖z‖²/8t}`   (`cutoffGauss_sub_frozen_le`),

with `K` depending only on `c, r, C₁, C₂`. The three parts: `θ (e^{-σ/4t} − e^{-q/4t}) U` (`|e^x − e^y| ≤ e^{max}|x − y|`
and the third moment `u√u e^{-u} ≤ 8 e^{-u/2}`), `θ e^{-q/4t} (U − 1)` (the first moment `√u e^{-u} ≤ e^{-u/2}`), and
`(θ − 1) e^{-q/4t}`, supported in `‖z‖ ≥ r/2` (the second moment `u e^{-u} ≤ 2 e^{-u/2}`).
-/

open Set Real

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- `|eˣ − eʸ| ≤ e^{max x y} |x − y|`. -/
theorem abs_exp_sub_exp_le (x y : ℝ) : |Real.exp x - Real.exp y| ≤ Real.exp (max x y) * |x - y| := by
  have key : ∀ a b : ℝ, a ≤ b → Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
    intro a b hab
    have h1 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by have := Real.add_one_le_exp (-(b - a)); linarith
    have h2 : Real.exp b * Real.exp (-(b - a)) = Real.exp a := by rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos b]
  rcases le_total x y with h | h
  · rw [abs_sub_comm (Real.exp x), abs_sub_comm x y,
      abs_of_nonneg (by linarith [Real.exp_le_exp.2 h] : 0 ≤ Real.exp y - Real.exp x),
      max_eq_right h, abs_of_nonneg (by linarith : 0 ≤ y - x)]
    exact key x y h
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h] : 0 ≤ Real.exp x - Real.exp y),
      max_eq_left h, abs_of_nonneg (by linarith : 0 ≤ x - y)]
    exact key y x h

/-- **The pointwise comparison** of the cut-off parametrix integrand with the frozen Gaussian. -/
theorem cutoffGauss_sub_frozen_le {t c r C₁ C₂ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hr : 0 < r)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) {z : Fin n → ℝ} {θv σv qv Uv : ℝ} (hθb : |θv| ≤ 1)
    (hθ1 : ‖z‖ < r / 2 → θv = 1) (hθ0 : r ≤ ‖z‖ → θv = 0) (hσ : ‖z‖ < r → c * ‖z‖ ^ 2 ≤ σv)
    (hq : c * ‖z‖ ^ 2 ≤ qv) (hσq : ‖z‖ < r → |σv - qv| ≤ C₁ * ‖z‖ ^ 3)
    (hU : ‖z‖ < r → |Uv - 1| ≤ C₂ * (‖z‖ + t)) :
    |θv * Real.exp (-σv / (4 * t)) * Uv - Real.exp (-qv / (4 * t))| ≤
      ((1 + C₂ * (r + 1)) * C₁ * 2 * √(4 / c) ^ 3 + C₂ * (√(4 / c) + 1) + 64 / (r ^ 2 * c)) * √t *
        Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by
  set u := c * ‖z‖ ^ 2 / (4 * t) with hu
  have hu0 : 0 ≤ u := by positivity
  have hst : 0 ≤ √t := Real.sqrt_nonneg t
  have htst : t ≤ √t := by
    have h1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have h2 := Real.mul_self_sqrt ht.le
    nlinarith [Real.sqrt_nonneg t]
  have hE : 0 < Real.exp (-u / 2) := Real.exp_pos _
  have hz0 := norm_nonneg z
  -- `‖z‖ = √(4/c) √t √u`
  have hzu : ‖z‖ = √(4 / c) * √t * √u := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity), hu]
    rw [show 4 / c * t * (c * ‖z‖ ^ 2 / (4 * t)) = ‖z‖ ^ 2 by field_simp]
    exact (Real.sqrt_sq hz0).symm
  have hz2 : ‖z‖ ^ 2 = 4 / c * t * u := by rw [hu]; field_simp
  have hqe : Real.exp (-qv / (4 * t)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.2; rw [hu, neg_div, neg_le_neg_iff]; gcongr
  -- the far term: `e^{-u} ≤ (64/(r²c)) √t e^{-u/2}` where `‖z‖ ≥ r/2`
  have hfar : r / 2 ≤ ‖z‖ → Real.exp (-u) ≤ 32 / (r ^ 2 * c) * √t * Real.exp (-u / 2) := by
    intro hz
    have h1 : 1 ≤ ‖z‖ ^ 2 / (r / 2) ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ (by positivity) hz 2
    calc Real.exp (-u) ≤ ‖z‖ ^ 2 / (r / 2) ^ 2 * Real.exp (-u) := le_mul_of_one_le_left (Real.exp_pos _).le h1
      _ = 16 / (r ^ 2 * c) * t * (u * Real.exp (-u)) := by rw [hz2]; field_simp; ring
      _ ≤ 16 / (r ^ 2 * c) * t * (2 * Real.exp (-u / 2)) :=
          mul_le_mul_of_nonneg_left (mul_exp_neg_le u hu0) (by positivity)
      _ = 32 / (r ^ 2 * c) * t * Real.exp (-u / 2) := by ring
      _ ≤ 32 / (r ^ 2 * c) * √t * Real.exp (-u / 2) := by gcongr
  set K := (1 + C₂ * (r + 1)) * C₁ * 2 * √(4 / c) ^ 3 + C₂ * (√(4 / c) + 1) + 64 / (r ^ 2 * c) with hK
  have hK1 : 0 ≤ (1 + C₂ * (r + 1)) * C₁ * 2 * √(4 / c) ^ 3 := by positivity
  have hK2 : 0 ≤ C₂ * (√(4 / c) + 1) := by positivity
  have hK3 : 0 ≤ 64 / (r ^ 2 * c) := by positivity
  by_cases hzr : ‖z‖ < r
  · -- near the diagonal: the three parts
    have hUb : |Uv| ≤ 1 + C₂ * (r + 1) := by
      have h1 := hU hzr
      have h2 : |Uv| ≤ |Uv - 1| + 1 := by
        have := abs_add_le (Uv - 1) 1; simpa using this
      have : C₂ * (‖z‖ + t) ≤ C₂ * (r + 1) := by gcongr <;> linarith
      linarith
    have hsplit : θv * Real.exp (-σv / (4 * t)) * Uv - Real.exp (-qv / (4 * t)) =
        θv * (Real.exp (-σv / (4 * t)) - Real.exp (-qv / (4 * t))) * Uv +
          θv * Real.exp (-qv / (4 * t)) * (Uv - 1) + (θv - 1) * Real.exp (-qv / (4 * t)) := by ring
    -- part 1
    have hmax : max (-σv / (4 * t)) (-qv / (4 * t)) ≤ -u := by
      apply max_le
      · rw [hu, neg_div, neg_le_neg_iff]; gcongr; exact hσ hzr
      · rw [hu, neg_div, neg_le_neg_iff]; gcongr
    have hd : |Real.exp (-σv / (4 * t)) - Real.exp (-qv / (4 * t))| ≤ Real.exp (-u) * (C₁ * ‖z‖ ^ 3 / (4 * t)) := by
      refine (abs_exp_sub_exp_le _ _).trans
        (mul_le_mul (Real.exp_le_exp.2 hmax) ?_ (abs_nonneg _) (Real.exp_pos _).le)
      · rw [show -σv / (4 * t) - -qv / (4 * t) = -(σv - qv) / (4 * t) by ring, abs_div, abs_neg,
          abs_of_pos (by positivity : (0 : ℝ) < 4 * t)]
        gcongr; exact hσq hzr
    have hz3 : C₁ * ‖z‖ ^ 3 / (4 * t) = C₁ * √(4 / c) ^ 3 / 4 * √t * (u * √u) := by
      have h4t : √t * √t = t := Real.mul_self_sqrt ht.le
      have hu' : √u * √u = u := Real.mul_self_sqrt hu0
      rw [hzu, mul_pow, mul_pow, show √t ^ 3 = t * √t by rw [pow_succ, sq, h4t],
        show √u ^ 3 = u * √u by rw [pow_succ, sq, hu']]
      field_simp
    have hEu : Real.exp (-u) ≤ Real.exp (-u / 2) := Real.exp_le_exp.2 (by linarith)
    have hqe0 : 0 ≤ Real.exp (-qv / (4 * t)) := (Real.exp_pos _).le
    -- the three bounds
    have p1 : |θv * (Real.exp (-σv / (4 * t)) - Real.exp (-qv / (4 * t))) * Uv| ≤
        (1 + C₂ * (r + 1)) * C₁ * 2 * √(4 / c) ^ 3 * √t * Real.exp (-u / 2) := by
      rw [abs_mul, abs_mul]
      calc |θv| * |Real.exp (-σv / (4 * t)) - Real.exp (-qv / (4 * t))| * |Uv|
          ≤ 1 * (Real.exp (-u) * (C₁ * ‖z‖ ^ 3 / (4 * t))) * (1 + C₂ * (r + 1)) := by gcongr
        _ = (1 + C₂ * (r + 1)) * (C₁ * √(4 / c) ^ 3 / 4) * √t * (u * √u * Real.exp (-u)) := by
            rw [hz3]; ring
        _ ≤ (1 + C₂ * (r + 1)) * (C₁ * √(4 / c) ^ 3 / 4) * √t * (8 * Real.exp (-u / 2)) :=
            mul_le_mul_of_nonneg_left (mul_sqrt_mul_exp_neg_le u hu0) (by positivity)
        _ = _ := by ring
    have p2 : |θv * Real.exp (-qv / (4 * t)) * (Uv - 1)| ≤ C₂ * (√(4 / c) + 1) * √t * Real.exp (-u / 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hqe0]
      have hsu := sqrt_mul_exp_neg_le u hu0
      calc |θv| * Real.exp (-qv / (4 * t)) * |Uv - 1| ≤ 1 * Real.exp (-u) * (C₂ * (‖z‖ + t)) := by
            gcongr; exact hU hzr
        _ = C₂ * (√(4 / c) * √t * (√u * Real.exp (-u)) + t * Real.exp (-u)) := by rw [hzu]; ring
        _ ≤ C₂ * (√(4 / c) * √t * Real.exp (-u / 2) + √t * Real.exp (-u / 2)) := by gcongr
        _ = _ := by ring
    have p3 : |(θv - 1) * Real.exp (-qv / (4 * t))| ≤ 64 / (r ^ 2 * c) * √t * Real.exp (-u / 2) := by
      by_cases hzh : ‖z‖ < r / 2
      · rw [hθ1 hzh, sub_self, zero_mul, abs_zero]; positivity
      · push Not at hzh
        rw [abs_mul, abs_of_nonneg hqe0]
        have h1 : |θv - 1| ≤ 2 := by
          have := abs_add_le θv (-1); rw [abs_neg, abs_one, ← sub_eq_add_neg] at this; linarith
        calc |θv - 1| * Real.exp (-qv / (4 * t)) ≤ 2 * (32 / (r ^ 2 * c) * √t * Real.exp (-u / 2)) := by
              gcongr; exact hqe.trans (hfar hzh)
          _ = _ := by ring
    rw [hsplit]
    calc _ ≤ |θv * (Real.exp (-σv / (4 * t)) - Real.exp (-qv / (4 * t))) * Uv| +
          |θv * Real.exp (-qv / (4 * t)) * (Uv - 1)| + |(θv - 1) * Real.exp (-qv / (4 * t))| := abs_add_three _ _ _
      _ ≤ _ := add_le_add (add_le_add p1 p2) p3
      _ = K * √t * Real.exp (-u / 2) := by rw [hK]; ring
  · -- away from the support: `θ = 0`
    push Not at hzr
    rw [hθ0 hzr, zero_mul, zero_mul, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-qv / (4 * t)) ≤ Real.exp (-u) := hqe
      _ ≤ 32 / (r ^ 2 * c) * √t * Real.exp (-u / 2) := hfar (by linarith)
      _ ≤ K * √t * Real.exp (-u / 2) := by
          gcongr
          rw [hK]
          have : 32 / (r ^ 2 * c) ≤ 64 / (r ^ 2 * c) := by gcongr; norm_num
          linarith

/-- Away from the diagonal the Gaussian factor is `O(√t)` times a wider Gaussian: for `r' ≤ ‖z‖`,
`e^{-u} ≤ (32/(r'²c)) √t e^{-u/2}` with `u = c‖z‖²/4t`, `t ∈ (0, 1]`. -/
theorem exp_neg_le_of_far {t c r' : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hr' : 0 < r') {z : Fin n → ℝ}
    (hz : r' ≤ ‖z‖) :
    Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) ≤ 32 / (r' ^ 2 * c) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by
  set u := c * ‖z‖ ^ 2 / (4 * t) with hu
  have hu0 : 0 ≤ u := by positivity
  have htst : t ≤ √t := by
    have h1 : √t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have h2 := Real.mul_self_sqrt ht.le
    nlinarith [Real.sqrt_nonneg t]
  have hz2 : ‖z‖ ^ 2 = 4 / c * t * u := by rw [hu]; field_simp
  have h1 : 1 ≤ ‖z‖ ^ 2 / r' ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hr'.le hz 2
  calc Real.exp (-u) ≤ ‖z‖ ^ 2 / r' ^ 2 * Real.exp (-u) := le_mul_of_one_le_left (Real.exp_pos _).le h1
    _ = 4 / (r' ^ 2 * c) * t * (u * Real.exp (-u)) := by rw [hz2]; field_simp
    _ ≤ 4 / (r' ^ 2 * c) * t * (2 * Real.exp (-u / 2)) :=
        mul_le_mul_of_nonneg_left (mul_exp_neg_le u hu0) (by positivity)
    _ = 8 / (r' ^ 2 * c) * t * Real.exp (-u / 2) := by ring
    _ ≤ 8 / (r' ^ 2 * c) * √t * Real.exp (-u / 2) := by gcongr
    _ ≤ 32 / (r' ^ 2 * c) * √t * Real.exp (-u / 2) := by
        gcongr; norm_num

/-- **The pointwise comparison with two radii**: the Taylor bound and the bound on `U − 1` only for `‖z‖ < r_b`,
the lower bound on `σ` and `|U| ≤ A` for `‖z‖ < r` (the support of the cutoff), `r_b ≤ r`. -/
theorem cutoffGauss_sub_frozen_le₂ {t c r rb C₁ C₂ A : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c)
    (hrb : 0 < rb) (hrbr : rb ≤ r) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hA : 0 ≤ A) {z : Fin n → ℝ} {θv σv qv Uv : ℝ}
    (hθb : θv ∈ Icc (0 : ℝ) 1) (hθ1 : ‖z‖ < r / 2 → θv = 1) (hθ0 : r ≤ ‖z‖ → θv = 0)
    (hσ : ‖z‖ < r → c * ‖z‖ ^ 2 ≤ σv) (hq : c * ‖z‖ ^ 2 ≤ qv) (hσq : ‖z‖ < rb → |σv - qv| ≤ C₁ * ‖z‖ ^ 3)
    (hU : ‖z‖ < rb → |Uv - 1| ≤ C₂ * (‖z‖ + t)) (hUA : ‖z‖ < r → |Uv| ≤ A) :
    |θv * Real.exp (-σv / (4 * t)) * Uv - Real.exp (-qv / (4 * t))| ≤
      (((1 + C₂ * (rb + 1)) * C₁ * 2 * √(4 / c) ^ 3 + C₂ * (√(4 / c) + 1) + 64 / (rb ^ 2 * c)) +
        (A + 1) * (32 / (rb ^ 2 * c))) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by
  set K₀ := (1 + C₂ * (rb + 1)) * C₁ * 2 * √(4 / c) ^ 3 + C₂ * (√(4 / c) + 1) + 64 / (rb ^ 2 * c) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hK₁0 : 0 ≤ (A + 1) * (32 / (rb ^ 2 * c)) := by positivity
  have hE0 : 0 ≤ √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by positivity
  have hθabs : |θv| ≤ 1 := by rw [abs_of_nonneg hθb.1]; exact hθb.2
  have hqe : Real.exp (-qv / (4 * t)) ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
    apply Real.exp_le_exp.2; rw [neg_div, neg_le_neg_iff]; gcongr
  by_cases hnear : ‖z‖ < rb
  · -- the near region: the one-radius comparison at radius `rb`
    have h := cutoffGauss_sub_frozen_le ht ht1 hc hrb hC₁ hC₂ hθabs
      (fun h => hθ1 (lt_of_lt_of_le h (by linarith))) (fun h => absurd hnear (not_lt.2 h))
      (fun h => hσ (lt_of_lt_of_le h hrbr)) hq hσq hU
    calc _ ≤ K₀ * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := h
      _ ≤ _ := by nlinarith [mul_nonneg hK₁0 hE0]
  · push Not at hnear
    have hfar := exp_neg_le_of_far ht ht1 hc hrb hnear
    by_cases hin : ‖z‖ < r
    · -- the middle region: both terms are Gaussian-small
      have hσe : Real.exp (-σv / (4 * t)) ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
        apply Real.exp_le_exp.2; rw [neg_div, neg_le_neg_iff]; gcongr; exact hσ hin
      have h1 : |θv * Real.exp (-σv / (4 * t)) * Uv - Real.exp (-qv / (4 * t))| ≤
          (A + 1) * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
        have h2 := abs_add_le (θv * Real.exp (-σv / (4 * t)) * Uv) (-Real.exp (-qv / (4 * t)))
        rw [abs_neg, ← sub_eq_add_neg, abs_of_pos (Real.exp_pos _)] at h2
        have h3 : |θv * Real.exp (-σv / (4 * t)) * Uv| ≤ A * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc |θv| * Real.exp (-σv / (4 * t)) * |Uv| ≤ 1 * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) * A := by
                gcongr; exact hUA hin
            _ = _ := by ring
        linarith
      calc _ ≤ (A + 1) * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := h1
        _ ≤ (A + 1) * (32 / (rb ^ 2 * c) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2)) := by gcongr
        _ = (A + 1) * (32 / (rb ^ 2 * c)) * (√t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2)) := by ring
        _ ≤ _ := by nlinarith [mul_nonneg hK₀0 hE0]
    · -- beyond the cutoff: `θ = 0`
      push Not at hin
      rw [hθ0 hin, zero_mul, zero_mul, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-qv / (4 * t)) ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := hqe
        _ ≤ 32 / (rb ^ 2 * c) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := hfar
        _ = 32 / (rb ^ 2 * c) * (√t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2)) := by ring
        _ ≤ _ := by
            have : 32 / (rb ^ 2 * c) ≤ (A + 1) * (32 / (rb ^ 2 * c)) :=
              le_mul_of_one_le_left (by positivity) (by linarith)
            nlinarith [mul_nonneg hK₀0 hE0, mul_le_mul_of_nonneg_right this hE0]

end Lightlike
