import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalCoeff

/-!
# The Harish-Chandra majorant of the principal-series matrix coefficients

Every matrix coefficient of the even principal series is dominated by the `ν`- and
`K`-type-independent function
`Ξ(ξ) = e^{ξ/2} ∫ (1 + x²)^{-1/2} (1 + e^{2ξ} x²)^{-1/2} dx` (`norm_mcoefP_le`): the integrand of
`Φ^ν_{m,n}(ξ)` has exactly this modulus, since `|e_k(x)| = (1 + x²)^{-1/2}` and `|e^{-wξ}| = e^{ξ/2}`.
Substituting `x = e^{-ξ} u` and bounding `(1 + e^{-2ξ} u²)^{-1/2} ≤ e^{ξ/4} (1 + u²)^{-1/8}` gives the
decay `Ξ(ξ) ≤ C e^{-ξ/4}` for `ξ ≥ 0`, `C = ∫ (1 + u²)^{-5/8} du` (`hcXi_le`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (decay of the matrix coefficients, for the
opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The majorant `Ξ(ξ) = e^{ξ/2} ∫ (1 + x²)^{-1/2} (1 + (e^ξ x)²)^{-1/2} dx`. -/
def hcXi (ξ : ℝ) : ℝ :=
  ∫ x : ℝ, (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * (Real.exp (ξ / 2) *
    (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2))

/-- **The Harish-Chandra majorant**: `|Φ^ν_{m,n}(ξ)| ≤ Ξ(ξ)` for every `ν, m, n`. -/
theorem norm_mcoefP_le (ν ξ : ℝ) (m n : ℤ) : ‖mcoefP ν m n ξ‖ ≤ hcXi ξ := by
  rw [mcoefP_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, norm_mul, RCLike.norm_conj, norm_kVecP, norm_exp_neg_wP, norm_kVecP]

/-- The constant `C = ∫ (1 + u²)^{-5/8} du` of the decay bound. -/
def hcConst : ℝ := ∫ u : ℝ, (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2)

lemma integrable_rpow_neg_five_eighths :
    Integrable fun u : ℝ => (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 5 / 4)
    (by simp; norm_num)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp [Real.norm_eq_abs, sq_abs]

/-- `Ξ(ξ) = e^{-ξ/2} ∫ (1 + u²)^{-1/2} (1 + (e^{-ξ} u)²)^{-1/2} du`. -/
lemma hcXi_eq (ξ : ℝ) :
    hcXi ξ = Real.exp (-ξ / 2) * ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 : ℝ) / 2) *
      (1 + (Real.exp (-ξ) * u) ^ 2) ^ (-(1 : ℝ) / 2) := by
  have h := Measure.integral_comp_mul_left
    (fun x : ℝ => (1 + x ^ 2) ^ (-(1 : ℝ) / 2) *
      (Real.exp (ξ / 2) * (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2))) (Real.exp (-ξ))
  rw [abs_of_pos (inv_pos.2 (Real.exp_pos _)), smul_eq_mul, ← Real.exp_neg, neg_neg] at h
  have hc : Real.exp (-ξ) * Real.exp ξ = 1 := by rw [← Real.exp_add]; simp
  have key : hcXi ξ = Real.exp (-ξ) * ∫ x : ℝ, (fun x : ℝ => (1 + x ^ 2) ^ (-(1 : ℝ) / 2) *
      (Real.exp (ξ / 2) * (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2))) (Real.exp (-ξ) * x) := by
    rw [h, ← mul_assoc, hc, one_mul]
    rfl
  rw [key, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext u
  beta_reduce
  rw [show Real.exp ξ * (Real.exp (-ξ) * u) = u by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]]
  have : Real.exp (-ξ) * Real.exp (ξ / 2) = Real.exp (-ξ / 2) := by rw [← Real.exp_add]; ring_nf
  rw [← this]
  ring

/-- **Exponential decay of the majorant**: `Ξ(ξ) ≤ C e^{-ξ/4}` for `ξ ≥ 0`. -/
theorem hcXi_le {ξ : ℝ} (hξ : 0 ≤ ξ) : hcXi ξ ≤ hcConst * Real.exp (-ξ / 4) := by
  rw [hcXi_eq]
  have hpt : ∀ u : ℝ, (1 + u ^ 2) ^ (-(1 : ℝ) / 2) * (1 + (Real.exp (-ξ) * u) ^ 2) ^ (-(1 : ℝ) / 2)
      ≤ Real.exp (ξ / 4) * (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2) := by
    intro u
    have h1 : (0 : ℝ) < 1 + u ^ 2 := by positivity
    set B := 1 + (Real.exp (-ξ) * u) ^ 2 with hB
    have hB1 : 1 ≤ B := by rw [hB]; nlinarith [sq_nonneg (Real.exp (-ξ) * u)]
    have he : Real.exp (-ξ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have he0 := Real.exp_pos (-ξ)
    have hBlow : Real.exp (-ξ) ^ 2 * (1 + u ^ 2) ≤ B := by
      rw [hB, mul_pow]
      nlinarith [sq_nonneg u, pow_le_one₀ he0.le he (n := 2), sq_nonneg (Real.exp (-ξ))]
    have hBpos : 0 < Real.exp (-ξ) ^ 2 * (1 + u ^ 2) := by positivity
    have s1 : B ^ (-(1 : ℝ) / 2) ≤ B ^ (-(1 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
    have s2 : B ^ (-(1 : ℝ) / 8) ≤ (Real.exp (-ξ) ^ 2 * (1 + u ^ 2)) ^ (-(1 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_nonpos hBpos hBlow (by norm_num)
    have s3 : (Real.exp (-ξ) ^ 2 * (1 + u ^ 2)) ^ (-(1 : ℝ) / 8) =
        Real.exp (ξ / 4) * (1 + u ^ 2) ^ (-(1 : ℝ) / 8) := by
      rw [Real.mul_rpow (by positivity) h1.le, ← Real.exp_nat_mul, ← Real.exp_mul]
      congr 2
      push_cast
      ring
    have s4 : (1 + u ^ 2) ^ (-(1 : ℝ) / 2) * (1 + u ^ 2) ^ (-(1 : ℝ) / 8) =
        (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2) := by
      rw [← Real.rpow_add h1]; norm_num
    calc (1 + u ^ 2) ^ (-(1 : ℝ) / 2) * B ^ (-(1 : ℝ) / 2)
        ≤ (1 + u ^ 2) ^ (-(1 : ℝ) / 2) * (Real.exp (ξ / 4) * (1 + u ^ 2) ^ (-(1 : ℝ) / 8)) := by
          gcongr
          rw [← s3]; exact s1.trans s2
      _ = Real.exp (ξ / 4) * (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2) := by rw [← s4]; ring
  have hmeas : Continuous fun u : ℝ => (1 + u ^ 2) ^ (-(1 : ℝ) / 2) *
      (1 + (Real.exp (-ξ) * u) ^ 2) ^ (-(1 : ℝ) / 2) := by
    refine ((continuous_const.add (continuous_pow 2)).rpow_const fun u => Or.inl ?_).mul
      ((continuous_const.add ((continuous_const.mul continuous_id).pow 2)).rpow_const
        fun u => Or.inl ?_)
    · exact (show (0 : ℝ) < 1 + u ^ 2 by positivity).ne'
    · exact (show (0 : ℝ) < 1 + (Real.exp (-ξ) * u) ^ 2 by positivity).ne'
  have hint : Integrable fun u : ℝ => (1 + u ^ 2) ^ (-(1 : ℝ) / 2) *
      (1 + (Real.exp (-ξ) * u) ^ 2) ^ (-(1 : ℝ) / 2) :=
    (integrable_rpow_neg_five_eighths.const_mul (Real.exp (ξ / 4))).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt u)
  calc Real.exp (-ξ / 2) * ∫ u : ℝ, (1 + u ^ 2) ^ (-(1 : ℝ) / 2) *
        (1 + (Real.exp (-ξ) * u) ^ 2) ^ (-(1 : ℝ) / 2)
      ≤ Real.exp (-ξ / 2) * ∫ u : ℝ, Real.exp (ξ / 4) * (1 + u ^ 2) ^ (-(5 / 4 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left (integral_mono hint
          (integrable_rpow_neg_five_eighths.const_mul _) hpt) (Real.exp_pos _).le
    _ = hcConst * Real.exp (-ξ / 4) := by
        rw [integral_const_mul, hcConst, ← mul_assoc, ← Real.exp_add]
        ring_nf

end Lightlike.Lorentz.SL2RPlancherel
