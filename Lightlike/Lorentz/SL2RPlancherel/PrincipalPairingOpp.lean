import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalPairing
import Lightlike.Lorentz.SL2RPlancherel.KTypeOpposite

/-!
# The opposite-sign ladder chains against the principal-series matrix coefficients

The opposite-sign chain `HcN_{s,l} G` (type `(l, -s)`) is lowered by the adjoint ladder exactly as
the same-sign one, now against `Φ^ν_{s,l}`, since `ladDown_{l+1,-s} Φ_{s,l+1} = -(w + l + 1) Φ_{s,l}`;
at `l = 0` the chain is the profile and `conj Φ^ν_{s,0} = (-1)^s conj Φ^{-ν}_{0,s}`. So for smooth
compactly supported `G`,
`∫_{ξ>0} HcN_{s,l} G conj Φ^ν_{s,l} sinh
= ∏_{j<l} conj(-(w_ν + j + 1)) · (-1)^s ∏_{j<s} conj(-(w_{-ν} + j + 1)) · (1/2) Ĝ(ν/2)`
(`integral_HcN_mul_conj_mcoefP`), the same constant as for the same-sign chains.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `conj Φ^ν_{s,0} = (-1)^s conj Φ^{-ν}_{0,s}`. -/
lemma conj_mcoefP_nat_zero (ν ξ : ℝ) (s : ℕ) :
    (starRingEnd ℂ) (mcoefP ν s 0 ξ) = (-1 : ℂ) ^ s * (starRingEnd ℂ) (mcoefP (-ν) 0 s ξ) := by
  have hsign : (-1 : ℂ) ^ ((0 : ℤ) - s) = (-1) ^ s := by
    rw [zero_sub, zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  have hr := mcoefP_neg_neg (-ν) ξ s 0
  rw [neg_zero] at hr
  rw [conj_mcoefP, neg_zero, hr, mcoefP_eq_conj, hsign]

/-- **The opposite-sign ladder chain against the matrix coefficients**. -/
theorem integral_HcN_mul_conj_mcoefP (ν : ℝ) (s l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    ∫ ξ in Ioi 0, HcN s G l ξ * (starRingEnd ℂ) (mcoefP ν s l ξ) * (Real.sinh ξ : ℂ) =
      (∏ j ∈ Finset.range l, (starRingEnd ℂ) (-(wP ν + ((j : ℂ) + 1)))) *
        ((-1 : ℂ) ^ s * ((∏ j ∈ Finset.range s, (starRingEnd ℂ) (-(wP (-ν) + ((j : ℂ) + 1)))) *
          ((1 / 2) * sphTransformH G (ν / 2)))) := by
  obtain ⟨B, -, hB⟩ := HcN_eq_zero s hc
  induction l with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero]
    have h3 := integral_profile_mul_conj_mcoefP (-ν) s hG hc
    rw [neg_div, sphTransformH_neg] at h3
    rw [← h3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [HcN_zero_eq_Hc, Hc_zero, conj_mcoefP_nat_zero]
    ring
  | succ l ih =>
    have hdown : ∀ ξ ∈ Ioi (0 : ℝ),
        ladDown ((l : ℝ) + 1) (-(s : ℝ)) (mcoefP ν s ((l : ℤ) + 1)) ξ =
          -(wP ν + ((l : ℂ) + 1)) * mcoefP ν s l ξ := by
      intro ξ hξ
      have h := ladDown_mcoefP ν s ((l : ℤ) + 1) (ne_of_gt hξ)
      push_cast at h
      simpa using h
    have h1 : IntegrableOn (fun ξ => ladUp (l : ℝ) (-(s : ℝ)) (HcN s G l) ξ *
        (starRingEnd ℂ) (mcoefP ν s ((l : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_Ioi_of_eq_zero (B := B) (((continuous_HcN s hG (l + 1)).mul
        (Complex.continuous_conj.comp (continuous_mcoefP ν s ((l : ℤ) + 1)))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh))
        (fun ξ hξ => by simp [hB (l + 1) ξ hξ])).congr_fun
        (fun ξ hξ => by simp only [ladUp_HcN s hG l hξ, Pi.mul_apply, Function.comp_apply])
        measurableSet_Ioi
    have h2 : IntegrableOn (fun ξ => HcN s G l ξ *
        (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (-(s : ℝ)) (mcoefP ν s ((l : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_Ioi_of_eq_zero (B := B) (((continuous_HcN s hG l).mul
        (Complex.continuous_conj.comp (show Continuous fun ξ =>
          -(wP ν + ((l : ℂ) + 1)) * mcoefP ν s l ξ from
          continuous_const.mul (continuous_mcoefP ν s l)))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh))
        (fun ξ hξ => by simp [hB l ξ hξ])).congr_fun
        (fun ξ hξ => by simp only [hdown ξ hξ, Pi.mul_apply, Function.comp_apply])
        measurableSet_Ioi
    have hadj := integral_Ioi_ladUp_mul_conj (l : ℝ) (-(s : ℝ))
      ((contDiffOn_HcN s hG l).of_le (by norm_cast))
      (contDiff_one_mcoefP ν s ((l : ℤ) + 1)).contDiffOn (fun ξ h => hB l ξ h.le)
      (tendsto_mul_conj_sinh (continuous_HcN s hG l) (continuous_mcoefP ν s ((l : ℤ) + 1)))
      h1 h2
    have e1 : ∫ ξ in Ioi 0, HcN s G (l + 1) ξ *
        (starRingEnd ℂ) (mcoefP ν s ((l + 1 : ℕ) : ℤ) ξ) * (Real.sinh ξ : ℂ) =
        ∫ ξ in Ioi 0, ladUp (l : ℝ) (-(s : ℝ)) (HcN s G l) ξ *
          (starRingEnd ℂ) (mcoefP ν s ((l : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => by
        simp only [ladUp_HcN s hG l hξ, Nat.cast_succ]
    have e2 : ∫ ξ in Ioi 0, HcN s G l ξ *
        (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (-(s : ℝ)) (mcoefP ν s ((l : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ) =
        (starRingEnd ℂ) (-(wP ν + ((l : ℂ) + 1))) *
          ∫ ξ in Ioi 0, HcN s G l ξ * (starRingEnd ℂ) (mcoefP ν s l ξ) * (Real.sinh ξ : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
      simp only [hdown ξ hξ, map_mul]
      ring
    rw [e1, hadj, e2, ih, Finset.prod_range_succ]
    ring

/-- **The block weight for the opposite-sign chains**: at `ν = 2ρ`,
`|∫_{ξ>0} HcN_{s,l} G conj Φ^{2ρ}_{s,l} sinh|² = w_l(ρ) w_s(ρ)/4 · |Ĝ(ρ)|²`. -/
theorem norm_sq_integral_HcN_mul_conj_mcoefP (ρ : ℝ) (s l : ℕ) {G : ℝ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    ‖∫ ξ in Ioi 0, HcN s G l ξ * (starRingEnd ℂ) (mcoefP (2 * ρ) s l ξ) * (Real.sinh ξ : ℂ)‖ ^ 2 =
      wl l ρ * wl s ρ / 4 * ‖sphTransformH G ρ‖ ^ 2 := by
  rw [integral_HcN_mul_conj_mcoefP (2 * ρ) s l hG hc, show 2 * ρ / 2 = ρ by ring]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod, mul_pow,
    ← Finset.prod_pow, norm_sq_conj_neg_wP_add, norm_sq_conj_neg_wP_neg_add, wl]
  rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by simp]
  ring

end Lightlike.Lorentz.SL2RPlancherel
