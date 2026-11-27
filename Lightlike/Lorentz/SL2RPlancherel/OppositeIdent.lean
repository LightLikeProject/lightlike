import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeTransform
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlockOpp

/-!
# The principal-series transform of an opposite-sign block

For the block `(l, -s)` let `C(ν) = ∏_{j<l} conj(-(w_ν + j + 1)) · (-1)^s ∏_{j<s} conj(-(w_{-ν} + j + 1))`
be the pairing constant of the ladder chains (`integral_HcN_mul_conj_mcoefP`) and
`T χ (ρ) = √(ρ tanh(πρ) w_l(ρ) w_s(ρ)) / C(2ρ) · ∫_{(0,∞)} χ conj Φ^{2ρ}_{s,l} sinh` (`oppTrans`).
Then `|C(2ρ)|² = w_l(ρ) w_s(ρ) > 0` (`norm_sq_oppConst`), `T` is the block transform on the chains,
`T (HcN_{s,l} G) = blockTgt s l G` on `ρ > 0` (`oppTrans_HcN`), and `|T χ (ρ)| = √(ρ tanh(πρ)) |P χ (2ρ)|`
(`norm_oppTrans`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The pairing constant of the opposite-sign ladder chains. -/
def oppConst (s l : ℕ) (ν : ℝ) : ℂ :=
  (∏ j ∈ Finset.range l, (starRingEnd ℂ) (-(wP ν + ((j : ℂ) + 1)))) *
    ((-1 : ℂ) ^ s * ∏ j ∈ Finset.range s, (starRingEnd ℂ) (-(wP (-ν) + ((j : ℂ) + 1))))

lemma wl_pos (l : ℕ) (ρ : ℝ) : 0 < wl l ρ :=
  Finset.prod_pos fun k _ => by positivity

/-- `|C(2ρ)|² = w_l(ρ) w_s(ρ)`. -/
theorem norm_sq_oppConst (s l : ℕ) (ρ : ℝ) : ‖oppConst s l (2 * ρ)‖ ^ 2 = wl l ρ * wl s ρ := by
  unfold oppConst
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_prod, mul_pow,
    ← Finset.prod_pow, norm_sq_conj_neg_wP_add, norm_sq_conj_neg_wP_neg_add, wl]

lemma oppConst_ne_zero (s l : ℕ) (ρ : ℝ) : oppConst s l (2 * ρ) ≠ 0 := by
  intro h
  have := norm_sq_oppConst s l ρ
  rw [h, norm_zero, zero_pow two_ne_zero] at this
  exact (mul_pos (wl_pos l ρ) (wl_pos s ρ)).ne this

/-- The principal-series transform of the opposite-sign block `(l, -s)`. -/
def oppTrans (s l : ℕ) (χ : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ((Real.sqrt (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ) : ℝ) : ℂ) /
    oppConst s l (2 * ρ) * oppPairing s l χ (2 * ρ)

/-- **On the ladder chains the transform is the block transform**. -/
theorem oppTrans_HcN (s l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (ρ : ℝ) : oppTrans s l (HcN s G l) ρ = blockTgt s l G ρ := by
  have hC := oppConst_ne_zero s l ρ
  have hP : oppPairing s l (HcN s G l) (2 * ρ) = oppConst s l (2 * ρ) * ((1 / 2) * sphTransformH G ρ) := by
    unfold oppPairing oppConst
    rw [integral_HcN_mul_conj_mcoefP (2 * ρ) s l hG hc, show 2 * ρ / 2 = ρ by ring]
    ring
  rw [oppTrans, hP, blockTgt]
  generalize oppConst s l (2 * ρ) = C at hC ⊢
  field_simp
  push_cast
  ring

/-- `|T χ (ρ)| = √(ρ tanh(πρ)) |P χ (2ρ)|` for `ρ ≥ 0`. -/
theorem norm_oppTrans (s l : ℕ) (χ : ℝ → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖oppTrans s l χ ρ‖ = Real.sqrt (ρ * Real.tanh (Real.pi * ρ)) * ‖oppPairing s l χ (2 * ρ)‖ := by
  have hC := oppConst_ne_zero s l ρ
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ (tanh_nonneg_of_nonneg (by positivity))
  have hnC : ‖oppConst s l (2 * ρ)‖ = Real.sqrt (wl l ρ * wl s ρ) := by
    rw [← norm_sq_oppConst s l ρ, Real.sqrt_sq (norm_nonneg _)]
  rw [oppTrans, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hnC,
    show ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ =
      (ρ * Real.tanh (Real.pi * ρ)) * (wl l ρ * wl s ρ) by ring,
    Real.sqrt_mul ht, mul_div_assoc, div_self (Real.sqrt_pos.2 (mul_pos (wl_pos l ρ) (wl_pos s ρ))).ne',
    mul_one]

end Lightlike.Lorentz.SL2RPlancherel
