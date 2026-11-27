import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.CasimirTest
import Lightlike.Lorentz.SL2RPlancherel.PrincipalDiscreteOrth

/-!
# Decay of the principal-series pairing of a test function

For `χ` smooth with compact support in `(0, ∞)` and the matrix coefficient `Φ^ν_{s,l}` of the block
`(l, -s)`, the pairing `P χ ν = ∫_{(0,∞)} χ conj Φ^ν_{s,l} sinh` satisfies
`P (L χ) ν = (ν² + 1)/4 · P χ ν` (`pairing_radialCasimir`, by the symmetry of the Casimir) and
`|P χ ν| ≤ C ∫ |χ| sinh` with `C = ∫ (1 + u²)^{-5/8} du` (`norm_pairing_le`, from `|Φ| ≤ Ξ ≤ C`);
hence `|P χ ν| ≤ 4 C ∫ |L χ| sinh / (ν² + 1)` (`norm_pairing_le_div`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The principal-series pairing `∫_{(0,∞)} χ conj Φ^ν_{s,l} sinh`. -/
def oppPairing (s l : ℕ) (χ : ℝ → ℂ) (ν : ℝ) : ℂ :=
  ∫ x in Ioi 0, χ x * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)

/-- **The Casimir multiplies the pairing by the eigenvalue** `(ν² + 1)/4`. -/
theorem pairing_radialCasimir (s l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ Ioi 0) :
    oppPairing s l (radialCasimir l (-(s : ℝ)) χ) ν =
      (((ν ^ 2 + 1) / 4 : ℝ) : ℂ) * oppPairing s l χ ν := by
  have hG : ContDiffOn ℝ 2 (mcoefP ν s l) (Ioi 0) :=
    ((contDiff_mcoefP ν s l).of_le (by norm_cast)).contDiffOn
  unfold oppPairing
  rw [integral_radialCasimir_test l (-(s : ℝ)) hχ hc hsub hG, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hL := radialCasimir_mcoefP ν (s : ℤ) (l : ℤ) hx
  simp only [Int.cast_natCast] at hL
  rw [hL, neg_wP_mul_wP_add_one, map_mul, Complex.conj_ofReal]
  ring

/-- The weight `C ∫ |χ| sinh` dominating the pairing, `C = ∫ (1 + u²)^{-5/8} du`. -/
def pairingWeight (χ : ℝ → ℂ) : ℝ := hcConst * ∫ x in Ioi 0, ‖χ x‖ * Real.sinh x

lemma norm_mcoefP_le_hcConst (ν : ℝ) (m n : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    ‖mcoefP ν m n x‖ ≤ hcConst := by
  have h := (norm_mcoefP_le ν x m n).trans (hcXi_le hx)
  have hC : 0 ≤ hcConst := by
    have := hcXi_le (ξ := 0) le_rfl
    have h0 := (norm_nonneg (mcoefP ν m n 0)).trans (norm_mcoefP_le ν 0 m n)
    simp at this
    linarith
  have he : Real.exp (-x / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith

/-- `|P χ ν| ≤ C ∫ |χ| sinh`. -/
theorem norm_pairing_le (s l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : ‖oppPairing s l χ ν‖ ≤ pairingWeight χ := by
  unfold oppPairing pairingWeight
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_)
  · exact (((hχ.mul (Complex.continuous_conj.comp (continuous_mcoefP ν s l))).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)).norm.integrable_of_hasCompactSupport
      (hc.mul_right.mul_right).norm).integrableOn
  · exact ((continuous_const.mul (hχ.norm.mul Real.continuous_sinh)).integrable_of_hasCompactSupport
      (hc.norm.mul_right.mul_left)).integrableOn
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sinh_pos_iff.2 hx0).le]
    have h := norm_mcoefP_le_hcConst ν s l hx0.le
    have hs := (Real.sinh_pos_iff.2 hx0).le
    calc ‖χ x‖ * ‖mcoefP ν s l x‖ * Real.sinh x ≤ ‖χ x‖ * hcConst * Real.sinh x := by gcongr
      _ = hcConst * (‖χ x‖ * Real.sinh x) := by ring

/-- **Decay of the pairing**: `|P χ ν| ≤ 4 C ∫ |L χ| sinh / (ν² + 1)`. -/
theorem norm_pairing_le_div (s l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hsub : tsupport χ ⊆ Ioi 0) :
    ‖oppPairing s l χ ν‖ ≤ 4 * pairingWeight (radialCasimir l (-(s : ℝ)) χ) / (ν ^ 2 + 1) := by
  obtain ⟨hL, hLc, -⟩ := radialCasimir_test l (-(s : ℝ)) hχ hc hsub
  have h := norm_pairing_le s l ν hL.continuous hLc
  rw [pairing_radialCasimir s l ν hχ hc hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (oppPairing s l χ ν)]

end Lightlike.Lorentz.SL2RPlancherel
