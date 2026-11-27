import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KKChain

/-!
# The reflected same-sign blocks

The components `(-2r, 2l)` are handled like `(2r, -2l)`: by the reflection symmetry
`Φ^ν_{-r,l} = Φ^ν_{r,-l}`, if `kkCoeff f (-2r, 2l) = Hc_{r,l} G` on `(0, ∞)` then
`piCoeff ν f (-r) l` is `(2π)²` times the pairing of the chain with `conj Φ^{-ν}_{-r,l}`, and the block
transform `blockL2 r l (kkL2 f (-2r, 2l))` is the principal-series coefficient with density
`ρ tanh(πρ)` (`norm_sq_blockL2_kkL2_refl`), in particular for every smooth compactly supported `f`
vanishing near `K` (`norm_sq_blockL2_kkL2_refl_of_smooth`). With `PrincipalBlock.lean` and
`KKChain.lean` this covers every even `K`-type `(2a, 2b)` with `a b ≤ 0`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (identification of the block transforms with
matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- If the component `m` of `f` is the chain `Hc_{r,l} G` on `(0, ∞)`, then
`kkL2 f m = π⁻¹ blockE r l G`. -/
theorem kkL2_eq_blockE_of {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (m : Fin 2 → ℤ) (r l : ℕ) (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f m ξ = Hc r G l ξ) :
    kkL2 (hf.toLp f) m = ((Real.pi : ℂ))⁻¹ • blockE r l G := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine Lp.ext ?_
  have h1 := kkL2_toLp_ae hfc hf m
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockE r l G)
  have h3 : (blockE r l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockSrc r l G :=
    MemLp.coeFn_toLp (memLp_blockSrc r l G.2.1 G.2.2)
  filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 e3 hξ
  rw [e1, e2, Pi.smul_apply, e3, kkSrc, blockSrc, h ξ hξ, smul_eq_mul, Complex.ofReal_mul]
  field_simp

theorem piCoeff_eq_integral_Hc_refl (ν : ℝ) {f : SL2R → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (r l : ℕ) {G : ℝ → ℂ}
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * -(r : ℤ), 2 * (l : ℤ)] ξ = Hc r G l ξ) :
    piCoeff ν f (-r) l = ((2 * π : ℝ) : ℂ) ^ 2 * ∫ ξ in Ioi (0 : ℝ),
      Hc r G l ξ * (starRingEnd ℂ) (mcoefP (-ν) (-r) l ξ) * (Real.sinh ξ : ℂ) := by
  rw [piCoeff_eq_kkCoeff ν hf hc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (-(r : ℤ)) (l : ℤ) ξ) =
      mcoefP ν (-(r : ℤ)) (l : ℤ) ξ := by
    rw [conj_mcoefP, neg_neg, ← mcoefP_neg_neg ν ξ (-(r : ℤ)) (l : ℤ), neg_neg]
  rw [h ξ hξ, hΦ]
  ring

theorem norm_sq_piCoeff_eq_refl (ρ : ℝ) {f : SL2R → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * -(r : ℤ), 2 * (l : ℤ)] ξ = Hc r G l ξ) :
    ‖piCoeff (2 * ρ) f (-r) l‖ ^ 2 =
      (2 * π) ^ 4 * (wl l ρ * wl r ρ / 4 * ‖sphTransformH G ρ‖ ^ 2) := by
  rw [piCoeff_eq_integral_Hc_refl (2 * ρ) hf hc r l h, norm_mul, mul_pow, norm_pow,
    show -(2 * ρ) = 2 * (-ρ) by ring, norm_sq_integral_Hc_mul_conj_mcoefP (-ρ) r l hG hcG,
    wl_neg, wl_neg, sphTransformH_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  ring

/-- **The reflected same-sign block transform is the principal-series matrix coefficient.** -/
theorem norm_sq_blockL2_kkL2_refl {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (hc : HasCompactSupport f) (r l : ℕ) (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * -(r : ℤ), 2 * (l : ℤ)] ξ = Hc r G l ξ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) ![2 * -(r : ℤ), 2 * (l : ℤ)]) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f (-r) l‖ ^ 2 := by
  rw [kkL2_eq_blockE_of hfc hf _ r l G h, LinearIsometry.map_smul, blockL2_apply]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockF r l G)
  have h3 : (blockF r l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockTgt r l G :=
    MemLp.coeFn_toLp (memLp_blockTgt r l G.2.1 G.2.2)
  filter_upwards [h2, h3, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hnn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity)))
      (wl_nonneg l ρ)) (wl_nonneg r ρ)
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow,
    norm_sq_piCoeff_eq_refl ρ hfc hc r l G.2.1 G.2.2 h, blockTgt, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hnn, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  field_simp
  ring

/-- **The reflected same-sign block transforms of a smooth function vanishing near `K`.** -/
theorem norm_sq_blockL2_kkL2_refl_of_smooth {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ g : SL2R, sumSq g < 2 + ε → f g = 0) (hf : MemLp f 2 haarR) (r l : ℕ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) ![2 * -(r : ℤ), 2 * (l : ℤ)]) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f (-r) l‖ ^ 2 := by
  have hfc : Continuous f := by
    have e : f = fun g : SL2R => F fun i j => g i j := funext hfF
    rw [e]
    exact hF.continuous.comp (continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))
  obtain ⟨G, hG⟩ := exists_Hc_eq_kkCoeff hF hfF hc hε h0 ![2 * -(r : ℤ), 2 * (l : ℤ)] r l
  exact norm_sq_blockL2_kkL2_refl hfc hf hc r l G hG

end Lightlike.Lorentz.SL2RPlancherel
