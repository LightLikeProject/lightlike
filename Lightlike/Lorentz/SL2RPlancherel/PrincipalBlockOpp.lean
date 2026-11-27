import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlock
import Lightlike.Lorentz.SL2RPlancherel.PrincipalPairingOpp
import Lightlike.Lorentz.SL2RPlancherel.KTypeOppositeIso

/-!
# The opposite-sign block transforms are principal-series matrix coefficients

If the `K × K` component `(2s, 2l)` of a continuous compactly supported `f ∈ L²(SL(2,ℝ))` is the
opposite-sign ladder chain `HcN_{s,l} G` on `(0, ∞)`, then `kkL2 f (2s, 2l) = π⁻¹ blockEN s l G` lies in
the continuous part, and the Plancherel isometry of that part satisfies, for almost every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`
(`norm_sq_blockL2N_kkL2`), with the same density as the same-sign blocks.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- If the component `(2s, 2l)` of `f` is the chain `HcN_{s,l} G` on `(0, ∞)`, the matrix
coefficient of `π_ν(f)` is `(2π)²` times the pairing of the chain with `conj Φ^{-ν}_{s,l}`. -/
theorem piCoeff_eq_integral_HcN (ν : ℝ) {f : SL2R → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s l : ℕ) {G : ℝ → ℂ}
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = HcN s G l ξ) :
    piCoeff ν f s l = ((2 * π : ℝ) : ℂ) ^ 2 * ∫ ξ in Ioi (0 : ℝ),
      HcN s G l ξ * (starRingEnd ℂ) (mcoefP (-ν) s l ξ) * (Real.sinh ξ : ℂ) := by
  rw [piCoeff_eq_kkCoeff ν hf hc]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (s : ℤ) (l : ℤ) ξ) = mcoefP ν (s : ℤ) (l : ℤ) ξ := by
    rw [conj_mcoefP, neg_neg, mcoefP_neg_neg]
  rw [h ξ hξ, hΦ]
  ring

/-- At `ν = 2ρ`, `|piCoeff (2ρ) f s l|² = (2π)⁴ w_l(ρ) w_s(ρ)/4 · |Ĝ(ρ)|²` for an opposite-sign
chain component. -/
theorem norm_sq_piCoeff_eq_of_HcN (ρ : ℝ) {f : SL2R → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hcG : HasCompactSupport G)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = HcN s G l ξ) :
    ‖piCoeff (2 * ρ) f s l‖ ^ 2 =
      (2 * π) ^ 4 * (wl l ρ * wl s ρ / 4 * ‖sphTransformH G ρ‖ ^ 2) := by
  rw [piCoeff_eq_integral_HcN (2 * ρ) hf hc s l h, norm_mul, mul_pow, norm_pow,
    show -(2 * ρ) = 2 * (-ρ) by ring, norm_sq_integral_HcN_mul_conj_mcoefP (-ρ) s l hG hcG,
    wl_neg, wl_neg, sphTransformH_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  ring

/-- If the component `(2s, 2l)` of `f` is the chain `HcN_{s,l} G` on `(0, ∞)`, then
`kkL2 f (2s, 2l) = π⁻¹ blockEN s l G`. -/
theorem kkL2_eq_blockEN {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (s l : ℕ)
    (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = HcN s G l ξ) :
    kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)] = ((Real.pi : ℂ))⁻¹ • blockEN s l G := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine Lp.ext ?_
  have h1 := kkL2_toLp_ae hfc hf ![2 * (s : ℤ), 2 * (l : ℤ)]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockEN s l G)
  have h3 : (blockEN s l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockSrcN s l G :=
    MemLp.coeFn_toLp (memLp_blockSrcN s l G.2.1 G.2.2)
  filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 e3 hξ
  rw [e1, e2, Pi.smul_apply, e3, kkSrc, blockSrcN, h ξ hξ, smul_eq_mul, Complex.ofReal_mul]
  field_simp

/-- **The opposite-sign block transform is the principal-series matrix coefficient**: for almost
every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`. -/
theorem norm_sq_blockL2N_kkL2 {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (hc : HasCompactSupport f) (s l : ℕ) (G : smoothCS)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = HcN s G l ξ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2N s l ((contPartN s l).orthogonalProjectionOnto
          (kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)])) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f s l‖ ^ 2 := by
  have hmem : kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)] =
      (((((Real.pi : ℂ))⁻¹ • blockENc s l G : contPartN s l)) : L2Ioi) := by
    rw [kkL2_eq_blockEN hfc hf s l G h]
    rfl
  rw [hmem, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearIsometry.map_smul,
    blockL2N_apply]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockF s l G)
  have h3 : (blockF s l G : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] blockTgt s l G :=
    MemLp.coeFn_toLp (memLp_blockTgt s l G.2.1 G.2.2)
  filter_upwards [h2, h3, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hnn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl s ρ :=
    mul_nonneg (mul_nonneg (mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity)))
      (wl_nonneg l ρ)) (wl_nonneg s ρ)
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow,
    norm_sq_piCoeff_eq_of_HcN ρ hfc hc s l G.2.1 G.2.2 h, blockTgt, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hnn, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  field_simp
  ring

/-- Non-vacuity: the chain hypothesis of `norm_sq_blockL2N_kkL2` holds for `f = 0`, `G = 0`. -/
example (s l : ℕ) : ∀ ξ ∈ Ioi (0 : ℝ),
    kkCoeff (0 : SL2R → ℂ) ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = HcN s ((0 : smoothCS) : ℝ → ℂ) l ξ := by
  intro ξ _
  have h := HcN_smul s (0 : ℂ) (contDiff_const (c := (0 : ℂ))) l ξ
  simp only [zero_smul, zero_mul] at h
  simp only [ZeroMemClass.coe_zero, kkCoeff, kkProfile]
  simp [h]

end Lightlike.Lorentz.SL2RPlancherel
