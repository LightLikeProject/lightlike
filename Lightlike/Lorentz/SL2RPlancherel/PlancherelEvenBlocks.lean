import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlockSameFull

/-!
# The opposite-sign blocks of negative weights

The components `(-2s, -2l)` of a smooth compactly supported `f` are handled by the same block
isometry `blockL2N s l` as `(2s, 2l)`: since `Φ^ν_{-s,-l} = Φ^ν_{s,l} = conj Φ^{-ν}_{s,l}`
(`mcoefP_neg_neg`, `conj_mcoefP`), `piCoeff ν f (-s) (-l) = (2π)² P (kkCoeff f (-2s, -2l)) (-ν)`, and
for almost every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (-2s, -2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f (-s) (-l)|²`
(`norm_sq_blockL2N_kkL2_neg_of_contDiff`); both follow from `norm_sq_blockL2N_kkL2_aux`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The common form: if `p ν = (2π)² P (kkCoeff f m) (-ν)` for the opposite-sign pairing, then the
continuous part of the component `m`, mapped by `blockL2N s l`, is `p` with the density
`ρ tanh(πρ)`. -/
theorem norm_sq_blockL2N_kkL2_aux {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) (s l : ℕ) (p : ℝ → ℂ)
    (hp : ∀ ν, p ν = ((2 * π : ℝ) : ℂ) ^ 2 * oppPairing s l (kkCoeff f m) (-ν)) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2N s l ((contPartN s l).orthogonalProjectionOnto (kkL2 (hf.toLp f) m)) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) * ‖p (2 * ρ)‖ ^ 2 := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  set g := kkCoeff f m with hgdef
  have hg : ContDiff ℝ ∞ g := contDiff_kkCoeff hF hfF m
  have hgc : HasCompactSupport g := hasCompactSupport_kkCoeff hc m
  have hmem := memLp_srcFun_of_continuous hg.continuous hgc
  have hkk : kkL2 (hf.toLp f) m = ((Real.pi : ℂ))⁻¹ • hmem.toLp (srcFun g) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    refine Lp.ext ?_
    filter_upwards [kkL2_toLp_ae hfc hf m, Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (hmem.toLp (srcFun g)),
      MemLp.coeFn_toLp hmem] with ξ e1 e2 e3
    rw [e1, e2, Pi.smul_apply, e3, kkSrc, srcFun, smul_eq_mul, Complex.ofReal_mul, hgdef]
    field_simp
  rw [hkk, map_smul, LinearIsometry.map_smul]
  filter_upwards [Lp.coeFn_smul ((Real.pi : ℂ))⁻¹
      (blockL2N s l ((contPartN s l).orthogonalProjectionOnto (hmem.toLp (srcFun g)))),
    blockL2N_srcFun s l hg hgc, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity))
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow, norm_oppTrans s l _ hρ0.le, mul_pow,
    Real.sq_sqrt ht, hp, norm_mul, norm_pow, norm_oppPairing_neg_of_smooth s l hg hgc,
    norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

/-- **The opposite-sign block `(-2s, -2l)` for every smooth compactly supported `f`.** -/
theorem norm_sq_blockL2N_kkL2_neg_of_contDiff {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (s l : ℕ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2N s l ((contPartN s l).orthogonalProjectionOnto
          (kkL2 (hf.toLp f) ![2 * -(s : ℤ), 2 * -(l : ℤ)])) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f (-s) (-l)‖ ^ 2 := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  refine norm_sq_blockL2N_kkL2_aux hF hfF hc hf _ s l (fun ν => piCoeff ν f (-s) (-l)) fun ν => ?_
  rw [piCoeff_eq_kkCoeff ν hfc hc]
  unfold oppPairing
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (s : ℤ) (l : ℤ) ξ) = mcoefP ν (-(s : ℤ)) (-(l : ℤ)) ξ := by
    rw [conj_mcoefP, neg_neg]
  rw [hΦ]
  ring

end Lightlike.Lorentz.SL2RPlancherel
