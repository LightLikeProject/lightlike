import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeBlockIdent
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlockOpp

/-!
# The opposite-sign block transforms are principal-series matrix coefficients, for every component

For a continuous compactly supported `f ∈ L²(SL(2,ℝ))` whose `K × K` component `(2s, 2l)` is, on
`(0, ∞)`, a smooth function with compact support in `(0, ∞)` (no ladder-chain condition), the
Plancherel isometry of the continuous part of the block satisfies, for almost every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`
(`norm_sq_blockL2N_kkL2_of_test`), the formula of `norm_sq_blockL2N_kkL2` without its chain
hypothesis.

The two ingredients:

* `eq_zero_of_orth_of_trunc`: a linear map on the test functions of `(0, ∞)` that vanishes on the
  test functions orthogonal to the discrete directions and tends to `0` on the truncated discrete
  directions vanishes identically (it factors through the moments, `exists_factor_moments`);
* `oppPairing_neg`, `norm_oppPairing_neg`: the reflection `ν ↦ -ν` multiplies the pairing
  `∫ χ conj Φ^ν_{s,l} sinh` by the unimodular factor `C(-ν)/C(ν)` of the pairing constants, as it
  does on the ladder chains (`integral_HcN_mul_conj_mcoefP`, `sphTransformH_neg`); so
  `|piCoeff (2ρ) f s l| = (2π)² |∫ χ conj Φ^{2ρ}_{s,l} sinh|`.

Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Vanishing from the orthogonal test functions and the truncations.** -/
theorem eq_zero_of_orth_of_trunc (s l : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : testPos →ₗ[ℂ] E)
    (h0 : ∀ K : testPos, (∀ i, inner ℂ (phiVec s l i) (srcL K) = 0) → D K = 0)
    (htr : ∀ i : DiscIdx s l, Tendsto (fun n => D (truncT s l i.1 n)) atTop (𝓝 0))
    (K : testPos) : D K = 0 := by
  classical
  obtain ⟨L, hL⟩ := exists_factor_moments s l D h0
  set v := srcL K with hv
  set P := (discSpan s l).starProjection v with hP
  have hPmem : P ∈ discSpan s l := (discSpan s l).starProjection_apply_mem v
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hPmem
  set u := v - P with hu
  have huo : u ∈ (discSpan s l)ᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hmu : momentCLM s l u = 0 := by
    funext i
    simp only [momentCLM, ContinuousLinearMap.pi_apply, innerSL_apply_apply, Pi.zero_apply]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) huo
  set ψ : ℕ → testPos := fun n => K + ∑ i, (-c i) • truncT s l i.1 n with hψ
  have hsrcψ : Tendsto (fun n => srcL (ψ n)) atTop (𝓝 u) := by
    have h := (tendsto_const_nhds (x := v)).add
      (tendsto_finsetSum (Finset.univ : Finset (DiscIdx s l))
        fun i _ => (tendsto_srcL_truncT s l i).const_smul (-c i))
    have e : v + ∑ i, (-c i) • phiVec s l i = u := by
      simp only [neg_smul, Finset.sum_neg_distrib, hc, hu, sub_eq_add_neg]
    rw [e] at h
    refine h.congr fun n => ?_
    simp only [hψ, map_add, map_sum, map_smul, hv]
  have h1 : Tendsto (fun n => D (ψ n)) atTop (𝓝 0) := by
    have := ((L.continuous.comp (momentCLM s l).continuous).tendsto u).comp hsrcψ
    simp only [Function.comp_def, hmu, map_zero] at this
    exact this.congr fun n => (hL (ψ n)).symm
  have h2 : Tendsto (fun n => D (ψ n)) atTop (𝓝 (D K)) := by
    have h := (tendsto_const_nhds (x := D K)).add
      (tendsto_finsetSum (Finset.univ : Finset (DiscIdx s l))
        fun i _ => (htr i).const_smul (-c i))
    simp only [smul_zero, Finset.sum_const_zero, add_zero] at h
    refine h.congr fun n => ?_
    simp only [hψ, map_add, map_sum, map_smul]
  exact tendsto_nhds_unique h2 h1

/-- A test function orthogonal to the discrete directions is an opposite-sign ladder chain. -/
theorem exists_HcN_eq_of_orth (s l : ℕ) (K : testPos)
    (hK : ∀ i, inner ℂ (phiVec s l i) (srcL K) = 0) :
    ∃ G : smoothCS, ∀ ξ, 0 < ξ → HcN s G l ξ = (K.1 : ℝ → ℂ) ξ := by
  have hmom : ∀ i : ℕ, l ≤ i + s → i < l →
      ∫ ξ in Ioi (0 : ℝ), (K.1 : ℝ → ℂ) ξ * ((phiN s l i ξ : ℝ) : ℂ) * (Real.sinh ξ : ℂ) = 0 := by
    intro i hli hil
    have h := hK ⟨⟨i, hil⟩, hli⟩
    rw [inner_phiVec_srcL] at h
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast Real.pi_ne_zero)
  obtain ⟨G, hG, hGc, hGeq⟩ := exists_hLRN_eq s l K.1.2.1 K.1.2.2 K.2 hmom
  exact ⟨⟨G, hG, hGc⟩, fun ξ hξ => by rw [HcN_eq_hLRN s hG l hξ, hGeq ξ hξ]⟩

/-- The pairing on a ladder chain: `∫ HcN_{s,l} G conj Φ^ν sinh = C(ν) · Ĝ(ν/2)/2`. -/
lemma oppPairing_HcN (s l : ℕ) (ν : ℝ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    oppPairing s l (HcN s G l) ν = oppConst s l ν * ((1 / 2) * sphTransformH G (ν / 2)) := by
  unfold oppPairing oppConst
  rw [integral_HcN_mul_conj_mcoefP ν s l hG hc]
  ring

lemma oppConst_ne_zero' (s l : ℕ) (ν : ℝ) : oppConst s l ν ≠ 0 := by
  have := oppConst_ne_zero s l (ν / 2)
  rwa [show 2 * (ν / 2) = ν by ring] at this

lemma norm_oppConst_neg (s l : ℕ) (ν : ℝ) : ‖oppConst s l (-ν)‖ = ‖oppConst s l ν‖ := by
  have h1 := norm_sq_oppConst s l (ν / 2)
  have h2 := norm_sq_oppConst s l (-(ν / 2))
  rw [show 2 * (ν / 2) = ν by ring] at h1
  rw [show 2 * (-(ν / 2)) = -ν by ring, wl_neg, wl_neg, ← h1] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- The pairing at `ν`, as a linear functional of the test function. -/
def evalPairing (s l : ℕ) (ν : ℝ) : testPos →ₗ[ℂ] ℂ where
  toFun K := oppPairing s l K.1 ν
  map_add' F G := oppPairing_add s l F.1.2.1.continuous F.1.2.2 G.1.2.1.continuous G.1.2.2 ν
  map_smul' c F := oppPairing_smul s l c F.1 ν

/-- **The reflection `ν ↦ -ν` of the pairing**: `P χ (-ν) = C(-ν)/C(ν) · P χ (ν)` for every test
function of `(0, ∞)`. -/
theorem oppPairing_neg (s l : ℕ) (K : testPos) (ν : ℝ) :
    oppPairing s l K.1 (-ν) = oppConst s l (-ν) / oppConst s l ν * oppPairing s l K.1 ν := by
  set u := oppConst s l (-ν) / oppConst s l ν with hu
  have h := eq_zero_of_orth_of_trunc s l (evalPairing s l (-ν) - u • evalPairing s l ν)
    (fun K hK => by
      obtain ⟨G, hG⟩ := exists_HcN_eq_of_orth s l K hK
      show oppPairing s l K.1 (-ν) - u * oppPairing s l K.1 ν = 0
      rw [← oppPairing_congr s l (fun ξ hξ => hG ξ hξ), ← oppPairing_congr s l (fun ξ hξ => hG ξ hξ),
        oppPairing_HcN s l _ G.2.1 G.2.2, oppPairing_HcN s l _ G.2.1 G.2.2, neg_div,
        sphTransformH_neg, hu]
      field_simp [oppConst_ne_zero' s l ν]
      ring)
    (fun i => by
      have h1 := (tendsto_oppPairing_truncFun s l i (-ν)).sub
        ((tendsto_oppPairing_truncFun s l i ν).const_mul u)
      simp only [mul_zero, sub_zero] at h1
      exact h1) K
  have h' : oppPairing s l K.1 (-ν) - u * oppPairing s l K.1 ν = 0 := h
  exact sub_eq_zero.1 h'

/-- `|P χ (-ν)| = |P χ (ν)|`. -/
theorem norm_oppPairing_neg (s l : ℕ) (K : testPos) (ν : ℝ) :
    ‖oppPairing s l K.1 (-ν)‖ = ‖oppPairing s l K.1 ν‖ := by
  rw [oppPairing_neg, norm_mul, norm_div, norm_oppConst_neg,
    div_self (norm_ne_zero_iff.2 (oppConst_ne_zero' s l ν)), one_mul]

/-- If the component `(2s, 2l)` of `f` is a test function `χ` on `(0, ∞)`, then
`kkL2 f (2s, 2l) = π⁻¹ src χ`. -/
theorem kkL2_eq_srcL {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (s l : ℕ)
    (K : testPos)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = (K.1 : ℝ → ℂ) ξ) :
    kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)] = ((Real.pi : ℂ))⁻¹ • srcL K := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine Lp.ext ?_
  have h1 := kkL2_toLp_ae hfc hf ![2 * (s : ℤ), 2 * (l : ℤ)]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (srcL K)
  have h3 : (srcL K : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] srcFun K.1 :=
    MemLp.coeFn_toLp (memLp_srcFun K.1)
  filter_upwards [h1, h2, h3, ae_restrict_mem measurableSet_Ioi] with ξ e1 e2 e3 hξ
  rw [e1, e2, Pi.smul_apply, e3, kkSrc, srcFun, h ξ hξ, smul_eq_mul, Complex.ofReal_mul]
  field_simp

/-- The principal-series coefficient of a component that is a test function:
`piCoeff ν f s l = (2π)² P χ (-ν)`. -/
theorem piCoeff_eq_oppPairing (ν : ℝ) {f : SL2R → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (s l : ℕ) {χ : ℝ → ℂ}
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = χ ξ) :
    piCoeff ν f s l = ((2 * π : ℝ) : ℂ) ^ 2 * oppPairing s l χ (-ν) := by
  rw [piCoeff_eq_kkCoeff ν hf hc]
  unfold oppPairing
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (s : ℤ) (l : ℤ) ξ) = mcoefP ν (s : ℤ) (l : ℤ) ξ := by
    rw [conj_mcoefP, neg_neg, mcoefP_neg_neg]
  rw [h ξ hξ, hΦ]
  ring

/-- **The opposite-sign block transform is the principal-series matrix coefficient, for every
component that is a test function of `(0, ∞)`**: for almost every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`. -/
theorem norm_sq_blockL2N_kkL2_of_test {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR)
    (hc : HasCompactSupport f) (s l : ℕ) (K : testPos)
    (h : ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f ![2 * (s : ℤ), 2 * (l : ℤ)] ξ = (K.1 : ℝ → ℂ) ξ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2N s l ((contPartN s l).orthogonalProjectionOnto
          (kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)])) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f s l‖ ^ 2 := by
  rw [kkL2_eq_srcL hfc hf s l K h, map_smul, LinearIsometry.map_smul, blockL2N_srcL]
  have h2 := Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (transL s l K)
  have h3 : (transL s l K : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)] oppTrans s l K.1 :=
    MemLp.coeFn_toLp (memLp_oppTrans s l K.1.2.1 K.1.2.2 K.2)
  filter_upwards [h2, h3, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity))
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow, norm_oppTrans s l _ hρ0.le, mul_pow,
    Real.sq_sqrt ht, piCoeff_eq_oppPairing (2 * ρ) hfc hc s l h, norm_mul, norm_pow,
    norm_oppPairing_neg, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

end Lightlike.Lorentz.SL2RPlancherel
