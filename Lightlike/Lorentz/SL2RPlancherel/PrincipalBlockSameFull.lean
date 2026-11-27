import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlockFull
import Lightlike.Lorentz.SL2RPlancherel.PrincipalBlockRefl

/-!
# The same-sign block transforms for components that do not vanish near `K`

For the same-sign blocks `(2r, -2l)` and `(-2r, 2l)` let `P g ν = ∫_{(0,∞)} g conj Φ^ν_{-r,l} sinh`
(`samePairing`) and `T g ρ = √(ρ tanh(πρ) w_l(ρ) w_r(ρ)) / C(2ρ) · P g (2ρ)` (`sameTrans`), with the
pairing constant `C = oppConst r l` of the chains (`integral_Hc_mul_conj_mcoefP`). Every test
function of `(0, ∞)` is a same-sign ladder chain (`exists_hLR_eq`), so `blockL2 (src χ) = T χ`
(`blockL2_srcL`) and `|P χ (-ν)| = |P χ (ν)|` (`norm_samePairing_neg`) on test functions; the
cut-offs of `PrincipalBlockFull.lean` extend both to every smooth compactly supported `g`
(`blockL2_srcFun`, `norm_samePairing_neg_of_smooth`). Hence, for `f = F ∘ entries` with `F` smooth
and `f` compactly supported, with no vanishing condition near `K`, for almost every `ρ > 0`,
`|blockL2 r l (kkL2 f (2r, -2l))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f r (-l)|²`
(`norm_sq_blockL2_kkL2_of_contDiff`) and the same for `(-2r, 2l)` with `piCoeff (2ρ) f (-r) l`
(`norm_sq_blockL2_kkL2_refl_of_contDiff`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The same-sign pairing `∫_{(0,∞)} g conj Φ^ν_{-r,l} sinh`. -/
def samePairing (r l : ℕ) (χ : ℝ → ℂ) (ν : ℝ) : ℂ :=
  ∫ x in Ioi 0, χ x * (starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x) * (Real.sinh x : ℂ)

/-- The same-sign principal-series transform. -/
def sameTrans (r l : ℕ) (χ : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ((Real.sqrt (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ) : ℝ) : ℂ) /
    oppConst r l (2 * ρ) * samePairing r l χ (2 * ρ)

lemma samePairing_congr (r l : ℕ) {χ ψ : ℝ → ℂ} (h : ∀ x, 0 < x → χ x = ψ x) (ν : ℝ) :
    samePairing r l χ ν = samePairing r l ψ ν := by
  unfold samePairing
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [h x hx]

lemma samePairing_Hc (r l : ℕ) (ν : ℝ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    samePairing r l (Hc r G l) ν = oppConst r l ν * ((1 / 2) * sphTransformH G (ν / 2)) := by
  unfold samePairing oppConst
  rw [integral_Hc_mul_conj_mcoefP ν r l hG hc]
  ring

/-- On the chains the transform is the block transform. -/
theorem sameTrans_Hc (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (ρ : ℝ) : sameTrans r l (Hc r G l) ρ = blockTgt r l G ρ := by
  have hC := oppConst_ne_zero r l ρ
  rw [sameTrans, samePairing_Hc r l _ hG hc, show 2 * ρ / 2 = ρ by ring, blockTgt]
  generalize oppConst r l (2 * ρ) = C at hC ⊢
  field_simp
  push_cast
  ring

/-- `|T χ (ρ)| = √(ρ tanh(πρ)) |P χ (2ρ)|` for `ρ ≥ 0`. -/
theorem norm_sameTrans (r l : ℕ) (χ : ℝ → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖sameTrans r l χ ρ‖ = Real.sqrt (ρ * Real.tanh (Real.pi * ρ)) * ‖samePairing r l χ (2 * ρ)‖ := by
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ (tanh_nonneg_of_nonneg (by positivity))
  have hnC : ‖oppConst r l (2 * ρ)‖ = Real.sqrt (wl l ρ * wl r ρ) := by
    rw [← norm_sq_oppConst r l ρ, Real.sqrt_sq (norm_nonneg _), mul_comm]
  rw [sameTrans, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), hnC,
    show ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ =
      (ρ * Real.tanh (Real.pi * ρ)) * (wl l ρ * wl r ρ) by ring,
    Real.sqrt_mul ht, mul_div_assoc,
    div_self (Real.sqrt_pos.2 (mul_pos (wl_pos l ρ) (wl_pos r ρ))).ne', mul_one]

/-- A test function of `(0, ∞)` is a same-sign chain. -/
theorem exists_Hc_eq_test (r l : ℕ) (K : testPos) :
    ∃ G : smoothCS, ∀ ξ, 0 < ξ → Hc r G l ξ = (K.1 : ℝ → ℂ) ξ := by
  obtain ⟨G, hG, hGc, hGeq⟩ := exists_hLR_eq r l K.1.2.1 K.1.2.2 K.2
  exact ⟨⟨G, hG, hGc⟩, fun ξ hξ => by rw [Hc_eq_hLR r hG l hξ, hGeq ξ hξ]⟩

/-- `P χ (-ν) = C(-ν)/C(ν) · P χ (ν)` on test functions. -/
theorem samePairing_neg (r l : ℕ) (K : testPos) (ν : ℝ) :
    samePairing r l K.1 (-ν) = oppConst r l (-ν) / oppConst r l ν * samePairing r l K.1 ν := by
  obtain ⟨G, hG⟩ := exists_Hc_eq_test r l K
  rw [← samePairing_congr r l (fun ξ hξ => hG ξ hξ), ← samePairing_congr r l (fun ξ hξ => hG ξ hξ),
    samePairing_Hc r l _ G.2.1 G.2.2, samePairing_Hc r l _ G.2.1 G.2.2, neg_div, sphTransformH_neg]
  field_simp [oppConst_ne_zero' r l ν]

theorem norm_samePairing_neg (r l : ℕ) (K : testPos) (ν : ℝ) :
    ‖samePairing r l K.1 (-ν)‖ = ‖samePairing r l K.1 ν‖ := by
  rw [samePairing_neg, norm_mul, norm_div, norm_oppConst_neg,
    div_self (norm_ne_zero_iff.2 (oppConst_ne_zero' r l ν)), one_mul]

/-- **On test functions the same-sign block isometry is the transform.** -/
theorem blockL2_srcL (r l : ℕ) (K : testPos) :
    (blockL2 r l (srcL K) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] sameTrans r l K.1 := by
  obtain ⟨G, hG⟩ := exists_Hc_eq_test r l K
  have hsrc : srcL K = blockE r l G := by
    refine MemLp.toLp_congr (memLp_srcFun K.1) (memLp_blockSrc r l G.2.1 G.2.2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    show srcFun K.1 ξ = blockSrc r l G ξ
    rw [srcFun, blockSrc, hG ξ hξ]
  rw [hsrc, blockL2_apply]
  filter_upwards [MemLp.coeFn_toLp (memLp_blockTgt r l G.2.1 G.2.2)] with ρ hρ
  rw [show (blockF r l G : ℝ → ℂ) ρ = blockTgt r l G ρ from hρ, ← sameTrans_Hc r l G.2.1 G.2.2 ρ]
  unfold sameTrans
  rw [samePairing_congr r l (fun ξ hξ => hG ξ hξ)]

lemma integrableOn_samePairing (r l : ℕ) (ν : ℝ) {χ : ℝ → ℂ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) :
    IntegrableOn (fun x => χ x * (starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x) * (Real.sinh x : ℂ))
      (Ioi 0) :=
  (((hχ.mul (Complex.continuous_conj.comp (continuous_mcoefP ν (-(r : ℤ)) l))).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)).integrable_of_hasCompactSupport
    (hc.mul_right.mul_right)).integrableOn

theorem tendsto_samePairing_cutNearZero (r l : ℕ) {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) (ν : ℝ) :
    Tendsto (fun n => samePairing r l (cutNearZero g n) ν) atTop (𝓝 (samePairing r l g ν)) := by
  unfold samePairing
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖g x * (starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x) * (Real.sinh x : ℂ)‖)
    (Eventually.of_forall fun n => (((hg.mul (Complex.continuous_ofReal.comp
      ((cutoffBump n).contDiff (n := 0)).continuous)).mul
      (Complex.continuous_conj.comp (continuous_mcoefP ν (-(r : ℤ)) l))).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => ?_)
    (integrableOn_samePairing r l ν hg hc).norm ?_
  · have h0 : 0 ≤ (cutoffBump n : ℝ → ℝ) x := (cutoffBump n).nonneg
    have h1 : (cutoffBump n : ℝ → ℝ) x ≤ 1 := (cutoffBump n).le_one
    simp only [cutNearZero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    have := norm_nonneg (g x)
    have := norm_nonneg ((starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x))
    have := abs_nonneg (Real.sinh x)
    calc ‖g x‖ * (cutoffBump n : ℝ → ℝ) x * ‖(starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x)‖ *
          |Real.sinh x|
        ≤ ‖g x‖ * 1 * ‖(starRingEnd ℂ) (mcoefP ν (-(r : ℤ)) l x)‖ * |Real.sinh x| := by gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoffBump_eq_one hx] with n hn
    simp [cutNearZero, hn]

/-- **The same-sign block identity for every smooth compactly supported `g`.** -/
theorem blockL2_srcFun (r l : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (blockL2 r l ((memLp_srcFun_of_continuous hg.continuous hc).toLp (srcFun g)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] sameTrans r l g := by
  refine ae_eq_of_cut (blockL2 r l).toContinuousLinearMap hg hc
    (fun n => sameTrans r l (cutNearZero g n)) _ (fun n => blockL2_srcL r l (cutNearZeroT hg n)) (fun ρ _ => ?_)
  unfold sameTrans
  exact (tendsto_samePairing_cutNearZero r l hg.continuous hc (2 * ρ)).const_mul _

theorem norm_samePairing_neg_of_smooth (r l : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (ν : ℝ) :
    ‖samePairing r l g (-ν)‖ = ‖samePairing r l g ν‖ := by
  have h1 := (tendsto_samePairing_cutNearZero r l hg.continuous hc (-ν)).norm
  have h2 := (tendsto_samePairing_cutNearZero r l hg.continuous hc ν).norm
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  exact (norm_samePairing_neg r l (cutNearZeroT hg n) ν).symm

/-- The common form: if `p ν = (2π)² P (kkCoeff f m) (-ν)`, then the block transform of the
component `m` is `p` with the density `ρ tanh(πρ)`. -/
theorem norm_sq_blockL2_kkL2_aux {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) (r l : ℕ) (p : ℝ → ℂ)
    (hp : ∀ ν, p ν = ((2 * π : ℝ) : ℂ) ^ 2 * samePairing r l (kkCoeff f m) (-ν)) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) m) : ℝ → ℂ) ρ‖ ^ 2 =
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
  rw [hkk, LinearIsometry.map_smul]
  filter_upwards [Lp.coeFn_smul ((Real.pi : ℂ))⁻¹ (blockL2 r l (hmem.toLp (srcFun g))),
    blockL2_srcFun r l hg hgc, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity))
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow, norm_sameTrans r l _ hρ0.le, mul_pow,
    Real.sq_sqrt ht, hp, norm_mul, norm_pow, norm_samePairing_neg_of_smooth r l hg hgc,
    norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

/-- **The same-sign block `(2r, -2l)` for every smooth compactly supported `f`**: for almost every
`ρ > 0`, `|blockL2 r l (kkL2 f (2r, -2l))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f r (-l)|²`. -/
theorem norm_sq_blockL2_kkL2_of_contDiff {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (r l : ℕ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) ![2 * (r : ℤ), 2 * -(l : ℤ)]) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f r (-l)‖ ^ 2 := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  refine norm_sq_blockL2_kkL2_aux hF hfF hc hf _ r l (fun ν => piCoeff ν f r (-l)) fun ν => ?_
  rw [piCoeff_eq_kkCoeff ν hfc hc]
  unfold samePairing
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (-(r : ℤ)) (l : ℤ) ξ) = mcoefP ν (r : ℤ) (-(l : ℤ)) ξ := by
    rw [conj_mcoefP, neg_neg, neg_neg]
  rw [hΦ]
  ring

/-- **The reflected same-sign block `(-2r, 2l)` for every smooth compactly supported `f`.** -/
theorem norm_sq_blockL2_kkL2_refl_of_contDiff {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (r l : ℕ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2 r l (kkL2 (hf.toLp f) ![2 * -(r : ℤ), 2 * (l : ℤ)]) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f (-r) l‖ ^ 2 := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  refine norm_sq_blockL2_kkL2_aux hF hfF hc hf _ r l (fun ν => piCoeff ν f (-r) l) fun ν => ?_
  rw [piCoeff_eq_kkCoeff ν hfc hc]
  unfold samePairing
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hΦ : (starRingEnd ℂ) (mcoefP (-ν) (-(r : ℤ)) (l : ℤ) ξ) =
      mcoefP ν (-(r : ℤ)) (l : ℤ) ξ := by
    rw [conj_mcoefP, neg_neg, ← mcoefP_neg_neg ν ξ (-(r : ℤ)) (l : ℤ), neg_neg]
  rw [hΦ]
  ring

end Lightlike.Lorentz.SL2RPlancherel
