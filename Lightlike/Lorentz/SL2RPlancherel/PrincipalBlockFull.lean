import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.OppositeBlockCoeff
import Lightlike.Lorentz.SL2RPlancherel.KKChain

/-!
# The opposite-sign block transforms for components that do not vanish near `K`

The block identities of `OppositeBlockIdent.lean` and `OppositeBlockCoeff.lean` are proved for test
functions with compact support in `(0, ∞)`. Here they are extended by a limit to every smooth
compactly supported `g` on `ℝ`, the components `kkCoeff f m` of a smooth compactly supported `f`
on `SL(2,ℝ)` included, which need not vanish near `ξ = 0`, i.e. near `K`:

* `ae_eq_of_cut`: if a continuous linear `B` on `L²(0, ∞)` sends the sources of the cut-offs
  `g η_n` (`cutNearZeroT`) almost everywhere to functions converging pointwise to `T`, then `B (src g) = T`
  almost everywhere; the sources converge in `L²` (`tendsto_srcL_cutNearZeroT`);
* `blockL2N_srcFun`: `blockL2N (P_cont (src g)) = T g` almost everywhere, and
  `norm_oppPairing_neg_of_smooth`: `|P g (-ν)| = |P g (ν)|`;
* `norm_sq_blockL2N_kkL2_of_smooth`: for `f = F ∘ entries` with `F` smooth and `f` compactly
  supported, for almost every `ρ > 0`,
  `|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`,
  with no vanishing condition near `K`.

Layer 2c-v of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The cut-off `g η_n`, vanishing near `0`. -/
def cutNearZero (g : ℝ → ℂ) (n : ℕ) (ξ : ℝ) : ℂ := g ξ * (((cutoffBump n : ℝ → ℝ) ξ : ℝ) : ℂ)

lemma tsupport_cutNearZero (g : ℝ → ℂ) (n : ℕ) :
    tsupport (cutNearZero g n) ⊆ tsupport (cutoffBump n : ℝ → ℝ) :=
  closure_mono fun ξ hξ => by
    rw [Function.mem_support] at hξ ⊢
    intro h0
    exact hξ (by simp [cutNearZero, h0])

lemma contDiff_cutNearZero {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (n : ℕ) : ContDiff ℝ ∞ (cutNearZero g n) :=
  hg.mul (Complex.ofRealCLM.contDiff.comp ((cutoffBump n).contDiff (n := ⊤)))

/-- The cut-off as a test function of `(0, ∞)`. -/
def cutNearZeroT {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (n : ℕ) : testPos :=
  ⟨⟨cutNearZero g n, contDiff_cutNearZero hg n,
    ((cutoffBump n).hasCompactSupport).mono' ((subset_tsupport _).trans (tsupport_cutNearZero g n))⟩,
    (tsupport_cutNearZero g n).trans (tsupport_cutoffBump n)⟩

theorem memLp_srcFun_of_continuous {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) :
    MemLp (srcFun g) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ((Complex.continuous_ofReal.comp (continuous_const.mul
    (Real.continuous_sqrt.comp Real.continuous_sinh))).mul hg).memLp_of_hasCompactSupport hc.mul_left

/-- **The sources of the cut-offs converge in `L²(0, ∞)`.** -/
theorem tendsto_srcL_cutNearZeroT {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Tendsto (fun n => srcL (cutNearZeroT hg n)) atTop
      (𝓝 ((memLp_srcFun_of_continuous hg.continuous hc).toLp (srcFun g))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmem := memLp_srcFun_of_continuous hg.continuous hc
  have hsq : Tendsto (fun n => ‖srcL (cutNearZeroT hg n) - hmem.toLp (srcFun g)‖ ^ 2) atTop (𝓝 0) := by
    have he : ∀ n, ‖srcL (cutNearZeroT hg n) - hmem.toLp (srcFun g)‖ ^ 2 = ∫ ξ in Ioi (0 : ℝ),
        ‖srcFun g ξ * (((cutoffBump n : ℝ → ℝ) ξ - 1 : ℝ) : ℂ)‖ ^ 2 := by
      intro n
      rw [norm_sq_Lp_two_eq']
      refine integral_congr_ae ?_
      have h1 := Lp.coeFn_sub (srcL (cutNearZeroT hg n)) (hmem.toLp (srcFun g))
      have h2 : (srcL (cutNearZeroT hg n) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
          srcFun (cutNearZeroT hg n).1 := MemLp.coeFn_toLp (memLp_srcFun _)
      have h3 := MemLp.coeFn_toLp hmem
      filter_upwards [h1, h2, h3] with ξ e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3]
      congr 2
      show srcFun (cutNearZero g n) ξ - srcFun g ξ = _
      simp only [srcFun, cutNearZero]
      push_cast
      ring
    simp_rw [he]
    have hint : Integrable (fun ξ => ‖srcFun g ξ‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
      hmem.integrable_norm_pow two_ne_zero
    have hlim := tendsto_integral_of_dominated_convergence (fun ξ => ‖srcFun g ξ‖ ^ 2)
      (F := fun (n : ℕ) ξ => ‖srcFun g ξ * (((cutoffBump n : ℝ → ℝ) ξ - 1 : ℝ) : ℂ)‖ ^ 2)
      (f := fun _ => (0 : ℝ))
      (fun n => ((hmem.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((cutoffBump n).contDiff (n := 0)).continuous.sub
          continuous_const)).aestronglyMeasurable).norm.pow 2))
      hint (fun n => Eventually.of_forall fun ξ => ?_) ?_
    · simpa using hlim
    · have h0 : 0 ≤ (cutoffBump n : ℝ → ℝ) ξ := (cutoffBump n).nonneg
      have h1 : (cutoffBump n : ℝ → ℝ) ξ ≤ 1 := (cutoffBump n).le_one
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow]
      have : |(cutoffBump n : ℝ → ℝ) ξ - 1| ^ 2 ≤ 1 := by
        rw [sq_abs]; nlinarith
      nlinarith [sq_nonneg ‖srcFun g ξ‖]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_cutoffBump_eq_one hξ] with n hn
      simp [hn]
  have := hsq.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **Limits of the cut-offs.** -/
theorem ae_eq_of_cut (B : L2Ioi →L[ℂ] L2Ioi) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (T : ℕ → ℝ → ℂ) (T₀ : ℝ → ℂ)
    (hB : ∀ n, (B (srcL (cutNearZeroT hg n)) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] T n)
    (hpt : ∀ ρ, 0 < ρ → Tendsto (fun n => T n ρ) atTop (𝓝 (T₀ ρ))) :
    (B ((memLp_srcFun_of_continuous hg.continuous hc).toLp (srcFun g)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] T₀ := by
  have hT := (B.continuous.tendsto _).comp (tendsto_srcL_cutNearZeroT hg hc)
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
  filter_upwards [hlim, ae_all_iff.2 hB, ae_restrict_mem measurableSet_Ioi] with x hx hx' hx0
  have h2 : Tendsto (fun k => (B (srcL (cutNearZeroT hg (ns k))) : ℝ → ℂ) x) atTop (𝓝 (T₀ x)) :=
    ((hpt x hx0).comp hns.tendsto_atTop).congr fun k => (hx' (ns k)).symm
  exact tendsto_nhds_unique hx h2

/-- The pairings of the cut-offs converge. -/
theorem tendsto_oppPairing_cutNearZero (s l : ℕ) {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) (ν : ℝ) :
    Tendsto (fun n => oppPairing s l (cutNearZero g n) ν) atTop (𝓝 (oppPairing s l g ν)) := by
  unfold oppPairing
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖g x * (starRingEnd ℂ) (mcoefP ν s l x) * (Real.sinh x : ℂ)‖)
    (Eventually.of_forall fun n => (((hg.mul (Complex.continuous_ofReal.comp
      ((cutoffBump n).contDiff (n := 0)).continuous)).mul
      (Complex.continuous_conj.comp (continuous_mcoefP ν s l))).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => ?_)
    (integrableOn_pairing s l ν hg hc).norm ?_
  · have h0 : 0 ≤ (cutoffBump n : ℝ → ℝ) x := (cutoffBump n).nonneg
    have h1 : (cutoffBump n : ℝ → ℝ) x ≤ 1 := (cutoffBump n).le_one
    simp only [cutNearZero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    have := norm_nonneg (g x)
    have := norm_nonneg ((starRingEnd ℂ) (mcoefP ν s l x))
    have := abs_nonneg (Real.sinh x)
    calc ‖g x‖ * (cutoffBump n : ℝ → ℝ) x * ‖(starRingEnd ℂ) (mcoefP ν s l x)‖ * |Real.sinh x|
        ≤ ‖g x‖ * 1 * ‖(starRingEnd ℂ) (mcoefP ν s l x)‖ * |Real.sinh x| := by gcongr
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cutoffBump_eq_one hx] with n hn
    simp [cutNearZero, hn]

/-- The continuous part followed by the block isometry, as a continuous linear map. -/
def blockCLM (s l : ℕ) : L2Ioi →L[ℂ] L2Ioi :=
  (blockL2N s l).toContinuousLinearMap.comp (contPartN s l).orthogonalProjectionOnto

/-- **The block identity for every smooth compactly supported `g`**:
`blockL2N (P_cont (src g)) = T g` almost everywhere on `(0, ∞)`. -/
theorem blockL2N_srcFun (s l : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    (blockL2N s l ((contPartN s l).orthogonalProjectionOnto
        ((memLp_srcFun_of_continuous hg.continuous hc).toLp (srcFun g))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] oppTrans s l g := by
  refine ae_eq_of_cut (blockCLM s l) hg hc (fun n => oppTrans s l (cutNearZero g n)) _
    (fun n => ?_) (fun ρ _ => ?_)
  · show (blockL2N s l ((contPartN s l).orthogonalProjectionOnto (srcL (cutNearZeroT hg n))) : ℝ → ℂ) =ᵐ[_] _
    rw [blockL2N_srcL]
    exact MemLp.coeFn_toLp (memLp_oppTrans s l (cutNearZeroT hg n).1.2.1 (cutNearZeroT hg n).1.2.2 (cutNearZeroT hg n).2)
  · unfold oppTrans
    exact (tendsto_oppPairing_cutNearZero s l hg.continuous hc (2 * ρ)).const_mul _

/-- `|P g (-ν)| = |P g (ν)|` for every smooth compactly supported `g`. -/
theorem norm_oppPairing_neg_of_smooth (s l : ℕ) {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (ν : ℝ) :
    ‖oppPairing s l g (-ν)‖ = ‖oppPairing s l g ν‖ := by
  have h1 := (tendsto_oppPairing_cutNearZero s l hg.continuous hc (-ν)).norm
  have h2 := (tendsto_oppPairing_cutNearZero s l hg.continuous hc ν).norm
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  exact (norm_oppPairing_neg s l (cutNearZeroT hg n) ν).symm

/-- A function of the matrix entries through a continuous `F` is continuous. -/
lemma continuous_of_entries {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ} (hF : Continuous F)
    (hfF : ∀ g : SL2R, f g = F fun i j => g i j) : Continuous f := by
  have e : f = fun g : SL2R => F fun i j => g i j := funext hfF
  rw [e]
  exact hF.comp (continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

/-- The components of a compactly supported `f` have compact support in `ξ`. -/
lemma hasCompactSupport_kkCoeff {f : SL2R → ℂ} (hc : HasCompactSupport f) (m : Fin 2 → ℤ) :
    HasCompactSupport (kkCoeff f m) := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image continuous_sumSq).isBounded.bddAbove
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) |R|) fun ξ hξ => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hξ
  refine kkCoeff_eq_zero_of_vanish (fun g hg => ?_) m
  by_contra hne
  have hle := hR ⟨g, subset_tsupport f hne, rfl⟩
  have hcosh := cosh_ge_half_abs ξ
  have := le_abs_self R
  linarith

/-- **The opposite-sign block transform is the principal-series matrix coefficient, for every
smooth compactly supported `f`**: for almost every `ρ > 0`,
`|blockL2N s l (P_cont (kkL2 f (2s, 2l)))(ρ)|² = ρ tanh(πρ) / (π² (2π)⁴) · |piCoeff (2ρ) f s l|²`. -/
theorem norm_sq_blockL2N_kkL2_of_smooth {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) (hf : MemLp f 2 haarR) (s l : ℕ) :
    ∀ᵐ ρ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(blockL2N s l ((contPartN s l).orthogonalProjectionOnto
          (kkL2 (hf.toLp f) ![2 * (s : ℤ), 2 * (l : ℤ)])) : ℝ → ℂ) ρ‖ ^ 2 =
        ρ * Real.tanh (Real.pi * ρ) / (Real.pi ^ 2 * (2 * Real.pi) ^ 4) *
          ‖piCoeff (2 * ρ) f s l‖ ^ 2 := by
  have hfc : Continuous f := continuous_of_entries hF.continuous hfF
  set m : Fin 2 → ℤ := ![2 * (s : ℤ), 2 * (l : ℤ)] with hm
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
  have hpi : ∀ ν, piCoeff ν f s l = ((2 * π : ℝ) : ℂ) ^ 2 * oppPairing s l g (-ν) := fun ν =>
    piCoeff_eq_oppPairing ν hfc hc s l (fun ξ _ => rfl)
  rw [hkk, map_smul, LinearIsometry.map_smul]
  filter_upwards [Lp.coeFn_smul ((Real.pi : ℂ))⁻¹
      (blockL2N s l ((contPartN s l).orthogonalProjectionOnto (hmem.toLp (srcFun g)))),
    blockL2N_srcFun s l hg hgc, ae_restrict_mem measurableSet_Ioi] with ρ e2 e3 hρ
  have hρ0 : (0 : ℝ) < ρ := hρ
  have ht : 0 ≤ ρ * Real.tanh (Real.pi * ρ) :=
    mul_nonneg hρ0.le (tanh_nonneg_of_nonneg (by positivity))
  rw [e2, Pi.smul_apply, e3, smul_eq_mul, norm_mul, mul_pow, norm_oppTrans s l _ hρ0.le, mul_pow,
    Real.sq_sqrt ht, hpi, norm_mul, norm_pow, norm_oppPairing_neg_of_smooth s l hg hgc,
    norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  field_simp

end Lightlike.Lorentz.SL2RPlancherel
