import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderSurjective
import Lightlike.Lorentz.SL2RPlancherel.SphericalL2

/-!
# The `K`-type `(l, r)` Plancherel isometry of a same-sign block

For natural `l, r` the map sending a radial generator `G` to its `K`-type `(l, r)` ladder image,
`ξ ↦ π √(sinh ξ) · Hc r G l ξ` in `L²(0, ∞)` (`blockE`), and the map sending it to the weighted
transform `ρ ↦ √(ρ tanh(πρ) w_l(ρ) w_r(ρ)) / 2 · Ĝ(ρ)` in `L²(0, ∞)` (`blockF`) have the same norm
(`norm_blockF`, the identity `norm_sq_ktype_lr` of layer 1).  The range of `blockE` is dense
(`denseRange_blockE`: every test function of `(0, ∞)` is a ladder image, `exists_hLR_eq`), so the
weighted transform extends to a linear isometry `blockL2` of `L²(0, ∞)`: the Plancherel formula of
the block (its surjectivity onto the weighted spectral side is not shown here).  Layer 2c-v of the Plancherel formula
on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `uRec` is homogeneous on `v > -1`. -/
theorem uRec_smul (r : ℕ) (c : ℂ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ∀ v : ℝ, -1 < v → uRec r (c • G) l v = c * uRec r G l v := by
  induction l with
  | zero =>
    intro v _
    simp only [uRec]
    rw [iteratedDeriv_const_smul_field, smul_eq_mul]
  | succ l ih =>
    intro v hv
    have hev : uRec r (c • G) l =ᶠ[𝓝 v] fun w => c * uRec r G l w :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hv) (fun y hy => ih y hy)
    have dG : DifferentiableAt ℝ (uRec r G l) v :=
      ((uRec_contDiffOn r hG l).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hv)
    show deriv (uRec r (c • G) l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r (c • G) l v =
      c * (deriv (uRec r G l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r G l v)
    rw [hev.deriv_eq, ih v hv, deriv_const_mul _ dG]
    ring

theorem Hc_smul (r : ℕ) (c : ℂ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) (ξ : ℝ) :
    Hc r (c • G) l ξ = c * Hc r G l ξ := by
  unfold Hc
  rw [uRec_smul r c hG l _ (by linarith [Real.one_le_cosh ξ])]
  ring

/-- `uRec` vanishes where the generator vanishes on a half-line. -/
theorem uRec_eq_zero_of_ge (r : ℕ) {G : ℝ → ℂ} {R : ℝ} (hGR : ∀ v, R < v → G v = 0) (l : ℕ) :
    ∀ v, R < v → uRec r G l v = 0 := by
  induction l with
  | zero =>
    intro v hv
    have hev : G =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using hGR w hw
    simp only [uRec]
    rw [hev.iteratedDeriv_eq]
    simp
  | succ l ih =>
    intro v hv
    have hev : uRec r G l =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hv] with w hw using ih w hw
    show deriv (uRec r G l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r G l v = 0
    rw [hev.deriv_eq, ih v hv]
    simp

/-- `Hc r G l` has compact support for a compactly supported `G` (it is continuous: `continuous_Hc`). -/
theorem hasCompactSupport_Hc (r : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) (l : ℕ) :
    HasCompactSupport (Hc r G l) := by
  obtain ⟨R, hR⟩ := (hc.isCompact.isBounded.subset_closedBall 0)
  have hGR : ∀ v, R < v → G v = 0 := fun v hv => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self v]
  set A : ℝ := Real.arcosh (|R| + 1) with hA
  have hA0 : 0 ≤ A := Real.arcosh_nonneg (by linarith [abs_nonneg R])
  have hcA : Real.cosh A = |R| + 1 := Real.cosh_arcosh (by linarith [abs_nonneg R])
  refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun ξ hξ => ?_
  have hξA : A < |ξ| := by
    by_contra h
    exact hξ (abs_le.mp (not_lt.mp h))
  have hcosh : R < Real.cosh ξ := by
    have h1 : Real.cosh A < Real.cosh ξ := Real.cosh_lt_cosh.2 (by rwa [abs_of_nonneg hA0])
    linarith [le_abs_self R]
  simp [Hc, uRec_eq_zero_of_ge r hGR l _ hcosh]

/-- The source map: `G ↦ π √(sinh ξ) Hc r G l ξ`. -/
def blockSrc (r l : ℕ) (G : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * Hc r G l ξ

/-- The target map: `G ↦ √(ρ tanh(πρ) w_l w_r) / 2 · Ĝ(ρ)`. -/
def blockTgt (r l : ℕ) (G : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ((Real.sqrt (ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ) / 2 : ℝ) : ℂ) * sphTransformH G ρ

lemma wl_nonneg (l : ℕ) (ρ : ℝ) : 0 ≤ wl l ρ :=
  Finset.prod_nonneg fun k _ => by positivity

lemma continuous_wl (l : ℕ) : Continuous (wl l) :=
  continuous_finset_prod _ fun _ _ => (continuous_const.add (continuous_id.pow 2)).add continuous_const

/-- The spherical transform of a test function is continuous. -/
lemma continuous_sphTransformH {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    Continuous (sphTransformH G) := by
  have : (fun ρ : ℝ => sphTransformH G ρ) = fun ρ =>
      (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz G hG hc)) (ρ / (2 * Real.pi)) :=
    funext (sphTransformH_eq_schwartz G hG hc)
  rw [show sphTransformH G = fun ρ => sphTransformH G ρ from rfl, this]
  exact (SchwartzMap.fourierTransformCLM ℂ (abelSchwartz G hG hc)).continuous.comp
    (continuous_id.div_const _)

theorem memLp_blockSrc (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    MemLp (blockSrc r l G) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : Continuous (blockSrc r l G) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sqrt.comp Real.continuous_sinh))).mul (continuous_Hc r hG l)
  exact hcont.memLp_of_hasCompactSupport (hasCompactSupport_Hc r hc l).mul_left

theorem integral_norm_sq_blockSrc (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) :
    ∫ ξ in Ioi (0 : ℝ), ‖blockSrc r l G ξ‖ ^ 2 =
      Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖hLR r G l ξ‖ ^ 2 * Real.sinh ξ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  rw [blockSrc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hs, Hc_eq_hLR r hG l hξ]
  ring

theorem memLp_blockTgt (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    MemLp (blockTgt r l G) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hw : Continuous fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ :=
    ((continuous_id.mul continuous_tanh_pi_mul).mul (continuous_wl l)).mul (continuous_wl r)
  have hcont : Continuous (blockTgt r l G) :=
    (Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp hw).div_const 2)).mul
      (continuous_sphTransformH hG hc)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have h := ((LRClaim_all r l G hG hc).1).div_const 4
  refine h.congr (Filter.Eventually.of_forall fun ρ => ?_)
  have hn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ :=
    mul_nonneg (mul_nonneg (mul_tanh_pi_mul_nonneg ρ) (wl_nonneg l ρ)) (wl_nonneg r ρ)
  simp only
  rw [blockTgt, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hn]
  ring

theorem integral_norm_sq_blockTgt (r l : ℕ) {G : ℝ → ℂ} :
    ∫ ρ in Ioi (0 : ℝ), ‖blockTgt r l G ρ‖ ^ 2 = (1 / 4 : ℝ) *
      ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ * ‖sphTransformH G ρ‖ ^ 2 := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ _ => ?_
  have hn : 0 ≤ ρ * Real.tanh (Real.pi * ρ) * wl l ρ * wl r ρ :=
    mul_nonneg (mul_nonneg (mul_tanh_pi_mul_nonneg ρ) (wl_nonneg l ρ)) (wl_nonneg r ρ)
  rw [blockTgt, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hn]
  ring

/-- **The block Plancherel identity on generators**: `‖blockTgt G‖² = ‖blockSrc G‖²` in
`L²(0, ∞)`. -/
theorem integral_norm_sq_blockTgt_eq (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    ∫ ρ in Ioi (0 : ℝ), ‖blockTgt r l G ρ‖ ^ 2 = ∫ ξ in Ioi (0 : ℝ), ‖blockSrc r l G ξ‖ ^ 2 := by
  rw [integral_norm_sq_blockTgt, integral_norm_sq_blockSrc r l hG, norm_sq_ktype_lr hG hc r l]

/-- The source map as a linear map from the test functions to `L²(0, ∞)`. -/
def blockE (r l : ℕ) : smoothCS →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun G := (memLp_blockSrc r l G.2.1 G.2.2).toLp (blockSrc r l G)
  map_add' F G := by
    have h : blockSrc r l ((F + G : smoothCS) : ℝ → ℂ) = blockSrc r l F + blockSrc r l G := by
      funext ξ
      simp only [blockSrc, Pi.add_apply]
      rw [show ((F + G : smoothCS) : ℝ → ℂ) = (F : ℝ → ℂ) + G from rfl, Hc_add r F.2.1 G.2.1 l ξ,
        mul_add]
    rw [← MemLp.toLp_add (memLp_blockSrc r l F.2.1 F.2.2) (memLp_blockSrc r l G.2.1 G.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : blockSrc r l ((c • F : smoothCS) : ℝ → ℂ) = c • blockSrc r l F := by
      funext ξ
      simp only [blockSrc, Pi.smul_apply, smul_eq_mul]
      rw [show ((c • F : smoothCS) : ℝ → ℂ) = c • (F : ℝ → ℂ) from rfl, Hc_smul r c F.2.1 l ξ]
      ring
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_blockSrc r l F.2.1 F.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- The target map as a linear map from the test functions to `L²(0, ∞)`. -/
def blockF (r l : ℕ) : smoothCS →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun G := (memLp_blockTgt r l G.2.1 G.2.2).toLp (blockTgt r l G)
  map_add' F G := by
    have h : blockTgt r l ((F + G : smoothCS) : ℝ → ℂ) = blockTgt r l F + blockTgt r l G := by
      funext ρ
      simp only [blockTgt, Pi.add_apply]
      rw [← mul_add, ← sphTransformH_add F.2.1 F.2.2 G.2.1 G.2.2 ρ]
      rfl
    rw [← MemLp.toLp_add (memLp_blockTgt r l F.2.1 F.2.2) (memLp_blockTgt r l G.2.1 G.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : blockTgt r l ((c • F : smoothCS) : ℝ → ℂ) = c • blockTgt r l F := by
      funext ρ
      simp only [blockTgt, Pi.smul_apply, smul_eq_mul]
      change ((_ : ℝ) : ℂ) * sphTransformH (c • (F : ℝ → ℂ)) ρ = _
      rw [sphTransformH_smul]
      ring
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_blockTgt r l F.2.1 F.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- The isometry property on test functions. -/
theorem norm_blockF (r l : ℕ) (G : smoothCS) : ‖blockF r l G‖ = ‖blockE r l G‖ := by
  have h1 : blockF r l G = (memLp_blockTgt r l G.2.1 G.2.2).toLp (blockTgt r l G) := rfl
  have h2 : blockE r l G = (memLp_blockSrc r l G.2.1 G.2.2).toLp (blockSrc r l G) := rfl
  rw [h1, h2, norm_toLp_two, norm_toLp_two, integral_norm_sq_blockTgt_eq r l G.2.1 G.2.2]

/-- **The ladder images of the radial generators are dense in `L²(0, ∞)`**: the range of `blockE`
is dense.  A vector orthogonal to it is orthogonal to `π √(sinh ξ) H` for every test function `H`
of `(0, ∞)` (`exists_hLR_eq`), hence to every test function, hence zero. -/
theorem denseRange_blockE (r l : ℕ) : DenseRange (blockE r l) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hinv : ContDiffOn ℝ ∞ (fun ξ => (((Real.pi * Real.sqrt (Real.sinh ξ))⁻¹ : ℝ) : ℂ)) (Ioi 0) := by
    have hsq : ContDiffOn ℝ ∞ (fun ξ => Real.sqrt (Real.sinh ξ)) (Ioi 0) :=
      Real.contDiff_sinh.contDiffOn.sqrt fun x hx => (Real.sinh_pos_iff.2 hx).ne'
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_const.mul hsq).inv fun x hx => ?_)
    exact mul_ne_zero Real.pi_ne_zero (Real.sqrt_pos.2 (Real.sinh_pos_iff.2 hx)).ne'
  have hclos : (LinearMap.range (blockE r l)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    have horth : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
        ∫ x, g x • (f : ℝ → ℂ) x = 0 := by
      intro g hg hgc hgsub
      set K : ℝ → ℂ := fun x => ((g x : ℝ) : ℂ) with hK
      have hKs : ContDiff ℝ ∞ K := Complex.ofRealCLM.contDiff.comp hg
      have hKsupp : tsupport K = tsupport g := by simp [hK, tsupport, Function.support]
      set H : ℝ → ℂ := fun x => K x * (((Real.pi * Real.sqrt (Real.sinh x))⁻¹ : ℝ) : ℂ) with hH
      have hHs : ContDiff ℝ ∞ H :=
        contDiff_mul_of_tsupport_subset isOpen_Ioi hKs (hKsupp ▸ hgsub) hinv
      have hHsupp : tsupport H ⊆ tsupport g := by
        rw [← hKsupp]; exact closure_mono (Function.support_mul_subset_left _ _)
      have hHc : HasCompactSupport H := hgc.mono' ((subset_tsupport _).trans hHsupp)
      obtain ⟨G, hGs, hGc, hG⟩ := exists_hLR_eq r l hHs hHc (hHsupp.trans hgsub)
      have h0 : inner ℂ (blockE r l ⟨G, hGs, hGc⟩) f = 0 :=
        (Submodule.mem_orthogonal _ _).1 hf _ (LinearMap.mem_range_self _ _)
      rw [MeasureTheory.L2.inner_def] at h0
      have hcoe : (blockE r l ⟨G, hGs, hGc⟩ : ℝ → ℂ) =ᵐ[μ] blockSrc r l G :=
        MemLp.coeFn_toLp (memLp_blockSrc r l hGs hGc)
      have hsrc : ∀ᵐ x ∂μ, (blockE r l ⟨G, hGs, hGc⟩ : ℝ → ℂ) x = K x := by
        filter_upwards [hcoe, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
        have hs : 0 < Real.sqrt (Real.sinh x) := Real.sqrt_pos.2 (Real.sinh_pos_iff.2 hxpos)
        rw [hx, blockSrc, Hc_eq_hLR r hGs l hxpos, hG x hxpos, hH]
        have hne : ((Real.pi * Real.sqrt (Real.sinh x) : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (mul_pos Real.pi_pos hs).ne'
        have hs' : ((Real.sqrt (Real.sinh x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        push_cast
        field_simp
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) fun x hx => by
        have : x ∉ tsupport g := fun h => hx (hgsub h)
        simp [image_eq_zero_of_notMem_tsupport this]]
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [hsrc] with x hx
      rw [hx, hK, Complex.real_smul]
      simp [mul_comm]
    have hfloc : LocallyIntegrableOn (f : ℝ → ℂ) (Ioi 0) :=
      locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable (by norm_num))
    have key := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hfloc horth
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 key
  have := Submodule.dense_iff_topologicalClosure_eq_top.2 hclos
  rwa [LinearMap.coe_range] at this

/-- **The `K`-type `(l, r)` Plancherel isometry** of a same-sign block (`l, r` natural): the
extension of `π √(sinh ξ) · H(ξ) ↦ √(ρ tanh(πρ) w_l(ρ) w_r(ρ)) / 2 · Ĝ(ρ)` (with `H` the ladder image
of the radial generator `G`) to a linear isometry `L²(0, ∞) → L²(0, ∞)`. -/
def blockL2 (r l : ℕ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) →ₗᵢ[ℂ]
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  LinearMap.extendOfIsometry (blockF r l) (denseRange_blockE r l) (norm_blockF r l)

/-- On ladder images of generators, `blockL2` is the weighted transform. -/
theorem blockL2_apply (r l : ℕ) (G : smoothCS) : blockL2 r l (blockE r l G) = blockF r l G :=
  LinearMap.extendOfIsometry_eq (blockF r l) (denseRange_blockE r l) (norm_blockF r l) G

/-- **The `K`-type `(l, r)` Plancherel identity in `L²`.** -/
theorem norm_blockL2 (r l : ℕ) (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ‖blockL2 r l f‖ = ‖f‖ :=
  (blockL2 r l).norm_map f

/-- Trust check: for the spherical block `(l, r) = (0, 0)` the weighted transform is `π` times the
spherical one of `SphericalL2.lean` (`sphL2fun`, normalised with `1/(2π)`). -/
theorem blockTgt_zero_zero (G : ℝ → ℂ) (ρ : ℝ) : blockTgt 0 0 G ρ = Real.pi * sphL2fun G ρ := by
  simp only [blockTgt, sphL2fun, wl_zero, mul_one]
  push_cast
  field_simp

/-- Non-vacuity: `blockL2_apply` for the zero generator. -/
example (r l : ℕ) : blockL2 r l (blockE r l 0) = blockF r l 0 := blockL2_apply r l 0

end Lightlike.Lorentz.SL2RPlancherel
