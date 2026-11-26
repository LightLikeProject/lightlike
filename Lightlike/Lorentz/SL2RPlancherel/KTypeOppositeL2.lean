import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderOppositeSurjective
import Lightlike.Lorentz.SL2RPlancherel.KTypeBlockL2

/-!
# The `K`-type `(l, -s)` Plancherel isometry on the ladder images of an opposite-sign block

For natural `l, s`, the map sending a radial generator `G` to `ξ ↦ π √(sinh ξ) · HcN s G l ξ` in
`L²(0, ∞)` (`blockEN`) has the same norm as the weighted transform `blockF s l G` of the same-sign
case (`norm_blockFN`, from `norm_sq_ktype_opp`).  Layer 2c-v of the Plancherel formula on
`SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `HcN s G l` vanishes for `|ξ|` large. -/
theorem hasCompactSupport_HcN (s : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) (l : ℕ) :
    HasCompactSupport (HcN s G l) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hGR : ∀ v, R < v → G v = 0 := fun v hv => image_eq_zero_of_notMem_tsupport fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_abs_self v]
  set A : ℝ := 2 * |R| + 2 with hA
  refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun ξ hξ => ?_
  have hξA : A < |ξ| := by
    by_contra h
    exact hξ (abs_le.mp (not_lt.mp h))
  have hcosh : R < Real.cosh ξ := by
    have h1 := cosh_ge_half |ξ|
    rw [Real.cosh_abs] at h1
    have := le_abs_self R
    linarith
  unfold HcN
  split_ifs
  · simp [qRec_eq_zero_of_gt s hGR l _ hcosh]
  · have hev : qRec s G s =ᶠ[𝓝 (Real.cosh ξ)] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hcosh] with w hw using qRec_eq_zero_of_gt s hGR s w hw
    rw [hev.iteratedDeriv_eq]
    simp

/-- `qRec` is homogeneous. -/
theorem qRec_smul (s : ℕ) (c : ℂ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    qRec s (c • G) l = c • qRec s G l := by
  induction l with
  | zero => simp only [qRec]; funext v; rw [Pi.smul_apply, iteratedDeriv_const_smul_field]
  | succ l ih =>
    funext v
    have dG := ((contDiff_qRec s hG l).differentiable (by simp)) v
    simp only [qRec, Pi.smul_apply, smul_eq_mul]
    rw [ih, show (c • qRec s G l) = fun w => c * qRec s G l w from rfl, deriv_const_mul _ dG]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- `HcN` is homogeneous. -/
theorem HcN_smul (s : ℕ) (c : ℂ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) (ξ : ℝ) :
    HcN s (c • G) l ξ = c * HcN s G l ξ := by
  unfold HcN
  split_ifs
  · rw [qRec_smul s c hG l, Pi.smul_apply, smul_eq_mul]; ring
  · rw [qRec_smul s c hG s, iteratedDeriv_const_smul_field, smul_eq_mul]; ring

/-- The source map of an opposite-sign block: `G ↦ π √(sinh ξ) HcN s G l ξ`. -/
def blockSrcN (s l : ℕ) (G : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ((Real.pi * Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * HcN s G l ξ

theorem memLp_blockSrcN (s l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    MemLp (blockSrcN s l G) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : Continuous (blockSrcN s l G) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sqrt.comp Real.continuous_sinh))).mul (continuous_HcN s hG l)
  exact hcont.memLp_of_hasCompactSupport (hasCompactSupport_HcN s hc l).mul_left

theorem integral_norm_sq_blockSrcN (s l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) :
    ∫ ξ in Ioi (0 : ℝ), ‖blockSrcN s l G ξ‖ ^ 2 =
      Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ), ‖hLRN s G l ξ‖ ^ 2 * Real.sinh ξ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  rw [blockSrcN, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hs, HcN_eq_hLRN s hG l hξ]
  ring

/-- The source map as a linear map from the test functions to `L²(0, ∞)`. -/
def blockEN (s l : ℕ) : smoothCS →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) where
  toFun G := (memLp_blockSrcN s l G.2.1 G.2.2).toLp (blockSrcN s l G)
  map_add' F G := by
    have h : blockSrcN s l ((F + G : smoothCS) : ℝ → ℂ) = blockSrcN s l F + blockSrcN s l G := by
      funext ξ
      simp only [blockSrcN, Pi.add_apply]
      rw [show ((F + G : smoothCS) : ℝ → ℂ) = (F : ℝ → ℂ) + G from rfl, HcN_add s F.2.1 G.2.1 l ξ,
        mul_add]
    rw [← MemLp.toLp_add (memLp_blockSrcN s l F.2.1 F.2.2) (memLp_blockSrcN s l G.2.1 G.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)
  map_smul' c F := by
    have h : blockSrcN s l ((c • F : smoothCS) : ℝ → ℂ) = c • blockSrcN s l F := by
      funext ξ
      simp only [blockSrcN, Pi.smul_apply, smul_eq_mul]
      rw [show ((c • F : smoothCS) : ℝ → ℂ) = c • (F : ℝ → ℂ) from rfl, HcN_smul s c F.2.1 l ξ]
      ring
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_blockSrcN s l F.2.1 F.2.2)]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq h)

/-- **The opposite-sign block Plancherel identity on generators**: `‖blockF s l G‖ = ‖blockEN s l G‖`
(the weights `w_l w_s` are those of the same-sign block `(l, s)`). -/
theorem norm_blockFN (s l : ℕ) (G : smoothCS) : ‖blockF s l G‖ = ‖blockEN s l G‖ := by
  have h1 : blockF s l G = (memLp_blockTgt s l G.2.1 G.2.2).toLp (blockTgt s l G) := rfl
  have h2 : blockEN s l G = (memLp_blockSrcN s l G.2.1 G.2.2).toLp (blockSrcN s l G) := rfl
  rw [h1, h2, norm_toLp_two, norm_toLp_two, integral_norm_sq_blockTgt, integral_norm_sq_blockSrcN s l G.2.1,
    norm_sq_ktype_opp G.2.1 G.2.2 s l]

/-- **The size of the discrete directions**: for `l - s ≤ i < l` and `ξ > 0`,
`φ_i(ξ)² sinh ξ ≤ sinh ξ / (1 + cosh ξ)² ≤ 2 e^{-ξ}`. -/
theorem phiN_sq_mul_sinh_le (s l i : ℕ) (hli : l ≤ i + s) (hil : i < l) {ξ : ℝ} (hξ : 0 < ξ) :
    phiN s l i ξ ^ 2 * Real.sinh ξ ≤ 2 * Real.exp (-ξ) := by
  have hc1 : 1 < Real.cosh ξ := Real.one_lt_cosh.2 (ne_of_gt hξ)
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.2 hξ
  have hsq : Real.sinh ξ ^ 2 = (Real.cosh ξ - 1) * (Real.cosh ξ + 1) := by
    have := Real.cosh_sq_sub_sinh_sq ξ; nlinarith
  have hc0 : 0 < Real.cosh ξ - 1 := sub_pos.2 hc1
  have hcp : 0 < Real.cosh ξ + 1 := by linarith
  -- `φ_i² = (c-1)^e / (c+1)^(l+s)` with `e = 2i + s - l`
  obtain ⟨e, he⟩ : ∃ e, 2 * (i + s) = e + (l + s) := ⟨2 * (i + s) - (l + s), by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, l + s = e + (d + 2) := ⟨l + s - e - 2, by omega⟩
  have hphi : phiN s l i ξ ^ 2 = (Real.cosh ξ - 1) ^ e / (Real.cosh ξ + 1) ^ (l + s) := by
    rw [phiN, div_pow, ← pow_mul, ← pow_mul, mul_comm (i + s), he, mul_comm (l + s) 2, pow_mul, hsq,
      mul_pow, pow_add]
    field_simp
  have h1 : (Real.cosh ξ - 1) ^ e ≤ (Real.cosh ξ + 1) ^ e :=
    pow_le_pow_left₀ hc0.le (by linarith) e
  have h2 : phiN s l i ξ ^ 2 ≤ 1 / (Real.cosh ξ + 1) ^ 2 := by
    rw [hphi, hd, pow_add, pow_add]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (1 : ℝ) ≤ (Real.cosh ξ + 1) ^ d := one_le_pow₀ (by linarith)
    calc (Real.cosh ξ - 1) ^ e * (Real.cosh ξ + 1) ^ 2
        ≤ (Real.cosh ξ + 1) ^ e * (Real.cosh ξ + 1) ^ 2 * 1 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Real.cosh ξ + 1) ^ e * (Real.cosh ξ + 1) ^ 2 * (Real.cosh ξ + 1) ^ d :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 * ((Real.cosh ξ + 1) ^ e * ((Real.cosh ξ + 1) ^ d * (Real.cosh ξ + 1) ^ 2)) := by ring
  -- `sinh / (c + 1)² ≤ 2 e^{-ξ}`
  have hsh : Real.sinh ξ ≤ Real.exp ξ / 2 := by
    rw [Real.sinh_eq]; have := Real.exp_pos (-ξ); linarith
  have hch : Real.exp ξ / 2 ≤ Real.cosh ξ + 1 := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-ξ); linarith
  have hE : 0 < Real.exp ξ := Real.exp_pos ξ
  calc phiN s l i ξ ^ 2 * Real.sinh ξ ≤ 1 / (Real.cosh ξ + 1) ^ 2 * Real.sinh ξ :=
        mul_le_mul_of_nonneg_right h2 hs.le
    _ ≤ 1 / (Real.exp ξ / 2) ^ 2 * (Real.exp ξ / 2) := by
        apply mul_le_mul _ hsh hs.le (by positivity)
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hch 2)
    _ = 2 * Real.exp (-ξ) := by
        rw [Real.exp_neg]; field_simp

/-- The discrete direction `√(sinh ξ) φ_i(ξ)` of the opposite-sign block, as a function. -/
def phiSrc (s l i : ℕ) (ξ : ℝ) : ℂ := ((Real.sqrt (Real.sinh ξ) * phiN s l i ξ : ℝ) : ℂ)

theorem memLp_phiSrc (s l i : ℕ) (hli : l ≤ i + s) (hil : i < l) :
    MemLp (phiSrc s l i) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hcont : ContinuousOn (phiSrc s l i) (Ioi 0) := by
    refine Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_sqrt.comp Real.continuous_sinh).continuousOn.mul ?_)
    refine ((Real.continuous_cosh.sub continuous_const).pow _).continuousOn.div
      (Real.continuous_sinh.pow _).continuousOn fun ξ hξ => ?_
    exact pow_ne_zero _ (Real.sinh_pos_iff.2 hξ).ne'
  rw [memLp_two_iff_integrable_sq_norm (hcont.aestronglyMeasurable measurableSet_Ioi)]
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul 2)
    ((hcont.aestronglyMeasurable measurableSet_Ioi).norm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hs : 0 ≤ Real.sinh ξ := (Real.sinh_pos_iff.2 hξ).le
  rw [norm_pow, norm_norm, phiSrc, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt hs, mul_comm]
  exact phiN_sq_mul_sinh_le s l i hli hil hξ

end Lightlike.Lorentz.SL2RPlancherel
