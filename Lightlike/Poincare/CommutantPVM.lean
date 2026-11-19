import Lightlike.Poincare.CommutantTranslations

/-!
# Operators commuting with the translations commute with the momentum projections

If a bounded operator `B` of the one-particle space commutes with every translation, it commutes with every
projection `E(U)` of the momentum projection-valued measure for `U` open (`commute_momOp_isOpen`: `1_U` is a
pointwise limit of Schwartz functions, `smoothApprox`, bounded by `1`), and then with `E(S)` for every Borel set `S`
(`commute_momOp`, Dynkin's `π`-`λ` theorem).

Supporting results for the irreducibility of the one-particle representations; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology BoundedContinuousFunction SchwartzMap Real
open scoped InnerProductSpace ContDiff

namespace Lightlike.Poincare

noncomputable section

/-! ## Smooth approximations of the indicator of an open set -/

/-- `ψ(k f) χ_k`, with `f` smooth of support `U` and `χ_k` a bump equal to `1` on the ball of radius `k`. -/
def smoothApproxFun (f : MomSpace → ℝ) (k : ℕ) : MomSpace → ℂ := fun p =>
  ((smoothTransition (k * f p) *
    (⟨k + 1, k + 2, by positivity, by linarith⟩ : ContDiffBump (0 : MomSpace)) p : ℝ) : ℂ)

lemma smoothApproxFun_contDiff {f : MomSpace → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (smoothApproxFun f k) := by
  unfold smoothApproxFun
  refine Complex.ofRealCLM.contDiff.comp ?_
  exact ((smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.mul hf)).mul (ContDiffBump.contDiff _)

lemma smoothApproxFun_hasCompactSupport (f : MomSpace → ℝ) (k : ℕ) :
    HasCompactSupport (smoothApproxFun f k) := by
  have h := (⟨k + 1, k + 2, by positivity, by linarith⟩ : ContDiffBump (0 : MomSpace)).hasCompactSupport
  refine h.mono fun p hp => ?_
  intro hb
  apply hp
  simp only [smoothApproxFun]
  rw [hb, mul_zero, Complex.ofReal_zero]

/-- The Schwartz approximations of `1_U`. -/
def smoothApprox {f : MomSpace → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) : 𝓢(MomSpace, ℂ) :=
  (smoothApproxFun_hasCompactSupport f k).toSchwartzMap (smoothApproxFun_contDiff hf k)

lemma norm_smoothApproxFun_le (f : MomSpace → ℝ) (k : ℕ) (p : MomSpace) : ‖smoothApproxFun f k p‖ ≤ 1 := by
  unfold smoothApproxFun
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (smoothTransition.nonneg _)
    (ContDiffBump.nonneg' _ _))]
  exact mul_le_one₀ (smoothTransition.le_one _) (ContDiffBump.nonneg' _ _) (ContDiffBump.le_one _)

lemma tendsto_smoothApproxFun {f : MomSpace → ℝ} (hf0 : ∀ p, 0 ≤ f p) (p : MomSpace) :
    Tendsto (fun k : ℕ => smoothApproxFun f k p) atTop
      (𝓝 ((Function.support f).indicator (fun _ => (1 : ℂ)) p)) := by
  -- the bump is eventually `1` at `p`
  have hbump : ∀ᶠ k : ℕ in atTop, (⟨k + 1, k + 2, by positivity, by linarith⟩ :
      ContDiffBump (0 : MomSpace)) p = 1 := by
    filter_upwards [eventually_ge_atTop ⌈‖p‖⌉₊] with k hk
    refine ContDiffBump.one_of_mem_closedBall _ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have := Nat.le_ceil ‖p‖
    have : (⌈‖p‖⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  by_cases hp : p ∈ Function.support f
  · rw [Set.indicator_of_mem hp]
    have hpos : 0 < f p := lt_of_le_of_ne (hf0 p) (Ne.symm hp)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hbump, eventually_ge_atTop ⌈1 / f p⌉₊] with k hk1 hk2
    have h1 : 1 ≤ (k : ℝ) * f p := by
      have : 1 / f p ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk2)
      rw [div_le_iff₀ hpos] at this
      linarith
    simp [smoothApproxFun, hk1, smoothTransition.one_of_one_le h1]
  · rw [Set.indicator_of_notMem hp]
    have h0 : f p = 0 := Function.notMem_support.1 hp
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
    simp [smoothApproxFun, h0]

/-! ## Strong convergence to the projection -/

variable {m : ℝ} {μ : Measure (MassShell m)} {n : ℕ}

/-- The open set of momenta of `MomSpace` corresponding to an open set of `ℝ⁴`. -/
lemma momE_mem_iff (U : Set (Fin 4 → ℝ)) (Q : MassShell m) :
    momE Q ∈ (WithLp.toLp 2 '' U : Set MomSpace) ↔ mom Q ∈ U := by
  constructor
  · rintro ⟨x, hx, hxQ⟩
    have : x = mom Q := by
      have := congrArg (WithLp.ofLp (p := 2)) hxQ
      simpa [momE] using this
    rwa [← this]
  · exact fun h => ⟨mom Q, h, rfl⟩

lemma tendsto_bcfMul_smoothApprox {U : Set (Fin 4 → ℝ)} (hU : MeasurableSet U) {f : MomSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : ∀ p, 0 ≤ f p) (hfU : Function.support f = WithLp.toLp 2 '' U)
    (v : Lp (Spinor n) 2 μ) :
    Tendsto (fun k : ℕ => bcfMul (schwartzMom (smoothApprox hf k)) v) atTop
      (𝓝 (momPVM (μ := μ) (n := n) U v)) := by
  change Tendsto _ atTop (𝓝 (momOp U v))
  rw [momOp_of_measurable hU, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hvm := Lp.aestronglyMeasurable v
  set G : ℕ → MassShell m → Spinor n := fun k Q => smoothApproxFun f k (momE Q) • v Q -
    (mom ⁻¹' U).indicator v Q
  have hcongr : ∀ k : ℕ, eLpNorm (⇑(bcfMul (schwartzMom (smoothApprox hf k)) v) -
      ⇑(indOp (μ := μ) (mom ⁻¹' U) (measurable_mom hU) v)) 2 μ = eLpNorm (G k) 2 μ := fun k =>
    eLpNorm_congr_ae ((coeFn_bcfMul _ v).sub (coeFn_indOp _ v))
  simp only [hcongr]
  have hGm : ∀ k, AEStronglyMeasurable (G k) μ := fun k =>
    ((((smoothApproxFun_contDiff hf k).continuous.comp continuous_momE).aestronglyMeasurable).smul hvm).sub
      (hvm.indicator (measurable_mom hU))
  have hlim : Tendsto (fun k : ℕ => ∫⁻ Q, ‖G k Q‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun Q => (2 * ‖v Q‖ₑ) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun k => ((hGm k).enorm.pow_const _)
    · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun Q => ?_
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      refine (enorm_sub_le).trans ?_
      have h1 : ‖smoothApproxFun f k (momE Q) • v Q‖ₑ ≤ ‖v Q‖ₑ := by
        rw [enorm_smul]
        calc ‖smoothApproxFun f k (momE Q)‖ₑ * ‖v Q‖ₑ ≤ 1 * ‖v Q‖ₑ := by
              gcongr
              rw [← ofReal_norm, ← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (norm_smoothApproxFun_le f k _)
          _ = ‖v Q‖ₑ := one_mul _
      have h2 : ‖(mom ⁻¹' U).indicator v Q‖ₑ ≤ ‖v Q‖ₑ := by
        by_cases h : Q ∈ mom ⁻¹' U
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, enorm_zero]; exact zero_le'
      calc _ ≤ ‖v Q‖ₑ + ‖v Q‖ₑ := add_le_add h1 h2
        _ = 2 * ‖v Q‖ₑ := by ring
    · have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        (Lp.memLp v).eLpNorm_lt_top
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) (by simpa using h.ne)
    · refine Filter.Eventually.of_forall fun Q => ?_
      have h := ((tendsto_smoothApproxFun hf0 (momE Q)).smul_const (v Q)).sub_const
        ((mom ⁻¹' U).indicator v Q)
      have hind : (Function.support f).indicator (fun _ => (1 : ℂ)) (momE Q) • v Q -
          (mom ⁻¹' U).indicator v Q = 0 := by
        rw [hfU]
        by_cases hQ : Q ∈ mom ⁻¹' U
        · rw [Set.indicator_of_mem ((momE_mem_iff U Q).2 hQ), Set.indicator_of_mem hQ, one_smul, sub_self]
        · rw [Set.indicator_of_notMem (fun h => hQ ((momE_mem_iff U Q).1 h)), Set.indicator_of_notMem hQ,
            zero_smul, sub_self]
      rw [hind] at h
      have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
  rw [lintegral_zero] at hlim
  have hlim2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim2
  refine hlim2.congr' (Filter.Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hGm k)]
  norm_num

/-! ## Commutation with the momentum projections -/

/-- `B` commutes with `E(U)` for `U` open. -/
theorem commute_momOp_isOpen [SFinite μ] (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)
    (hB : ∀ a f, B (translL2 n a f) = translL2 n a (B f)) {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (v : Lp (Spinor n) 2 μ) : B (momPVM (μ := μ) U v) = momPVM (μ := μ) U (B v) := by
  have hU' : IsOpen (WithLp.toLp 2 '' U : Set MomSpace) :=
    (PiLp.homeomorph 2 (fun _ : Fin 4 => ℝ)).symm.isOpenMap U hU
  obtain ⟨f, hfs, hf, hfr⟩ := hU'.exists_contDiff_support_eq (n := ⊤)
  have hf0 : ∀ p, 0 ≤ f p := fun p => (hfr ⟨p, rfl⟩).1
  have h2 := tendsto_bcfMul_smoothApprox (μ := μ) hU.measurableSet hf hf0 hfs (B v)
  have h1' : Tendsto (fun k : ℕ => B (bcfMul (schwartzMom (smoothApprox hf k)) v)) atTop
      (𝓝 (B (momPVM (μ := μ) U v))) := B.continuous.continuousAt.tendsto.comp
    (tendsto_bcfMul_smoothApprox hU.measurableSet hf hf0 hfs v)
  refine tendsto_nhds_unique h1' (h2.congr fun k => ?_)
  exact (commute_bcfMul_schwartz B hB (smoothApprox hf k) v).symm

lemma momOp_compl {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) (v : Lp (Spinor n) 2 μ) :
    momPVM (μ := μ) Sᶜ v = v - momPVM (μ := μ) S v := by
  change momOp Sᶜ v = v - momOp S v
  rw [momOp_of_measurable hS.compl, momOp_of_measurable hS]
  apply Lp.ext
  filter_upwards [coeFn_indOp (μ := μ) (measurable_mom hS.compl) v, Lp.coeFn_sub v
    (indOp (μ := μ) (mom ⁻¹' S) (measurable_mom hS) v), coeFn_indOp (μ := μ) (measurable_mom hS) v]
    with Q h1 h2 h3
  rw [h1, h2, Pi.sub_apply, h3]
  by_cases hQ : Q ∈ mom ⁻¹' S
  · rw [Set.indicator_of_notMem (show Q ∉ mom ⁻¹' Sᶜ from fun h => h hQ), Set.indicator_of_mem hQ, sub_self]
  · rw [Set.indicator_of_mem (show Q ∈ mom ⁻¹' Sᶜ from hQ), Set.indicator_of_notMem hQ, sub_zero]

/-- **`B` commutes with every momentum projection** `E(S)`, `S` Borel. -/
theorem commute_momOp [SFinite μ] (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)
    (hB : ∀ a f, B (translL2 n a f) = translL2 n a (B f)) {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S)
    (v : Lp (Spinor n) 2 μ) : B (momPVM (μ := μ) S v) = momPVM (μ := μ) S (B v) := by
  revert v
  refine MeasurableSpace.induction_on_inter (C := fun S _ => ∀ v, B (momPVM (μ := μ) S v) =
    momPVM (μ := μ) S (B v)) (BorelSpace.measurable_eq (α := Fin 4 → ℝ)) isPiSystem_isOpen ?_ ?_ ?_ ?_ S hS
  · intro v
    have h0 : momPVM (μ := μ) (n := n) ∅ = 0 := by
      have h := momPVM_eq_zero_of_disjoint (μ := μ) (n := n) (Set.empty_disjoint forwardCone)
      exact h
    rw [h0]
    simp
  · intro U hU v
    exact commute_momOp_isOpen B hB hU v
  · intro t ht h v
    rw [momOp_compl ht, momOp_compl ht, map_sub, h]
  · intro E hd hE h v
    have h1 := (hasSum_momOp (μ := μ) E hE hd v).map B B.continuous
    have h2 := hasSum_momOp (μ := μ) E hE hd (B v)
    have e : (⇑B ∘ fun j => (momOp (μ := μ) (n := n) (E j)) v) = fun j => momOp (E j) (B v) :=
      funext fun j => h j v
    rw [e] at h1
    exact h1.unique h2

end

end Lightlike.Poincare
