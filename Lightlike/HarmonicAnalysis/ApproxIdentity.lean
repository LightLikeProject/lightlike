import Lightlike.HarmonicAnalysis.ConvolutionFormula

/-!
# Approximate identities for the convolution operator

For a continuous function `ψ` on a compact Hausdorff group and `ε > 0` there is a continuous function `φ`
with `φ(z⁻¹) = conj φ(z)` such that the convolution operator `K_φ` moves `ψ` by at most `ε` in the sup norm.
The function `φ` is a normalised symmetric bump supported in a neighbourhood of `1` on which `ψ` varies by
less than `ε` (generalised tube lemma).

Supporting lemma for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory Filter Topology

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- A neighbourhood of `1` on which right translates of `ψ` move it by less than `ε`. -/
lemma eventually_forall_norm_sub_lt (ψ : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (1 : G), ∀ x : G, ‖ψ (x * w) - ψ x‖ < ε := by
  have key := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (1 : G))
    (P := fun w x => ‖ψ (x * w) - ψ x‖ < ε) (K := (Set.univ : Set G)) fun x _ => by
      have hg : Continuous fun z : G × G => ‖ψ (z.2 * z.1) - ψ z.2‖ := by fun_prop
      refine hg.continuousAt.eventually_lt continuousAt_const ?_
      simpa using hε
  exact key.mono fun w hw x => hw x (Set.mem_univ _)

/-- A symmetric nonnegative bump of integral one supported in a neighbourhood of `1`. -/
lemma exists_symm_bump {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ φ : C(G, ℝ), (∀ z, 0 ≤ φ z) ∧ (∀ z, φ z⁻¹ = φ z) ∧ (∀ z, φ z ≠ 0 → z ∈ W) ∧
      ∫ z, φ z ∂μ = 1 := by
  obtain ⟨V, hVW, hVo, hV1⟩ := mem_nhds_iff.1 hW
  have hVo' : IsOpen (V ∩ V⁻¹) := hVo.inter hVo.inv
  have h1 : (1 : G) ∈ V ∩ V⁻¹ := ⟨hV1, by simpa using hV1⟩
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hVo'.isClosed_compl
    (isClosed_singleton (x := (1 : G))) (Set.disjoint_singleton_right.2 (by simpa using h1))
  let φ0 : C(G, ℝ) := ⟨fun z => f z * f z⁻¹, by fun_prop⟩
  have hφ0nn : ∀ z, 0 ≤ φ0 z := fun z => mul_nonneg (hf01 z).1 (hf01 z⁻¹).1
  have hφ01 : φ0 1 = 1 := by simp [φ0, hf1 (Set.mem_singleton _)]
  have hpos : 0 < ∫ z, φ0 z ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : G)) φ0.continuous
      (HasCompactSupport.of_compactSpace _) hφ0nn (by rw [hφ01]; norm_num)
  refine ⟨(∫ z, φ0 z ∂μ)⁻¹ • φ0, fun z => ?_, fun z => ?_, fun z hz => ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 hpos.le) (hφ0nn z)
  · simp [φ0, mul_comm]
  · by_contra hzW
    have hzV : z ∉ V ∩ V⁻¹ := fun h => hzW (hVW h.1)
    have : f z = 0 := hf0 (by simpa using hzV)
    simp [φ0, this] at hz
  · simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

/-- **Approximate identity.** For `ψ` continuous and `ε > 0` there is a function `φ` with `φ(z⁻¹) = conj φ(z)`
such that `K_φ ψ` is within `ε` of `ψ` uniformly. -/
theorem exists_approx_identity (ψ : C(G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : C(G, ℂ), (∀ z, φ z⁻¹ = starRingEnd ℂ (φ z)) ∧
      ∀ x, ‖convToC μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) x - ψ x‖ ≤ ε := by
  have hev := eventually_forall_norm_sub_lt ψ hε
  obtain ⟨φr, hnn, hsym, hsupp, hint⟩ := exists_symm_bump μ
    (W := {w | ∀ x : G, ‖ψ (x * w) - ψ x‖ < ε}) hev
  let φ : C(G, ℂ) := ⟨fun z => (φr z : ℂ), by fun_prop⟩
  have hφ : ∀ z, φ z = (φr z : ℂ) := fun z => rfl
  refine ⟨φ, fun z => by simp [hφ, hsym z], fun x => ?_⟩
  rw [convToC_toLp_apply]
  have h1 : ∫ y, φ (y⁻¹ * x) * ψ y ∂μ = ∫ w, φ w * ψ (x * w) ∂μ := by
    rw [← integral_mul_left_eq_self (fun y => φ (y⁻¹ * x) * ψ y) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [mul_inv_rev, inv_mul_cancel_right, hφ, hsym w]
  have hint1 : ∫ w, φ w ∂μ = 1 := by
    simp only [hφ]
    rw [integral_complex_ofReal, hint]; simp
  have h2 : ψ x = ∫ w, φ w * ψ x ∂μ := by
    rw [integral_mul_const, hint1, one_mul]
  have hI1 : Integrable (fun w => φ w * ψ (x * w)) μ :=
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
  have hI2 : Integrable (fun w => φ w * ψ x) μ :=
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
  rw [h1]
  conv_lhs => rw [show (∫ w, φ w * ψ (x * w) ∂μ) - ψ x =
    (∫ w, φ w * ψ (x * w) ∂μ) - ∫ w, φ w * ψ x ∂μ by rw [← h2]]
  rw [← integral_sub hI1 hI2]
  have hg : Integrable (fun w => ε * φr w) μ :=
    (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
  calc ‖∫ w, (φ w * ψ (x * w) - φ w * ψ x) ∂μ‖ ≤ ∫ w, ε * φr w ∂μ := by
        refine norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun w => ?_)
        by_cases hw : φr w = 0
        · simp [hφ, hw]
        · have hlt := hsupp w hw x
          rw [← mul_sub, norm_mul, hφ, Complex.norm_real, Real.norm_of_nonneg (hnn w)]
          nlinarith [hnn w]
    _ = ε := by rw [integral_const_mul, hint, mul_one]

end

end Lightlike.HarmonicAnalysis
