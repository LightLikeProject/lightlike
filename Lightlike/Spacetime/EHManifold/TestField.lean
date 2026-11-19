import Lightlike.Spacetime.EHManifold.ManifoldStationary

/-!
# Test tensor fields in a chart, and the fundamental lemma for contractions

* `testField x₁ hη hηc hηs a b`: the symmetric tensor field with components `η (E_ab + E_ba)` in the chart at
  `x₁`, for a test function `η` supported in the chart target.
* `setIntegral_testField`: for an integrand `I h p` that is continuous on the chart domain and equals
  `h_{αβ} U^{αβ}` in the chart, its integral over the support of the test field is
  `∫ √|g| η (U^{ab} + U^{ba})`.
* `symm_part_eq_zero_of_forall_test`: if `∫ √|g| η (U^{ab} + U^{ba}) = 0` for all test functions `η`, then
  `U^{ab} + U^{ba} = 0` on the chart target (the fundamental lemma of the calculus of variations).

Supporting lemmas for stationarity statements; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M]

/-- The symmetric matrix `E_ab + E_ba`. -/
def testMatrix (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if i = a ∧ j = b then (1 : ℝ) else 0) + (if i = b ∧ j = a then 1 else 0)

lemma testMatrix_symm (a b i j : Fin n) : testMatrix a b i j = testMatrix a b j i := by
  simp only [testMatrix, Matrix.of_apply]
  rw [add_comm]
  simp only [and_comm]

/-- Contracting with `η (E_ab + E_ba)` picks the entries `ab` and `ba`. -/
lemma sum_testMatrix_mul (a b : Fin n) (c : ℝ) (U : Fin n → Fin n → ℝ) :
    ∑ α, ∑ β, (c * testMatrix a b α β) * U α β = c * (U a b + U b a) := by
  simp only [testMatrix, Matrix.of_apply]
  simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']

variable (x₁ : M) {η : (Fin n → ℝ) → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
  (hηs : tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target)

include hηc hηs in
lemma tsupport_chartExtend_subset_baseSet :
    tsupport (chartExtend x₁ η) ⊆ (chartTriv n x₁).baseSet := by
  refine (tsupport_chartExtend_subset x₁ hηc hηs).trans ?_
  rintro _ ⟨z, hz, rfl⟩
  exact symm_mem_chartTriv_baseSet x₁ (hηs hz)

/-- **The test tensor field** with components `η (E_ab + E_ba)` in the chart at `x₁`. -/
def testField (a b : Fin n) : SymBilinField 𝓘(ℝ, Fin n → ℝ) M :=
  SymBilinField.ofChart x₁ (chartExtend x₁ η) (contMDiff_chartExtend x₁ hηc hηs hη)
    (tsupport_chartExtend_subset_baseSet x₁ hηc hηs) (testMatrix a b) (testMatrix_symm a b)

lemma testField_eq_zero (a b : Fin n) {p : M}
    (hp : p ∉ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) :
    (testField x₁ hη hηc hηs a b).h p = 0 :=
  SymBilinField.ofChart_eq_zero x₁ _ _ _ _ _ (chartExtend_eq_zero x₁ hηs hp)

lemma coordComp_testField (a b : Fin n) {y : Fin n → ℝ} (hy : y ∈ tsupport η) (i j : Fin n) :
    (testField x₁ hη hηc hηs a b).coordComp x₁ y i j = η y * testMatrix a b i j := by
  have hyt := hηs hy
  unfold testField
  rw [SymBilinField.coordComp_ofChart x₁ _ _ _ _ _ hyt,
    chartExtend_of_mem x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_target hyt),
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv hyt]

variable [SecondCountableTopology M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M]
  [BorelSpace M]

/-- **The integral of a contraction against a test field**, in the chart. -/
theorem setIntegral_testField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (a b : Fin n)
    (I : SymBilinField 𝓘(ℝ, Fin n → ℝ) M → M → ℝ) (U : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (hIc : ∀ h, ContinuousOn (I h) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source)
    (hIchart : ∀ h, ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target,
      I h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) = ∑ α, ∑ β, h.coordComp x₁ y α β * U y α β) :
    ∫ p in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η,
        I (testField x₁ hη hηc hηs a b) p ∂(NondegMetric.volumeMeasure g) =
      ∫ y in tsupport η, NondegMetric.volDensity g x₁ y * (η y * (U y a b + U y b a)) := by
  have hKc := isCompact_symm_image_tsupport x₁ hηc hηs
  have hK0 := symm_image_tsupport_subset_source x₁ hηs
  have himg : extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) =
      tsupport η := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hw)]
      exact hw
    · intro hz
      exact ⟨_, ⟨z, hz, rfl⟩, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hz)⟩
  have hmeas : AEStronglyMeasurable (I (testField x₁ hη hηc hηs a b))
      ((NondegMetric.volumeMeasure g).restrict ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η)) :=
    ((hIc _).aestronglyMeasurable (isOpen_extChartAt_source x₁).measurableSet).mono_measure
      (Measure.restrict_mono hK0 le_rfl)
  rw [NondegMetric.setIntegral_volumeMeasure_chart g x₁ hKc.measurableSet hK0 _ hmeas, himg]
  refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet fun y hy => ?_
  show NondegMetric.volDensity g x₁ y *
      I (testField x₁ hη hηc hηs a b) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) = _
  rw [hIchart _ y (hηs hy)]
  simp only [coordComp_testField x₁ hη hηc hηs a b hy]
  rw [sum_testMatrix_mul]

/-- **The fundamental lemma for symmetrised components.** -/
theorem symm_part_eq_zero_of_forall_test (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M)
    (a b : Fin n) (U : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (hU : ∀ α β, ContinuousOn (fun y => U y α β) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target)
    (hzero : ∀ η : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target →
      ∫ y in tsupport η, NondegMetric.volDensity g x₁ y * (η y * (U y a b + U y b a)) = 0)
    {y₀ : Fin n → ℝ} (hy₀ : y₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    U y₀ a b + U y₀ b a = 0 := by
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ,
      f = fun y => NondegMetric.volDensity g x₁ y * (U y a b + U y b a) := ⟨_, rfl⟩
  have hfc : ContinuousOn f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
    rw [hf]
    exact (NondegMetric.continuousOn_volDensity g x₁).mul ((hU a b).add (hU b a))
  have hTo : IsOpen (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := isOpen_extChartAt_target x₁
  have hz : ∀ η : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → ∫ y, η y • f y = 0 := by
    intro η hη hηc hηs
    have hsuppz : ∀ y, y ∉ tsupport η → η y • f y = 0 := by
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsuppz, ← hzero η hη hηc hηs]
    refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet fun y _ => ?_
    show η y • f y = NondegMetric.volDensity g x₁ y * (η y * (U y a b + U y b a))
    rw [hf, smul_eq_mul]
    ring
  have hae := hTo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hfc.locallyIntegrableOn hTo.measurableSet) hz
  have hopen : IsOpen ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0}) :=
    hfc.isOpen_inter_preimage hTo isOpen_ne
  have hnull0 : volume {y : Fin n → ℝ | ¬(y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → f y = 0)} = 0 :=
    ae_iff.1 hae
  have hsub : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} ⊆
      {y : Fin n → ℝ | ¬(y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → f y = 0)} :=
    fun y hy himp => hy.2 (himp hy.1)
  have hempty : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} = ∅ :=
    (hopen.measure_eq_zero_iff volume).1 (measure_mono_null hsub hnull0)
  have hfy : f y₀ = 0 := by
    by_contra hne
    have hmem : y₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} := ⟨hy₀, hne⟩
    rw [hempty] at hmem
    exact hmem
  rw [hf] at hfy
  have hpos : 0 < NondegMetric.volDensity g x₁ y₀ :=
    Real.sqrt_pos.2 (abs_pos.2 (g.coordMetric_isUnit_det x₁ hy₀).ne_zero)
  exact (mul_eq_zero.1 hfy).resolve_left hpos.ne'

end Lightlike
