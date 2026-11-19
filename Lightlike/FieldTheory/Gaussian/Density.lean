import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The standard Gaussian measure has a density

`Measure.pi (gaussianReal 0 1)` on `ι → ℝ` is Lebesgue measure with density `∏ᵢ φ(xᵢ)`.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι]

/-- The product of standard normal distributions is Lebesgue measure on `ι → ℝ` with the product
density `∏ᵢ φ(xᵢ)`. -/
lemma pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq (μ := fun _ : ι => gaussianReal 0 1) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  set g : ι → ℝ → ℝ := fun i => (s i).indicator (gaussianPDFReal 0 1) with hg
  have hgm : ∀ i, Integrable (g i) := fun i =>
    (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hg0 : ∀ i x, 0 ≤ g i x := fun i x => by
    simp only [hg]; exact Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) x
  have e1 : ∀ x : ι → ℝ, (Set.pi univ s).indicator
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x =
      ENNReal.ofReal (∏ i, g i (x i)) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hg]; rw [Set.indicator_of_mem (hx i (mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra h; push Not at h; exact hx fun i _ => h i
      have : g i (x i) = 0 := by simp only [hg]; exact Set.indicator_of_notMem hi _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this]; simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [e1]
  have hint : Integrable (fun x : ι → ℝ => ∏ i, g i (x i)) := by
    have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℝ)) (f := g) hgm
    simpa [volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    Finset.prod_nonneg fun i _ => hg0 i (x i))]
  have := integral_fintype_prod_eq_prod (μ := fun _ : ι => (volume : Measure ℝ)) (f := g)
  rw [volume_pi, this, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hg0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply 0 one_ne_zero,
    ofReal_integral_eq_lintegral_ofReal (hgm i) (Filter.Eventually.of_forall (hg0 i))]
  rw [← lintegral_indicator (hs i)]
  refine lintegral_congr fun x => ?_
  simp only [hg]
  by_cases hx : x ∈ s i
  · simp [Set.indicator_of_mem hx, gaussianPDF]
  · simp [Set.indicator_of_notMem hx]


/-- The density of the product of standard normals. -/
lemma prod_gaussianPDFReal (x : ι → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i) =
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι * Real.exp (-(1 / 2) * ∑ i, x i ^ 2) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ]
  congr 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The standard Gaussian measure integrates against its density.** -/
lemma integral_stdGaussian (g : EuclideanSpace ℝ ι → ℝ) :
    ∫ y, g y ∂(stdGaussian (EuclideanSpace ℝ ι)) =
      ∫ y, (((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι *
        Real.exp (-(1 / 2) * ‖y‖ ^ 2)) * g y := by
  classical
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity]
  have hemb := (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  have h1 : (Measure.map (WithLp.toLp 2) ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))))) =
      Measure.map (MeasurableEquiv.toLp 2 (ι → ℝ)) _ := rfl
  rw [h1, hemb.integral_map,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 : ∀ y : ι → ℝ, (ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))).toReal •
      g ((MeasurableEquiv.toLp 2 (ι → ℝ)) y) =
      (fun z : EuclideanSpace ℝ ι => (((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι *
        Real.exp (-(1 / 2) * ‖z‖ ^ 2)) * g z) (MeasurableEquiv.toLp 2 (ι → ℝ) y) := by
    intro y
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
      prod_gaussianPDFReal, smul_eq_mul]
    simp [EuclideanSpace.norm_sq_eq]
  simp_rw [h2]
  exact (PiLp.volume_preserving_toLp ι).integral_comp hemb
    (fun z : EuclideanSpace ℝ ι => (((Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι *
        Real.exp (-(1 / 2) * ‖z‖ ^ 2)) * g z)

end Lightlike.FieldTheory
