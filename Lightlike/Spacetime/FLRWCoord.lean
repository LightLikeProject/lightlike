import Lightlike.Spacetime.FLRWChart
import Lightlike.Cosmology.FLRW
import Lightlike.Spacetime.Corners.Curvature

/-!
# The coordinate metric of the FLRW metric on `J × S³` is the coordinate FLRW metric (CO30, attempt 1)

`coordMetric_flrw`: for the Lorentzian metric `flrwMetric4` on `↥J × S³` (model `Fin 4 → ℝ`), in the chart of Mathlib's atlas at any point and on its whole
target, the coordinate components are `Cosmology.flrwMetric a 1`, the diagonal matrix `-1, a²/(1+|x|²/4)², …` of the FLRW metric with `k = 1`
(`Lightlike/Cosmology/FLRW.lean`). The ingredients are the conformal factor of the stereographic chart (`StereoConformal.lean`), the derivatives of the charts
(`FLRWChart.lean`) and the form of the metric (`FLRWModel.lean`).

**Limits.** The coordinate metric only; the Einstein equations on `J × S³` are the next step.
-/

open Manifold Metric Bundle TopologicalSpace Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

theorem modelEquiv_symm_apply (y : Fin 4 → ℝ) :
    modelEquiv.symm y = (y 0, (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun k => y k.succ)) := by
  rfl

theorem modelEquiv_symm_single0 : modelEquiv.symm (Pi.single 0 1 : Fin 4 → ℝ) = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) := by
  rw [modelEquiv_symm_apply]
  ext <;> simp [Pi.single_apply, Fin.succ_ne_zero]

theorem modelEquiv_symm_single_succ (k : Fin 3) :
    modelEquiv.symm (Pi.single k.succ 1 : Fin 4 → ℝ) = ((0 : ℝ), (EuclideanSpace.single k (1 : ℝ))) := by
  rw [modelEquiv_symm_apply]
  ext j <;> simp [Pi.single_apply, Fin.succ_inj, Fin.succ_ne_zero]


/-- the time coordinate of the point of the chart inverse -/
theorem val_chart_symm (J : Opens ℝ) (x : ↥J × S3) {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) :
    (((extChartAt I4 x).symm y).1 : ℝ) = y 0 := by
  have hz : modelEquiv.symm y ∈ (extChartAt IJS x).target := by
    have := hy
    simp only [I4, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  have hz' : modelEquiv.symm y ∈ (extChartAt 𝓘(ℝ, ℝ) x.1).target ×ˢ (extChartAt (𝓡 3) x.2).target := by
    rw [extChartAt_IJS] at hz
    simpa using hz
  have h1 : ((extChartAt I4 x).symm y).1 = (extChartAt 𝓘(ℝ, ℝ) x.1).symm (modelEquiv.symm y).1 := by
    rw [extChartAt_I4_symm, extChartAt_IJS_symm]
  rw [h1]
  have h2 := OpenPartialHomeomorph.subtypeRestr_symm_apply (OpenPartialHomeomorph.refl ℝ) ⟨x.1⟩ (U := J)
    (y := (modelEquiv.symm y).1)
  have hh := hz'.1
  simp [extChartAt, Opens.chartAt_eq] at hh ⊢
  have := h2 hh
  simpa [modelEquiv_symm_apply] using this

/-- **The coordinate components of the FLRW metric in the chart**, as the evaluation of the form on `e⁻¹ e_i`. -/
theorem coordMetric_flrw_aux (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) (x : ↥J × S3)
    {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) (v w : Fin 4 → ℝ) :
    (flrwMetric4 J ha hpos).toNondegMetric.g ((extChartAt I4 x).symm y)
      (mfderivWithin 𝓘(ℝ, Fin 4 → ℝ) I4 (extChartAt I4 x).symm (range I4) y v)
      (mfderivWithin 𝓘(ℝ, Fin 4 → ℝ) I4 (extChartAt I4 x).symm (range I4) y w) =
      -((modelEquiv.symm v).1 * (modelEquiv.symm w).1) +
        a (y 0) ^ 2 * (16 * ((‖(modelEquiv.symm y).2‖ ^ 2 + 4)⁻¹) ^ 2 *
          inner ℝ (modelEquiv.symm v).2 (modelEquiv.symm w).2) := by
  have hz : modelEquiv.symm y ∈ (extChartAt IJS x).target := by
    have := hy
    simp only [I4, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  have hd : DifferentiableAt ℝ a (((extChartAt I4 x).symm y).1 : ℝ) :=
    ((ha.contDiffAt (J.isOpen.mem_nhds ((extChartAt I4 x).symm y).1.2)).differentiableAt (by simp))
  show flrwForm4 a ((extChartAt I4 x).symm y) _ _ = _
  rw [flrwForm4_eq _ hd]
  refine (flrwForm_apply _ hd _ _).trans ?_
  erw [mfderiv_I4_chart_symm J x hy v, mfderiv_I4_chart_symm J x hy w]
  obtain ⟨hv1, hv2⟩ := chart_symm_deriv J x hz (modelEquiv.symm v)
  obtain ⟨hw1, hw2⟩ := chart_symm_deriv J x hz (modelEquiv.symm w)
  have hp : ((extChartAt I4 x).symm y) = (extChartAt IJS x).symm (modelEquiv.symm y) := rfl
  rw [val_chart_symm J x hy, hp, hv1, hw1, hv2, hw2, inner_fderiv_chartInv]


theorem norm_sq_modelEquiv_symm (y : Fin 4 → ℝ) : ‖(modelEquiv.symm y).2‖ ^ 2 = Cosmology.spatialNormSq y := by
  rw [modelEquiv_symm_apply, EuclideanSpace.norm_sq_eq]
  simp [Cosmology.spatialNormSq]

/-- **The coordinate metric of the FLRW metric on `J × S³` in the chart of Mathlib's atlas is the coordinate FLRW metric with `k = 1`** on the whole
chart target. -/
theorem coordMetric_flrw (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) (x : ↥J × S3)
    {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) :
    (flrwMetric4 J ha hpos).toNondegMetric.coordMetricW x y = Cosmology.flrwMetric a 1 y := by
  funext i j
  unfold NondegMetric.coordMetricW
  rw [coordMetric_flrw_aux J ha hpos x hy, norm_sq_modelEquiv_symm]
  have hq : (Cosmology.spatialNormSq y + 4) ≠ 0 := by
    have : 0 ≤ Cosmology.spatialNormSq y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have e16 : 16 * ((Cosmology.spatialNormSq y + 4)⁻¹) ^ 2 = (1 / (1 + 1 * Cosmology.spatialNormSq y / 4)) ^ 2 := by
    rw [show (1 + 1 * Cosmology.spatialNormSq y / 4) = (Cosmology.spatialNormSq y + 4) / 4 by ring, one_div, inv_div,
      div_pow, inv_pow]
    field_simp
    ring
  have h0 : ∀ l : Fin 3, (0 : Fin 4) ≠ l.succ := fun l => (Fin.succ_ne_zero l).symm
  rw [e16]
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · rw [modelEquiv_symm_single0]
    simp [Cosmology.flrwMetric]
  · rw [modelEquiv_symm_single0, modelEquiv_symm_single_succ]
    simp [Cosmology.flrwMetric, Matrix.diagonal_apply, Fin.succ_ne_zero, h0]
  · rw [modelEquiv_symm_single0, modelEquiv_symm_single_succ]
    simp [Cosmology.flrwMetric, Matrix.diagonal_apply, Fin.succ_ne_zero, h0]
  · rw [modelEquiv_symm_single_succ, modelEquiv_symm_single_succ]
    simp [Cosmology.flrwMetric, Matrix.diagonal_apply, Fin.succ_ne_zero, h0, Fin.succ_inj, div_pow]
    have hin : inner ℝ (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)) = if k = l then (1 : ℝ) else 0 := by
      simp [EuclideanSpace.inner_single_left, Pi.single_apply, eq_comm]
    rw [hin]
    split_ifs
    · field_simp
    · simp

end Lightlike
