import Mathlib
import Lightlike.Spacetime.RoundSphereTwoChart
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.Corners.Coordinates

/-!
# The coordinate metric of the round 2-sphere in the stereographic charts

For the metric `roundMetric2I r hr` of the 2-sphere of radius `r` on Mathlib's manifold `S²` modelled on `Fin 2 → ℝ`
(`I2`, the transport of `𝓡 2`), in the chart of Mathlib's atlas at any point and on its whole target the coordinate
components are `r² · 16 / (|y|² + 4)²` times the identity (`coordMetric_round2`).
-/

open Manifold Metric Bundle TopologicalSpace Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

theorem range_I2 : range I2 = univ := by
  rw [ModelWithCorners.transContinuousLinearEquiv_range]
  simp

theorem target_sphere_chart2 (x : S2) : (extChartAt (𝓡 2) x).target = Set.univ := by
  simp [extChartAt]
  exact stereographic'_target (n := 2) (-x)

instance : I2.Boundaryless := ⟨range_I2⟩

/-- **Step A**: the derivative of the chart inverse for `I2`, read through `modelEquiv2`, is that of `𝓡 2`. -/
theorem mfderiv_I2_chart_symm (x : S2) {y : Fin 2 → ℝ} (hy : y ∈ (extChartAt I2 x).target) (v : Fin 2 → ℝ) :
    modelEquiv2.symm (mfderivWithin 𝓘(ℝ, Fin 2 → ℝ) I2 (extChartAt I2 x).symm (range I2) y v) =
      mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) (extChartAt (𝓡 2) x).symm (range (𝓡 2))
        (modelEquiv2.symm y) (modelEquiv2.symm v) := by
  have hz : modelEquiv2.symm y ∈ (extChartAt (𝓡 2) x).target := by
    have := hy
    simp only [I2, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  have hd : MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) (extChartAt (𝓡 2) x).symm (range (𝓡 2))
      (modelEquiv2.symm y) := mdifferentiableWithinAt_extChartAt_symm hz
  have hr : range (𝓡 2 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))) = univ :=
    ModelWithCorners.range_eq_univ _
  rw [hr] at hd ⊢
  rw [mdifferentiableWithinAt_univ] at hd
  have hD := hd.hasMFDerivAt
  have hE := (modelEquiv2.symm.hasFDerivAt (x := y)).hasMFDerivAt
  have hc := hD.comp y hE
  have h4 := hasMFDerivAt_transContinuousLinearEquiv_right modelEquiv2 hc
  rw [range_I2, mfderivWithin_univ]
  have hfun : (extChartAt I2 x).symm = (extChartAt (𝓡 2) x).symm ∘ ⇑modelEquiv2.symm := rfl
  rw [hfun, h4.mfderiv]
  simp
  rfl

/-- **Step B**: the derivative of the chart inverse of the sphere, through the inclusion, is the derivative of the inverse
stereographic map. -/
theorem chart_symm_deriv2 (x : S2) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ (extChartAt (𝓡 2) x).target)
    (v : EuclideanSpace ℝ (Fin 2)) :
    dcoe2 ((extChartAt (𝓡 2) x).symm z)
      (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) (extChartAt (𝓡 2) x).symm (range (𝓡 2)) z v) =
      fderiv ℝ (fun u => (((stereographic' 2 (-x)).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) z v := by
  have hd2 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 2) (extChartAt (𝓡 2) x).symm z := by
    have := mdifferentiableWithinAt_extChartAt_symm hz
    simpa [mdifferentiableWithinAt_univ] using this
  have hr : range (𝓡 2 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))) = univ :=
    ModelWithCorners.range_eq_univ _
  rw [hr, mfderivWithin_univ]
  have hstereo : ∀ u, (((extChartAt (𝓡 2) x).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1))) =
      (((stereographic' 2 (-x)).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1))) :=
    fun u => by simp [extChartAt]; rfl
  obtain ⟨Df, hDf, hDfa⟩ := hasFDerivAt_stereoMap (stereoW2 (-x)) ((-x : S2) : EuclideanSpace ℝ (Fin (2 + 1))) z
  have hf : (fun u => (((stereographic' 2 (-x)).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) =
      stereoMap (stereoW2 (-x)) ((-x : S2) : EuclideanSpace ℝ (Fin (2 + 1))) := by
    funext w; exact stereographic_symm_eq2 (-x) w
  have hc := (hasMFDerivAt_sphereIncl2 ((extChartAt (𝓡 2) x).symm z)).comp z hd2.hasMFDerivAt
  have hcf : (sphereIncl2 ∘ (extChartAt (𝓡 2) x).symm) =
      stereoMap (stereoW2 (-x)) ((-x : S2) : EuclideanSpace ℝ (Fin (2 + 1))) := by
    funext u; rw [← hf]; exact hstereo u
  rw [hcf] at hc
  have hu := hasMFDerivAt_unique hc
    (show HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1))) _ z Df from hDf.hasMFDerivAt)
  have hfd : fderiv ℝ (fun u => (((stereographic' 2 (-x)).symm u : S2) : EuclideanSpace ℝ (Fin (2 + 1)))) z = Df := by
    rw [hf]; exact hDf.fderiv
  rw [hfd]
  have := congrArg (fun L => L v) hu
  exact this

variable (r : ℝ) (hr : r ≠ 0)

/-- the chart inverse of the transported model is the chart inverse of `𝓡 2` composed with `modelEquiv2⁻¹` -/
theorem extChartAt_I2_symm (x : S2) (y : Fin 2 → ℝ) :
    (extChartAt I2 x).symm y = (extChartAt (𝓡 2) x).symm (modelEquiv2.symm y) := rfl

/-- **The coordinate components of the round metric in the chart**, as the evaluation of the form on `e⁻¹ e_i`. -/
theorem coordMetric_round2_aux (x : S2) {y : Fin 2 → ℝ} (hy : y ∈ (extChartAt I2 x).target) (v w : Fin 2 → ℝ) :
    (roundMetric2I r hr).g ((extChartAt I2 x).symm y)
      (mfderivWithin 𝓘(ℝ, Fin 2 → ℝ) I2 (extChartAt I2 x).symm (range I2) y v)
      (mfderivWithin 𝓘(ℝ, Fin 2 → ℝ) I2 (extChartAt I2 x).symm (range I2) y w) =
      r ^ 2 * (16 * ((‖modelEquiv2.symm y‖ ^ 2 + 4)⁻¹) ^ 2 * inner ℝ (modelEquiv2.symm v) (modelEquiv2.symm w)) := by
  have hz : modelEquiv2.symm y ∈ (extChartAt (𝓡 2) x).target := by
    have := hy
    simp only [I2, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  show pullbackForm (I := I2) (radiusForm r) sphereIncl2 ((extChartAt I2 x).symm y) _ _ = _
  rw [pullbackForm_apply, radiusForm_apply, dι_I2, dι_I2]
  erw [mfderiv_I2_chart_symm x hy v, mfderiv_I2_chart_symm x hy w]
  have hp : ((extChartAt I2 x).symm y) = (extChartAt (𝓡 2) x).symm (modelEquiv2.symm y) := rfl
  rw [hp, chart_symm_deriv2 x hz, chart_symm_deriv2 x hz, inner_fderiv_chartInv2]

/-- **The coordinate metric of the round 2-sphere of radius `r`** in the chart of Mathlib's atlas at any point, on the whole
chart target: `r² · 16 / (|y|² + 4)²` times the identity matrix. -/
theorem coordMetric_round2 (x : S2) {y : Fin 2 → ℝ} (hy : y ∈ (extChartAt I2 x).target) :
    (roundMetric2I r hr).coordMetricW x y =
      (r ^ 2 * (16 * ((∑ i, y i ^ 2 + 4)⁻¹) ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  funext i j
  unfold NondegMetric.coordMetricW
  rw [coordMetric_round2_aux r hr x hy]
  have hn : ‖modelEquiv2.symm y‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [modelEquiv2, EuclideanSpace.equiv]
  rw [hn]
  have hin : inner ℝ (modelEquiv2.symm (Pi.single i 1 : Fin 2 → ℝ)) (modelEquiv2.symm (Pi.single j 1 : Fin 2 → ℝ)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    have e : ∀ k : Fin 2, modelEquiv2.symm (Pi.single k 1 : Fin 2 → ℝ) = EuclideanSpace.single k (1 : ℝ) := fun k => by
      ext l; simp [modelEquiv2, EuclideanSpace.equiv, Pi.single_apply]
    rw [e, e, EuclideanSpace.inner_single_left]
    simp [Matrix.one_apply, Pi.single_apply]
  rw [hin]
  simp [Matrix.smul_apply]
  ring

end Lightlike
