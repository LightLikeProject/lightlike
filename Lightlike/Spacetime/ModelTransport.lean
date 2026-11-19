import Mathlib

/-!
# Derivatives with respect to a transported model (CO30)

If `I` is a model with corners on `E` and `e : E ≃L[ℝ] F`, the derivative of a map `f` with respect to the model `I.transContinuousLinearEquiv e`
(Mathlib: `ModelWithCorners.transContinuousLinearEquiv`, the same manifold modelled on `F`) is the derivative with respect to `I`
composed with `e⁻¹` (`hasMFDerivAt_transContinuousLinearEquiv`). Used to model the product manifold `J × S³` on `Fin 4 → ℝ`.

**Limits.** The derivative of a map out of the manifold only.
-/

open Manifold Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **A derivative with respect to the model `I.transContinuousLinearEquiv e`** is the derivative with respect to `I` composed with `e⁻¹`. -/
theorem hasMFDerivAt_transContinuousLinearEquiv (e : E ≃L[ℝ] F) {f : M → M'} {p : M}
    {f' : TangentSpace I p →L[ℝ] TangentSpace I' (f p)} (h : HasMFDerivAt I I' f p f') :
    HasMFDerivAt (I.transContinuousLinearEquiv e) I' f p
      (f'.comp (e.symm : F →L[ℝ] E) : TangentSpace (I.transContinuousLinearEquiv e) p →L[ℝ] TangentSpace I' (f p)) := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have hs : HasFDerivWithinAt (e.symm : F → E) (e.symm : F →L[ℝ] E) (range (I.transContinuousLinearEquiv e))
      ((extChartAt (I.transContinuousLinearEquiv e) p) p) := e.symm.hasFDerivAt.hasFDerivWithinAt
  have hmaps : MapsTo (e.symm : F → E) (range (I.transContinuousLinearEquiv e)) (range I) := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range]
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hpt : (e.symm : F → E) ((extChartAt (I.transContinuousLinearEquiv e) p) p) = extChartAt I p p := by
    simp [ModelWithCorners.coe_extChartAt_transContinuousLinearEquiv]
  rw [← hpt] at h2
  have := h2.comp _ hs hmaps
  refine this.congr_of_eventuallyEq ?_ ?_
  · exact Filter.Eventually.of_forall fun z => rfl
  · rfl
/-- **The derivative of a map into `M`, with respect to the transported model on the target**, is `e` composed with the derivative. -/
theorem hasMFDerivAt_transContinuousLinearEquiv_right (e : E ≃L[ℝ] F) {f : M' → M} {p : M'}
    {f' : TangentSpace I' p →L[ℝ] TangentSpace I (f p)} (h : HasMFDerivAt I' I f p f') :
    HasMFDerivAt I' (I.transContinuousLinearEquiv e) f p
      ((e : E →L[ℝ] F).comp f' : TangentSpace I' p →L[ℝ] TangentSpace (I.transContinuousLinearEquiv e) (f p)) := by
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have := (e.hasFDerivAt (x := writtenInExtChartAt I' I p f (extChartAt I' p p))).comp_hasFDerivWithinAt _ h2
  refine this.congr_of_eventuallyEq ?_ ?_
  · exact Filter.Eventually.of_forall fun z => rfl
  · rfl
end Lightlike
