import Mathlib
import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Lorentzian
import Lightlike.Spacetime.ModelTransport

/-!
# The round metric on the 2-sphere

`S2` is the unit 2-sphere of `ℝ³` with Mathlib's manifold structure (model `𝓡 2`), and `roundMetric2I r hr` the metric
`r² h` of the round sphere of radius `r` (`h` the pullback of the Euclidean inner product by the inclusion), as a
smooth symmetric nondegenerate bilinear field (`NondegMetric`) of the manifold modelled on `Fin 2 → ℝ` (`I2`, the
transport of Mathlib's model `𝓡 2`). It is the same construction as `roundMetric` for the 3-sphere (`SphereMetric.lean`),
with the factor `r²` for the radius.

**Differences from the cited statement**: the radius `r` enters as the factor `r²` of the metric on the unit sphere
(the sphere of radius `r` is isometric to it), and `r ≠ 0` is the only condition (`r` and `-r` give the same metric).
-/

open Manifold Metric Bundle
open scoped ContDiff RealInnerProductSpace

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

/-- The unit 2-sphere, Mathlib's manifold structure with model `𝓡 2`. -/
abbrev S2 : Type := sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1

instance fact_finrank_E3 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) := ⟨by simp⟩

/-- The inclusion of the unit 2-sphere into `ℝ³`. -/
def sphereIncl2 (p : S2) : EuclideanSpace ℝ (Fin (2 + 1)) := p

theorem contMDiff_sphereIncl2 : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1))) ∞ sphereIncl2 :=
  contMDiff_coe_sphere

variable (r : ℝ) (hr : r ≠ 0)

/-- The form `r² ⟪·, ·⟫` of `ℝ³`. -/
def radiusForm : EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] ℝ :=
  (r ^ 2) • (innerSL ℝ : EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) →L[ℝ] ℝ)

theorem radiusForm_apply (a b : EuclideanSpace ℝ (Fin (2 + 1))) : radiusForm r a b = r ^ 2 * inner ℝ a b := by
  simp only [radiusForm, smul_apply, smul_eq_mul]
  rfl

/-- the identification of the model `ℝ²` (Euclidean) with `Fin 2 → ℝ` -/
def modelEquiv2 : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ

/-- the model with corners of `S²` on `Fin 2 → ℝ` -/
abbrev I2 : ModelWithCorners ℝ (Fin 2 → ℝ) (EuclideanSpace ℝ (Fin 2)) :=
  (𝓡 2).transContinuousLinearEquiv modelEquiv2

example : IsManifold I2 ∞ S2 := inferInstance

/-- The derivative of the inclusion as a plain continuous linear map. -/
def dcoe2 (x : S2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) :=
  mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1))) sphereIncl2 x

theorem hasMFDerivAt_sphereIncl2 (x : S2) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 + 1))) sphereIncl2 x (dcoe2 x) :=
  (contMDiff_sphereIncl2.mdifferentiableAt (by simp)).hasMFDerivAt

/-- The derivative of the inclusion with respect to the transported model. -/
theorem dι_I2 (x : S2) (v : TangentSpace I2 x) :
    dι (I := I2) sphereIncl2 x v = dcoe2 x (modelEquiv2.symm v) := by
  have h := hasMFDerivAt_transContinuousLinearEquiv modelEquiv2 (hasMFDerivAt_sphereIncl2 x)
  unfold dι
  rw [h.mfderiv]
  rfl

/-- **The round metric of the 2-sphere of radius `r` as a metric of the manifold modelled on `Fin 2 → ℝ`.** -/
def roundMetric2I : NondegMetric I2 S2 where
  g := pullbackForm (I := I2) (radiusForm r) sphereIncl2
  symm x v w := pullbackForm_symm (fun a b => by rw [radiusForm_apply, radiusForm_apply, real_inner_comm]) sphereIncl2 x v w
  nondegenerate x v h := by
    have h0 := h v
    rw [pullbackForm_apply, radiusForm_apply] at h0
    have h2 : r ^ 2 * inner ℝ (dι (I := I2) sphereIncl2 x v) (dι (I := I2) sphereIncl2 x v) = 0 := h0
    have h1 : dι (I := I2) sphereIncl2 x v = 0 :=
      inner_self_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (pow_ne_zero 2 hr))
    rw [dι_I2] at h1
    have h3 : modelEquiv2.symm v = 0 :=
      (injective_mvfderiv_subtypeVal_sphere (E := EuclideanSpace ℝ (Fin (2 + 1))) x)
        (h1.trans (map_zero _).symm)
    exact modelEquiv2.symm.injective (h3.trans (map_zero _).symm)
  contMDiff := contMDiff_pullbackForm _
    ((ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left (e := modelEquiv2)).2 contMDiff_sphereIncl2)

end Lightlike
