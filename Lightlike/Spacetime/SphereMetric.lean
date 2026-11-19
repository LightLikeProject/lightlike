import Mathlib
import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Lorentzian

/-!
# The round metric on the 3-sphere (CO30, attempt 1)

`roundMetric`: the metric of the unit sphere `S³ ⊆ ℝ⁴` as a smooth symmetric nondegenerate bilinear field (`NondegMetric`) on Mathlib's
manifold `sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`: the pullback of the Euclidean inner product by the inclusion
(`pullbackForm`, smooth by `contMDiff_pullbackForm`), nondegenerate because the derivative of the inclusion is injective
(`injective_mvfderiv_subtypeVal_sphere`).

**Limits.** The metric only; its coordinate expression in the stereographic charts and the product with a time interval are separate.
-/

open Manifold Metric Bundle
open scoped ContDiff RealInnerProductSpace

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

/-- The unit 3-sphere, Mathlib's manifold structure with model `𝓡 3`. -/
abbrev S3 : Type := sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (3 + 1))) = 3 + 1) := ⟨by simp⟩

/-- The inclusion of the unit 3-sphere into `ℝ⁴` as a map to a normed space. -/
def sphereIncl (p : S3) : EuclideanSpace ℝ (Fin (3 + 1)) := p

/-- The inclusion is smooth. -/
theorem contMDiff_sphereIncl : ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin (3 + 1))) ∞ sphereIncl :=
  contMDiff_coe_sphere

/-- **The round metric of the unit 3-sphere** as a smooth symmetric nondegenerate bilinear field. -/
def roundMetric : NondegMetric (𝓡 3) S3 where
  g := pullbackForm (I := 𝓡 3) (innerSL ℝ : EuclideanSpace ℝ (Fin (3 + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (3 + 1)) →L[ℝ] ℝ) sphereIncl
  symm x v w := pullbackForm_symm (fun a b => by rw [innerSL_apply_apply, innerSL_apply_apply]; exact real_inner_comm _ _) sphereIncl x v w
  nondegenerate x v h := by
    have h0 := h v
    rw [pullbackForm_apply] at h0
    have h2 : inner ℝ (dι (I := 𝓡 3) sphereIncl x v) (dι (I := 𝓡 3) sphereIncl x v) = 0 := h0
    have h1 : dι (I := 𝓡 3) sphereIncl x v = 0 := inner_self_eq_zero.1 h2
    exact (injective_mvfderiv_subtypeVal_sphere (E := EuclideanSpace ℝ (Fin (3 + 1))) x)
      (h1.trans (map_zero _).symm)
  contMDiff := contMDiff_pullbackForm _ contMDiff_sphereIncl

end Lightlike
