import Lightlike.Spacetime.Curvature

/-!
# Kaluza-Klein on a circle: fields independent of the fifth coordinate (row G1-044)

The 5D (more generally `(n+1)`-dimensional) coordinate space is `Fin (n + 1) → ℝ`, the fifth coordinate being
`Fin.last n`. A field of the `n`-dimensional base `Fin n → ℝ` is lifted to a field independent of the fifth
coordinate by composing with the projection `proj` that forgets it. This file has the lift of scalar
functions, the Kaluza-Klein metric matrix at a point, and the partial derivatives of lifted functions.

Source: overduin-wesson-1997, Section 2 (the ansatz `ds² = g_{μν} dxᵘ dxᵛ + φ² (dy + A_μ dxᵘ)²`).
-/

open Matrix

noncomputable section

namespace Lightlike
namespace KK

variable {n : ℕ}

/-- The projection `ℝ^{n+1} → ℝⁿ` that forgets the last coordinate. -/
def proj (x : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => x i.castSucc

/-- The projection `proj` as a continuous linear map. -/
def projL : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.castSucc

lemma projL_apply (x : Fin (n + 1) → ℝ) : projL x = proj x := rfl

/-- A function on the base lifted to a function independent of the fifth coordinate. -/
def lift (f : (Fin n → ℝ) → ℝ) : (Fin (n + 1) → ℝ) → ℝ := fun x => f (proj x)

lemma lift_eq_comp (f : (Fin n → ℝ) → ℝ) : lift f = f ∘ projL := rfl

lemma differentiableAt_lift {f : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}
    (hf : DifferentiableAt ℝ f (proj x)) : DifferentiableAt ℝ (lift f) x :=
  hf.comp x projL.differentiableAt

lemma projL_single_castSucc (k : Fin n) :
    projL (Pi.single k.castSucc (1 : ℝ) : Fin (n + 1) → ℝ) = Pi.single k 1 := by
  ext j
  show (Pi.single k.castSucc (1 : ℝ) : Fin (n + 1) → ℝ) j.castSucc = _
  simp [Pi.single_apply]

lemma projL_single_last : projL (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ) = 0 := by
  ext j
  show (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ) j.castSucc = _
  simp

lemma fderiv_lift {f : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}
    (hf : DifferentiableAt ℝ f (proj x)) :
    fderiv ℝ (lift f) x = (fderiv ℝ f (proj x)).comp projL := by
  have hf' : DifferentiableAt ℝ f (projL x) := hf
  rw [lift_eq_comp, fderiv_comp x hf' projL.differentiableAt, projL.fderiv]
  rfl

/-- The partial derivative of a lifted function along a base coordinate is the lift of the derivative. -/
lemma pd_castSucc_lift {f : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}
    (hf : DifferentiableAt ℝ f (proj x)) (k : Fin n) :
    pd k.castSucc (lift f) x = pd k f (proj x) := by
  unfold pd
  rw [fderiv_lift hf]
  simp only [ContinuousLinearMap.comp_apply, projL_single_castSucc]

/-- A lifted function does not depend on the fifth coordinate. -/
lemma pd_last_lift {f : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}
    (hf : DifferentiableAt ℝ f (proj x)) :
    pd (Fin.last n) (lift f) x = 0 := by
  unfold pd
  rw [fderiv_lift hf]
  simp only [ContinuousLinearMap.comp_apply, projL_single_last, map_zero]

end KK
end Lightlike
