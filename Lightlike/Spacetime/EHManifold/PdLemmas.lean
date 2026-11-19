import Lightlike.Spacetime.Curvature

/-!
# Rules for the partial derivative `pd` of differences, finite sums and products

Supporting lemmas; no catalogue entry.
-/

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The partial derivative of a difference of differentiable functions. -/
lemma pd_fun_sub {u v : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (μ : Fin n) :
    pd μ (fun y => u y - v y) x = pd μ u x - pd μ v x := by
  unfold pd
  have h := (hu.hasFDerivAt.fun_sub hv.hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.sub_apply]

/-- The partial derivative of a finite sum of differentiable functions. -/
lemma pd_fun_sum {ι : Type*} (t : Finset ι) (F : ι → (Fin n → ℝ) → ℝ) {x : Fin n → ℝ}
    (hF : ∀ i ∈ t, DifferentiableAt ℝ (F i) x) (μ : Fin n) :
    pd μ (fun y => ∑ i ∈ t, F i y) x = ∑ i ∈ t, pd μ (F i) x := by
  unfold pd
  have h := (HasFDerivAt.fun_sum fun i hi => (hF i hi).hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.sum_apply]

/-- The partial derivative of a product of differentiable functions. -/
lemma pd_fun_mul {u v : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (μ : Fin n) :
    pd μ (fun y => u y * v y) x = pd μ u x * v x + u x * pd μ v x := by
  unfold pd
  have h := (hu.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  show (fderiv ℝ (u * v) x) (Pi.single μ 1) = _
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end Lightlike
