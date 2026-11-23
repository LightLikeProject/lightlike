import Lightlike.Rows.G1_044.KKMetric

/-!
# Partial derivatives of functions pulled back along the projection `ℝⁿ⁺¹ → ℝⁿ` (G1-044)

For a function `f` on `ℝⁿ`, the function `f ∘ proj` on `ℝⁿ⁺¹` does not depend on the last coordinate:
`∂_{a} (f ∘ proj) = (∂_a f) ∘ proj` for `a < n` (`pd_comp_proj`) and `∂_n (f ∘ proj) = 0` (`pd_last_comp_proj`).

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ}

/-- The projection `proj` as a continuous linear map. -/
def projL (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.castSucc

theorem projL_apply (z : Fin (n + 1) → ℝ) : projL n z = proj z := rfl

theorem projL_single_castSucc (k : Fin n) : projL n (Pi.single k.castSucc (1 : ℝ)) = Pi.single k 1 := by
  funext i
  simp [projL_apply, proj, Pi.single_apply, Fin.castSucc_inj]

theorem projL_single_last : projL n (Pi.single (Fin.last n) (1 : ℝ)) = 0 := by
  funext i
  simp [projL_apply, proj, (Fin.castSucc_lt_last i).ne]

theorem hasFDerivAt_proj (x : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun z : Fin (n + 1) → ℝ => proj z) (projL n) x := (projL n).hasFDerivAt

/-- **Chain rule for the projection**: `∂_a (f ∘ proj) = (∂_a f) ∘ proj` for `a < n`. -/
theorem pd_comp_proj (f : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) (hf : DifferentiableAt ℝ f (proj x))
    (k : Fin n) : pd k.castSucc (fun z => f (proj z)) x = pd k f (proj x) := by
  have hc := (hf.hasFDerivAt.comp x (hasFDerivAt_proj x)).fderiv
  unfold pd
  rw [show (fun z => f (proj z)) = f ∘ proj from rfl, hc, ContinuousLinearMap.comp_apply,
    projL_single_castSucc]

/-- A function pulled back along the projection does not depend on the last coordinate. -/
theorem pd_last_comp_proj (f : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) (hf : DifferentiableAt ℝ f (proj x)) :
    pd (Fin.last n) (fun z => f (proj z)) x = 0 := by
  have hc := (hf.hasFDerivAt.comp x (hasFDerivAt_proj x)).fderiv
  unfold pd
  rw [show (fun z => f (proj z)) = f ∘ proj from rfl, hc, ContinuousLinearMap.comp_apply,
    projL_single_last, map_zero]

/-- The pulled-back function is differentiable. -/
theorem differentiableAt_comp_proj (f : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ)
    (hf : DifferentiableAt ℝ f (proj x)) : DifferentiableAt ℝ (fun z => f (proj z)) x :=
  (hf.hasFDerivAt.comp x (hasFDerivAt_proj x)).differentiableAt

/-- Derivative of a square: `∂_k (f²) = 2 f ∂_k f`. -/
theorem pd_sq (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) (hf : DifferentiableAt ℝ f p) (k : Fin n) :
    pd k (fun y => f y ^ 2) p = 2 * f p * pd k f p := by
  have h := pd_mul hf hf k
  simp only [pow_two]
  rw [h]
  ring

end KK

end Lightlike
