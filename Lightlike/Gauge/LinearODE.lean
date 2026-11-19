import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Basic

/-!
# A linear ODE with continuous coefficients and zero initial value has only the zero solution

For `y : ℝ → (Fin m → ℝ)` with `y' = A(t) y` on `[0, T)`, `A` continuous on `[0, T]` and `y 0 = 0`, `y = 0` on `[0, T]`.
This is the step of the invariance of the constraint surface under the flow of a first-class constraint: the values
`y_b(t) = φ_b(γ(t))` of the constraints along an integral curve `γ` satisfy such a system when the brackets are
combinations of the constraints (involutivity), and start at zero on the surface.
-/

open Set Matrix

namespace Lightlike.Gauge

variable {m : ℕ}

/-- **Zero solution of a linear ODE**: the coordinate bound of the coefficients gives the Gronwall constant. -/
theorem eq_zero_of_linear_ode (y : ℝ → (Fin m → ℝ)) (A : ℝ → Matrix (Fin m) (Fin m) ℝ) {T : ℝ}
    (hA : ∀ i j, ContinuousOn (fun t => A t i j) (Icc 0 T))
    (hy : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (A t *ᵥ y t) (Ici t) t) (hyc : ContinuousOn y (Icc 0 T))
    (hy0 : y 0 = 0) : ∀ t ∈ Icc 0 T, y t = 0 := by
  have hcont : ContinuousOn (fun t => fun i j => A t i j) (Icc 0 T) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hA i j
  obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  have hM' : ∀ t ∈ Icc 0 T, ∀ i j, |A t i j| ≤ max M 0 := by
    intro t ht i j
    have h1 := (norm_le_pi_norm (fun j => A t i j) j).trans ((norm_le_pi_norm (fun i j => A t i j) i).trans (hM t ht))
    exact (by simpa using h1 : |A t i j| ≤ M).trans (le_max_left _ _)
  refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := (m : ℝ) * max M 0) hyc hy hy0 ?_
  intro t ht
  have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ j, A t i j * y t j| ≤ ∑ j, |A t i j * y t j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, max M 0 * ‖y t‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hM' t ht' i j) (by simpa using norm_le_pi_norm (y t) j) (abs_nonneg _) (le_max_right _ _)
    _ = (m : ℝ) * max M 0 * ‖y t‖ := by simp [mul_assoc]

end Lightlike.Gauge
