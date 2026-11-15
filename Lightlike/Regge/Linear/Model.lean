import Mathlib
import Lightlike.Regge.Linear.Deficit

/-!
# The linearized deficit of a quadratic perturbation

For a perturbation whose entries are polynomials of degree at most two about the vertex `P`
(given by their 2-jets), the linearized deficit angle at `P` is exactly `s² ·` the linearized
curvature `∂₀∂₁ h₀₁ - ½ (∂₁² h₀₀ + ∂₀² h₁₁)`, for every `s > 0`: the lower-order terms cancel
by the symmetry of the star.
-/

open Real MeasureTheory Lightlike.Geodesic

namespace Lightlike.Regge.Linear

noncomputable section

/-- The 2-jet of a real function at a point: value, gradient, and the Hessian entries
`∂₀₀, ∂₀₁, ∂₁₁`. -/
structure Jet where
  /-- value -/
  v : ℝ
  /-- `∂₀` -/
  g0 : ℝ
  /-- `∂₁` -/
  g1 : ℝ
  /-- `∂₀₀` -/
  a : ℝ
  /-- `∂₀₁` -/
  b : ℝ
  /-- `∂₁₁` -/
  c : ℝ

/-- The quadratic Taylor polynomial of a jet, at the displacement `y`. -/
def Jet.eval (J : Jet) (y : Fin 2 → ℝ) : ℝ :=
  J.v + J.g0 * y 0 + J.g1 * y 1 + (J.a * y 0 ^ 2 + 2 * J.b * y 0 * y 1 + J.c * y 1 ^ 2) / 2

/-- The symmetric matrix field with the given jets at `P` for `h₀₀, h₀₁, h₁₁`. -/
def modelField (J00 J01 J11 : Jet) (P : Fin 2 → ℝ) :
    (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  fun x => !![J00.eval (x - P), J01.eval (x - P); J01.eval (x - P), J11.eval (x - P)]

/-- The linearized scalar curvature (half of it) of the jets:
`∂₀∂₁ h₀₁ - ½ (∂₁² h₀₀ + ∂₀² h₁₁)`. -/
def curv (J00 J01 J11 : Jet) : ℝ := J01.b - (J00.c + J11.a) / 2

/-- **Simpson's rule** is exact for quadratics on `[0, 1]`. -/
lemma integral_quad {g : ℝ → ℝ}
    (hg : ∀ t, g t = g 0 + (-3 * g 0 + 4 * g (1 / 2) - g 1) * t +
      (2 * g 0 - 4 * g (1 / 2) + 2 * g 1) * t ^ 2) :
    ∫ t in (0 : ℝ)..1, g t = (g 0 + 4 * g (1 / 2) + g 1) / 6 := by
  have : (fun t => g t) = fun t => (g 0 + (-3 * g 0 + 4 * g (1 / 2) - g 1) * t) +
      (2 * g 0 - 4 * g (1 / 2) + 2 * g 1) * t ^ 2 := by
    funext t; rw [hg t]
  rw [this, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · simp; ring
  all_goals first
    | exact intervalIntegrable_const
    | exact (by fun_prop : Continuous fun t : ℝ => _).intervalIntegrable _ _

/-- The edge variation of the model field is Simpson's rule on the integrand. -/
lemma edgeVar_model (J00 J01 J11 : Jet) (P : Fin 2 → ℝ) (s : ℝ) (p q : Fin 2 → ℝ) :
    edgeVar (modelField J00 J01 J11 P) s P p q =
      (normSq (modelField J00 J01 J11 P) (P + s • p) (q - p) +
        4 * normSq (modelField J00 J01 J11 P) (P + s • (p + (1 / 2 : ℝ) • (q - p))) (q - p) +
        normSq (modelField J00 J01 J11 P) (P + s • (p + (1 : ℝ) • (q - p))) (q - p)) / 6 := by
  unfold edgeVar
  have := integral_quad (g := fun t : ℝ =>
    normSq (modelField J00 J01 J11 P) (P + s • (p + t • (q - p))) (q - p)) (by
      intro t
      simp only [normSq, modelField, Jet.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, add_sub_cancel_left, zero_smul, add_zero, one_smul]
      ring)
  simpa using this

/-- **Exactness on quadratics.** For a field with quadratic entries about `P`, the linearized
deficit at `P` is exactly `s²` times the linearized curvature. -/
theorem linDef_model (J00 J01 J11 : Jet) (P : Fin 2 → ℝ) (s : ℝ) :
    linDef (modelField J00 J01 J11 P) s P = s ^ 2 * curv J00 J01 J11 := by
  simp only [linDef, varA, varB, varC, edgeVar_model, Fin.sum_univ_six, sqA, sqB, sqC, off]
  simp [normSq, modelField, Jet.eval, Matrix.mulVec, dotProduct, Fin.sum_univ_two, curv,
    Matrix.vecHead, Matrix.vecTail]
  ring

end

end Lightlike.Regge.Linear
