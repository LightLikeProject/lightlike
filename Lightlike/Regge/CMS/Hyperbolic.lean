import Mathlib
import Lightlike.GR.Schwarzschild
import Lightlike.Regge.Geodesic.Metric

/-!
# A curved example metric with explicit curvature: the hyperbolic plane `dx² + e^{2x} dy²`

The metric `g = diag(1, e^{2 y₀})` on `ℝ²` is the hyperbolic plane (curvature `-1`). This file
proves that it is a Riemannian metric on all of `ℝ²` and that its scalar curvature is the constant
`-2`, computed from the library's `christoffel`, `riemann`, `ricci` and `scalarCurvature`.
-/

open Matrix Real Lightlike Lightlike.Geodesic
open scoped ContDiff

namespace Lightlike.CMS

noncomputable section

/-- The diagonal entries `(1, e^{2 y₀})`. -/
def hypD (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![1, exp (2 * y 0)]

/-- The hyperbolic plane metric `dx² + e^{2x} dy²` in a chart of `ℝ²`. -/
def hypMetric : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun y => diagonal (hypD y)

/-- The expected Christoffel symbols: `Γ⁰₁₁ = -e^{2x}`, `Γ¹₀₁ = Γ¹₁₀ = 1`, others `0`. -/
def hypΓ (i j k : Fin 2) (y : Fin 2 → ℝ) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 1 then -exp (2 * y 0)
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then 1 else 0

lemma pd_hypD0 (k : Fin 2) (y : Fin 2 → ℝ) : pd k (fun y => hypD y 0) y = 0 := by
  simp [hypD, pd_const]

lemma pd_hypD1 (k : Fin 2) (y : Fin 2 → ℝ) :
    pd k (fun y => hypD y 1) y = if k = 0 then 2 * exp (2 * y 0) else 0 := by
  have hf : HasDerivAt (fun t : ℝ => exp (2 * t)) (2 * exp (2 * y 0)) (y 0) := by
    have := ((hasDerivAt_id (y 0)).const_mul 2).exp
    simpa [mul_comm] using this
  simpa [hypD] using pd_coord (n := 2) 0 k hf

lemma christoffel_hyp (y : Fin 2 → ℝ) (i j k : Fin 2) : christoffel hypMetric i j k y = hypΓ i j k y := by
  have hd : ∀ i, hypD y i ≠ 0 := by intro i; fin_cases i <;> simp [hypD, exp_ne_zero]
  change christoffel (fun y => diagonal (hypD y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hypΓ, pd_hypD0, pd_hypD1] <;> simp [hypD] <;> field_simp

lemma pd_hypΓ (m i j k : Fin 2) (x : Fin 2 → ℝ) :
    pd m (hypΓ i j k) x =
      if m = 0 ∧ i = 0 ∧ j = 1 ∧ k = 1 then -(2 * exp (2 * x 0)) else 0 := by
  have hf : HasDerivAt (fun t : ℝ => -exp (2 * t)) (-(2 * exp (2 * x 0))) (x 0) := by
    have := (((hasDerivAt_id (x 0)).const_mul 2).exp).neg
    convert this using 1
    · ext t; simp
    · simp [mul_comm]
  have hc := pd_coord (n := 2) 0 m hf
  rw [show hypΓ i j k = fun y => hypΓ i j k y from rfl]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [hypΓ, pd_const]
  simpa [eq_comm] using hc

theorem ricci_hyp (x : Fin 2 → ℝ) :
    ricci hypMetric 0 0 x = -1 ∧ ricci hypMetric 1 1 x = -exp (2 * x 0) ∧
      ricci hypMetric 0 1 x = 0 ∧ ricci hypMetric 1 0 x = 0 := by
  have hp : ∀ m i j k, pd m (christoffel hypMetric i j k) x = pd m (hypΓ i j k) x := by
    intro m i j k
    have : christoffel hypMetric i j k = hypΓ i j k := funext fun y => christoffel_hyp y i j k
    rw [this]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [ricci, riemann, Fin.sum_univ_two, hp, pd_hypΓ, christoffel_hyp, hypΓ]
    try ring

lemma inv_hyp (x : Fin 2 → ℝ) : (hypMetric x)⁻¹ = diagonal ![1, (exp (2 * x 0))⁻¹] := by
  rw [hypMetric, inv_diagonal_of_ne]
  · congr 1; ext i; fin_cases i <;> simp [hypD]
  · intro i; fin_cases i <;> simp [hypD, exp_ne_zero]

/-- **The scalar curvature of the hyperbolic plane metric is `-2`.** -/
theorem scalar_hyp (x : Fin 2 → ℝ) : scalarCurvature hypMetric x = -2 := by
  obtain ⟨h00, h11, h01, h10⟩ := ricci_hyp x
  simp only [scalarCurvature, Fin.sum_univ_two, inv_hyp, h00, h11, h01, h10]
  simp
  field_simp
  ring

/-- `hypMetric` is a Riemannian metric on the whole plane. -/
theorem isRiemMetric_hyp : IsRiemMetric hypMetric Set.univ where
  coord := by
    refine isCoordMetric_diagonal hypD isOpen_univ (fun i => ?_) (fun x _ i => ?_)
    · fin_cases i
      · exact contDiffOn_const
      · exact (by
          have : (fun y : Fin 2 → ℝ => hypD y 1) = fun y => exp (2 * y 0) := by ext y; simp [hypD]
          rw [this]; fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => hypD y 1).contDiffOn
    · fin_cases i <;> simp [hypD, exp_ne_zero]
  posDef := fun x _ => by
    rw [hypMetric, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> simp [hypD, exp_pos]

end

end Lightlike.CMS
