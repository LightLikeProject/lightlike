import Lightlike.Regge.Linear3.LinearizedLimit

/-!
# Trust check for the convergence of `Q_n`

`Qn_converges` is not vacuous: its hypotheses (smooth, symmetric, invariant under integer translations) hold for the
non-zero field `cosField` with `h₀₁ = h₁₀ = cos (2π x₂)` (`cosField_Qn`). The numerical check
`scripts/regge/regge3d_linearized_check.py` computes `Q_n` for a random smooth periodic field on the complex with
the interpolated lengths and compares it with the `η²` coefficient of `∫ (R/2) √det g` (equal to the Fierz–Pauli
form), with sign and factor controls.
-/

open Real Filter Topology
namespace Lightlike.Regge.Linear3
open Lightlike.Regge.Conv3

/-- A periodic smooth symmetric perturbation with only the off-diagonal entries `h₀₁ = h₁₀ = cos (2π x₂)`. -/
noncomputable def cosField : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => Matrix.of fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then Real.cos (2 * π * x 2) else 0

theorem cosField_smooth (i j : Fin 3) : ContDiff ℝ 3 (fun y => cosField y i j) := by
  unfold cosField
  by_cases h : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
  · simp only [Matrix.of_apply, h, ite_true]; fun_prop
  · simp only [Matrix.of_apply, h, ite_false]; exact contDiff_const

theorem cosField_symm (y : Fin 3 → ℝ) (i j : Fin 3) : cosField y i j = cosField y j i := by
  unfold cosField
  simp only [Matrix.of_apply]
  congr 1
  apply propext
  tauto

theorem cosField_periodic (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    cosField (p + fun i => (e i : ℝ)) = cosField p := by
  unfold cosField
  funext i j
  simp only [Matrix.of_apply]
  have : 2 * π * (p 2 + (e 2 : ℝ)) = 2 * π * p 2 + (e 2 : ℤ) * (2 * π) := by ring
  simp [Pi.add_apply, this, Real.cos_add_int_mul_two_pi]

/-- **Non-vacuity of the convergence of `Q_n`** for a non-zero periodic perturbation. -/
theorem cosField_Qn (δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N] (hN : 3 ≤ N), N0 ≤ N →
      |Qn N (by omega) cosField - ∫ y in unitCube, -(1 / 4) * svPair (Hm cosField y) (dd2 cosField y)| < δ :=
  Qn_converges cosField_smooth cosField_symm cosField_periodic δ hδ

end Lightlike.Regge.Linear3
