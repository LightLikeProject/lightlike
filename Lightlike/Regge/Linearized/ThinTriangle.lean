import Mathlib
import Lightlike.Regge.Linear.AngleDeriv

/-!
# Linearization is not uniform over non-fat triangles

Linearized Regge calculus differentiates the triangle angles with respect to the squared edge
lengths (`Lightlike.Regge.Linear.hasDerivAt_triAngle`). The derivative carries the factor `1/√D`,
with `√D = 4 ·` area. For a family of triangles that degenerates (area → 0 at fixed edge lengths),
the factor is unbounded, so no constant in a convergence estimate can hold uniformly over a
non-fat family of triangulations. Christiansen's convergence theorem assumes fat (shape-regular)
triangulations for exactly this reason.

This file proves the unboundedness for the isosceles family with two unit sides.
It is a statement about the angle sensitivity only; it does not claim that a
particular non-fat sequence of triangulations fails to converge.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- **Thin triangles have unbounded angle sensitivity.** For every bound `M`, there is a
nondegenerate triangle with squared sides `1, 1, c` whose apex angle has derivative `d > M` with
respect to a perturbation of the squared base length `c`. -/
theorem thin_triangle_sensitivity_unbounded (M : ℝ) :
    ∃ c d : ℝ, 0 < c ∧ c < 4 ∧
      HasDerivAt (fun ε : ℝ => triAngle (1 + ε * 0) (1 + ε * 0) (c + ε * 1)) d 0 ∧ M < d := by
  set δ : ℝ := 1 / (4 * (M ^ 2 + 1)) with hδ
  have hM : 0 < M ^ 2 + 1 := by positivity
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg M]
  have hD : disc 1 1 (4 - δ) = 4 * δ - δ ^ 2 := by unfold disc; ring
  have hDpos : 0 < disc 1 1 (4 - δ) := by rw [hD]; nlinarith
  have hder := hasDerivAt_triAngle (a := 1) (b := 1) (c := 4 - δ) (a₁ := 0) (b₁ := 0) (c₁ := 1)
    one_pos one_pos hDpos
  refine ⟨4 - δ, _, by linarith, by linarith, hder, ?_⟩
  -- the derivative is 1 / √D with D < 4 δ = 1 / (M² + 1)
  have hsq : 0 < √(disc 1 1 (4 - δ)) := Real.sqrt_pos.mpr hDpos
  have hlt : disc 1 1 (4 - δ) < 1 / (M ^ 2 + 1) := by
    rw [hD]
    have : 4 * δ = 1 / (M ^ 2 + 1) := by rw [hδ]; field_simp
    nlinarith
  have hroot : √(disc 1 1 (4 - δ)) < 1 / √(M ^ 2 + 1) := by
    calc √(disc 1 1 (4 - δ)) < √(1 / (M ^ 2 + 1)) := Real.sqrt_lt_sqrt hDpos.le hlt
      _ = 1 / √(M ^ 2 + 1) := by rw [Real.sqrt_div' _ hM.le, Real.sqrt_one]
  have hval : (2 * 1 - (1 - 1 + (4 - δ)) * 0 / 1 - (1 - 1 + (4 - δ)) * 0 / 1) /
      (2 * √(disc 1 1 (4 - δ))) = 1 / √(disc 1 1 (4 - δ)) := by
    field_simp; ring
  rw [hval]
  have hS : 0 < √(M ^ 2 + 1) := Real.sqrt_pos.mpr hM
  have h1 : √(M ^ 2 + 1) < 1 / √(disc 1 1 (4 - δ)) := by
    rw [lt_div_iff₀ hsq]
    calc √(M ^ 2 + 1) * √(disc 1 1 (4 - δ)) < √(M ^ 2 + 1) * (1 / √(M ^ 2 + 1)) :=
          mul_lt_mul_of_pos_left hroot hS
      _ = 1 := by field_simp
  have h2 : |M| ≤ √(M ^ 2 + 1) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  linarith [le_abs_self M]

end Lightlike.Regge.Linearized
