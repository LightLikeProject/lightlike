import Lightlike.Regge.Complex
import Lightlike.PonzanoRegge.Asymptotics

/-!
# A wrong-model control for the second-order expansion: the boundary of the 4-simplex

The expansion `regge_second_order` needs a flat complex. The boundary of the 4-simplex on five vertices,
with all edge lengths equal to `1`, is a closed complex in which every edge lies in three tetrahedra, and
every deficit angle is `2π - 3 arccos (1/3) > 0` (`simplexBoundary_deficit_pos`). The flatness hypothesis
therefore fails there. This file proves only the failure of the hypothesis (`simplexBoundary_deficit_pos`); it does not prove that
the conclusion of `regge_second_order` fails (the first-order term of the Regge action along a line of squared lengths is not
computed here).

## Main results

* `simplexBoundary`: the boundary of the 4-simplex as a `Complex3 (Fin 5)`.
* `dihedral_regular`: the regular dihedral angle is `arccos (1/3)`.
* `simplexBoundary_deficit_pos`: every deficit angle is positive.
-/

open Real Finset
namespace Lightlike.Regge.Linear3
open Lightlike.Regge
open Lightlike.PR (Complex3 dihedral cosDihedral)

/-- The boundary of the 4-simplex on five vertices: its five tetrahedra. -/
def simplexBoundary : Complex3 (Fin 5) where
  tets := univ.image fun i => univ.erase i
  card_eq := by
    intro t ht
    simp only [mem_image, mem_univ, true_and] at ht
    obtain ⟨i, rfl⟩ := ht
    simp

/-- Every edge of the boundary of the 4-simplex lies in exactly three tetrahedra. -/
theorem simplexBoundary_star (e : Finset (Fin 5)) (he : e.card = 2) :
    (star simplexBoundary e).card = 3 := by
  revert e
  decide


/-- The regular dihedral angle: `dihedral 1 1 1 1 1 1 = arccos (1/3)`. -/
theorem dihedral_regular : dihedral 1 1 1 1 1 1 = arccos (1 / 3) := by
  unfold dihedral cosDihedral
  congr 1
  have : √((1 ^ 2 - ((1 ^ 2 + 1 ^ 2 - 1 ^ 2) / (2 * 1)) ^ 2) * (1 ^ 2 - ((1 ^ 2 + 1 ^ 2 - 1 ^ 2) / (2 * 1)) ^ 2)) = 3 / 4 := by
    rw [show (1 ^ 2 - ((1 ^ 2 + 1 ^ 2 - 1 ^ 2) / (2 * 1)) ^ 2 : ℝ) = 3 / 4 by norm_num,
      Real.sqrt_mul_self (by norm_num)]
  simp only [this]
  norm_num

/-- **Wrong-model control.** On the boundary of the 4-simplex with all lengths equal (a closed
complex), every deficit angle is positive, so the flatness hypothesis of `regge_second_order` fails. -/
theorem simplexBoundary_deficit_pos {e : Finset (Fin 5)} (he : e.card = 2) :
    0 < deficit simplexBoundary (fun _ => 1) e := by
  rw [deficit_const _ 1 he, simplexBoundary_star e he, dihedral_regular]
  have h1 : arccos (1 / 3) < arccos (-(1 / 2)) :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have h2 : arccos (-(1 / 2) : ℝ) = 2 * π / 3 := by
    have h3 : arccos (1 / 2 : ℝ) = π / 3 := by
      rw [← Real.cos_pi_div_three]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rw [Real.arccos_neg, h3]; ring
  push_cast
  linarith

end Lightlike.Regge.Linear3
