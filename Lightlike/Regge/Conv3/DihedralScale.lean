import Mathlib
import Lightlike.Regge.Conv3.DihedralDeriv

/-!
# Scale invariance of the dihedral angle in the squared lengths

Multiplying all six squared edge lengths of a tetrahedron by `t > 0` (a similarity of ratio `√t`)
does not change its dihedral angles. This reduces the angles of a small tetrahedron of a fine
lattice to the angles of the tetrahedron rescaled to size one, to which the uniform second-order
bound `dihSq_taylor` applies.

## Main results

* `cosSq_smul`, `dihSq_smul`: `cosSq` and `dihSq` are invariant under `(a, …, f) ↦ t • (a, …, f)`.
-/

open Real

namespace Lightlike.Regge.Conv3

private lemma Nn_smul {t : ℝ} (ht : 0 < t) (a b c d e f : ℝ) (ha : a ≠ 0) :
    Nn (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) = t * Nn a b c d e f := by
  unfold Nn
  have := ht.ne'
  field_simp

private lemma Pp_smul {t : ℝ} (ht : 0 < t) (a b c : ℝ) (ha : a ≠ 0) :
    Pp (t * a) (t * b) (t * c) = t * Pp a b c := by
  unfold Pp
  have := ht.ne'
  field_simp

/-- The cosine of a dihedral angle is invariant under scaling of the squared lengths. -/
theorem cosSq_smul {t : ℝ} (ht : 0 < t) {a b c d e f : ℝ} (ha : a ≠ 0) :
    cosSq (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) = cosSq a b c d e f := by
  unfold cosSq
  rw [Nn_smul ht a b c d e f ha, Pp_smul ht a b c ha, Pp_smul ht a d e ha,
    show t * Pp a b c * (t * Pp a d e) = t ^ 2 * (Pp a b c * Pp a d e) by ring,
    sqrt_mul (sq_nonneg t), sqrt_sq ht.le]
  by_cases h : √(Pp a b c * Pp a d e) = 0
  · simp [h]
  · field_simp

/-- A dihedral angle is invariant under scaling of the squared lengths. -/
theorem dihSq_smul {t : ℝ} (ht : 0 < t) {a b c d e f : ℝ} (ha : a ≠ 0) :
    dihSq (t * a) (t * b) (t * c) (t * d) (t * e) (t * f) = dihSq a b c d e f := by
  unfold dihSq
  rw [cosSq_smul ht ha]

/-- Non-vacuity and trust check: the regular tetrahedron with unit squared edges has dihedral
angle `arccos (1/3)`, and the doubled one has the same. -/
example : dihSq 2 2 2 2 2 2 = dihSq 1 1 1 1 1 1 := by
  simpa using dihSq_smul (t := 2) (by norm_num) (a := 1) (b := 1) (c := 1) (d := 1) (e := 1)
    (f := 1) one_ne_zero

end Lightlike.Regge.Conv3
