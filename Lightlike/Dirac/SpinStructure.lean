import Mathlib
import Lightlike.Dirac.Flat

/-!
# Spin lifts of frame changes

A spin structure on a Riemannian manifold lifts every change of orthonormal frame, a rotation
`R ∈ SO(n)`, to an element of the spin group `Spin(n) ⊂ Cl(ℝⁿ, -‖·‖²)` acting on vectors by
conjugation, so that the lifts compose on triple overlaps.  This file fixes the algebraic part:
`IsSpinLift R s` says that `s` lies in Mathlib's `spinGroup` and conjugates the basis vector `eₐ` to
the vector with coordinates `R a ·`.  It is stated in the Clifford algebra itself, with no choice
of preimage under `ι`, so that no injectivity of `ι` is needed.

Lifts compose: if `s` lifts `R` and `t` lifts `R'` then `s * t` lifts `R' * R`
(`IsSpinLift.mul`), the algebraic content of the cocycle condition.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §1 (spin groups) and §1
  (spin structures, Definition 1.3); no equation number is claimed.
-/

open CliffordAlgebra

namespace Lightlike.Dirac

variable {n : ℕ}

/-- `s` is a **spin lift** of the frame change `R`: `s` is in `Spin(n)` (Mathlib's `spinGroup` of
the form `Qneg n`) and conjugation by `s` sends the basis vector `eₐ` to `∑ᵦ R a b eᵦ`. -/
def IsSpinLift (R : Matrix (Fin n) (Fin n) ℝ) (s : CliffordAlgebra (Qneg n)) : Prop :=
  s ∈ spinGroup (Qneg n) ∧
    ∀ a, s * ι (Qneg n) (e a) * star s = ι (Qneg n) (∑ b, R a b • e b)

/-- The identity lifts the identity frame change. -/
theorem isSpinLift_one : IsSpinLift (1 : Matrix (Fin n) (Fin n) ℝ) 1 := by
  refine ⟨(spinGroup (Qneg n)).one_mem, fun a => ?_⟩
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- Spin lifts compose: `s` lifts `R`, `t` lifts `R'`, then `s * t` lifts `R' * R`. -/
theorem IsSpinLift.mul {R R' : Matrix (Fin n) (Fin n) ℝ} {s t : CliffordAlgebra (Qneg n)}
    (hs : IsSpinLift R s) (ht : IsSpinLift R' t) : IsSpinLift (R' * R) (s * t) := by
  refine ⟨(spinGroup (Qneg n)).mul_mem hs.1 ht.1, fun a => ?_⟩
  have h1 : s * t * ι (Qneg n) (e a) * star (s * t) =
      s * (t * ι (Qneg n) (e a) * star t) * star s := by
    rw [star_mul]; noncomm_ring
  rw [h1, ht.2 a]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  simp only [hs.2, map_sum, map_smul, Matrix.mul_apply, Finset.sum_smul]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

end Lightlike.Dirac
