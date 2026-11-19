import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The contraction of two bilinear forms with respect to a third

For bilinear forms `g`, `A`, `B` on a finite-dimensional space and a basis `b`,
`formContract b g A B = tr(G⁻¹ A G⁻¹ B) = g^{ab} A_{bc} g^{cd} B_{da}`, with the matrices in the basis `b`.
It does not depend on the basis (`formContract_basis_indep`): it is the full contraction `⟨A, B⟩_g` of the
two forms with the inverse of `g`.

Supporting algebra for the intrinsic form of the Einstein–Hilbert first variation; no catalogue entry.
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The contraction `g^{ab} A_{bc} g^{cd} B_{da}` of two bilinear forms with the inverse of `g`, computed
in the basis `b`. -/
def formContract (b : Module.Basis (Fin n) ℝ V) (g A B : LinearMap.BilinForm ℝ V) : ℝ :=
  ((LinearMap.BilinForm.toMatrix b g)⁻¹ * LinearMap.BilinForm.toMatrix b A *
    (LinearMap.BilinForm.toMatrix b g)⁻¹ * LinearMap.BilinForm.toMatrix b B).trace

/-- A cancellation identity in a monoid, used for the change of basis. -/
lemma conj_cancel {R : Type*} [Monoid R] {u t p q : R} (hut : u * t = 1) (hpq : p * q = 1)
    (x a c : R) : (q * (x * u)) * (t * a * p) * (q * (x * u)) * (t * c * p) = q * (x * a * x * c) * p := by
  have h1 : ∀ z, u * (t * z) = z := fun z => by rw [← mul_assoc, hut, one_mul]
  have h2 : ∀ z, p * (q * z) = z := fun z => by rw [← mul_assoc, hpq, one_mul]
  simp only [mul_assoc, h1, h2]

/-- **The contraction does not depend on the basis.** -/
theorem formContract_basis_indep (b c : Module.Basis (Fin n) ℝ V) (g A B : LinearMap.BilinForm ℝ V) :
    formContract b g A B = formContract c g A B := by
  have hP : b.toMatrix c * c.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b c
  have hdet : IsUnit (b.toMatrix c).det := Matrix.isUnit_det_of_right_inverse hP
  have h1 : ((b.toMatrix c)ᵀ)⁻¹ * (b.toMatrix c)ᵀ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet)
  have h2 : b.toMatrix c * (b.toMatrix c)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) c g
  have hA := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) c A
  have hB := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) c B
  unfold formContract
  have ht : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ((b.toMatrix c)⁻¹ * X * b.toMatrix c).trace = X.trace := fun X => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [← hg, ← hA, ← hB, Matrix.mul_inv_rev, Matrix.mul_inv_rev, conj_cancel h1 h2, ht]

end Lightlike
