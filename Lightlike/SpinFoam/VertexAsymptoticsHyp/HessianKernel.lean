import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Invertibility of a complex symmetric matrix from its real and imaginary parts
(linear-algebra step of route 1 of task T-SF10-P2)

If `B = A + i C` is complex symmetric with `A = Re B` positive semidefinite and no nonzero real vector
in `ker A ∩ ker C`, then `det B ≠ 0`. This reduces the invertibility of `-H` at a critical point to
`Im(-H)` being injective on the kernel of `Re(-H)`, once `Re(-H) ≥ 0` is known.
-/

open Matrix
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

/-- **A complex symmetric matrix with positive semidefinite real part is invertible when the real
and imaginary parts have no common real kernel vector.** -/
theorem det_ne_zero_of_re_psd_ker {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.transpose = B)
    (hpsd : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ ((B.map Complex.re) *ᵥ u))
    (hker : ∀ v : Fin n → ℝ, (B.map Complex.re) *ᵥ v = 0 → (B.map Complex.im) *ᵥ v = 0 → v = 0) :
    B.det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set A : Matrix (Fin n) (Fin n) ℝ := B.map Complex.re with hAdef
  set C : Matrix (Fin n) (Fin n) ℝ := B.map Complex.im with hCdef
  set u : Fin n → ℝ := fun i => (w i).re with hu
  set v : Fin n → ℝ := fun i => (w i).im with hv
  have hAs : A.transpose = A := by
    ext i k
    have := congrFun (congrFun hB i) k
    simp only [hAdef, Matrix.transpose_apply, Matrix.map_apply] at this ⊢
    rw [this]
  have hCs : C.transpose = C := by
    ext i k
    have := congrFun (congrFun hB i) k
    simp only [hCdef, Matrix.transpose_apply, Matrix.map_apply] at this ⊢
    rw [this]
  have hre : A *ᵥ u - C *ᵥ v = 0 := by
    ext i
    have := congrArg Complex.re (congrFun hw i)
    simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] at this
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Pi.zero_apply, hAdef, hCdef, hu, hv,
      Matrix.map_apply, ← Finset.sum_sub_distrib]
    exact this
  have him : A *ᵥ v + C *ᵥ u = 0 := by
    ext i
    have := congrArg Complex.im (congrFun hw i)
    simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.zero_apply, hAdef, hCdef, hu, hv,
      Matrix.map_apply, ← Finset.sum_add_distrib]
    have h0 : ((0 : Fin n → ℂ) i).im = 0 := rfl
    rw [h0] at this
    rw [← this]
  have hsym : u ⬝ᵥ (C *ᵥ v) = v ⬝ᵥ (C *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, ← hCs, Matrix.vecMul_transpose, dotProduct_comm]
    rw [hCs]
  have hAu : A *ᵥ u = C *ᵥ v := sub_eq_zero.mp hre
  have hAv : A *ᵥ v = -(C *ᵥ u) := eq_neg_of_add_eq_zero_left him
  have hsum : u ⬝ᵥ (A *ᵥ u) + v ⬝ᵥ (A *ᵥ v) = 0 := by
    rw [hAu, hAv, dotProduct_neg, hsym]; ring
  have hu0 := hpsd u
  have hv0 := hpsd v
  have hPSD : A.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => by simpa using hpsd x⟩
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hAs
  have h1 : A *ᵥ u = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff]; simp only [star_trivial]; linarith
  have h2 : A *ᵥ v = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff]; simp only [star_trivial]; linarith
  have h3 : C *ᵥ v = 0 := by rw [← hAu]; exact h1
  have h4 : C *ᵥ u = 0 := by
    have := hAv; rw [h2] at this; exact neg_eq_zero.mp this.symm
  have hu' := hker u h1 h4
  have hv' := hker v h2 h3
  apply hw0
  ext i
  apply Complex.ext
  · exact congrFun hu' i
  · exact congrFun hv' i

end Lightlike.Asymptotics.Lorentzian
