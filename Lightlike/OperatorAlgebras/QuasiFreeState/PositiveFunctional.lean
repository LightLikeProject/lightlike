import Mathlib

/-!
# Positive linear functionals on a star algebra: hermiticity and Cauchy–Schwarz

For a linear functional `ρ : A →ₗ[ℂ] ℂ` on a unital star algebra with `0 ≤ ρ (a* a)` for all `a`, the form
`(x, y) ↦ ρ (x* y)` is hermitian (`posFun_star_mul`) and satisfies the Cauchy–Schwarz inequality
(`posFun_norm_sq_le`). Both are the standard first steps of the GNS construction; they are used for the
purity theorem of `Lightlike.OperatorAlgebras.QuasiFreeState.Pure`.

The hypotheses are stated as `∀ a, 0 ≤ ρ (star a * a)` (the second field of `IsState`), so that this file
depends on Mathlib only.
-/

open scoped ComplexOrder ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

section PositiveFunctional

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (ρ : A →ₗ[ℂ] ℂ)

/-- **Hermiticity** of a positive functional: `ρ (y* x) = conj (ρ (x* y))`, by polarization. -/
theorem posFun_star_mul (hnn : ∀ a : A, 0 ≤ ρ (star a * a)) (x y : A) :
    ρ (star y * x) = conj (ρ (star x * y)) := by
  have h1 := (Complex.nonneg_iff.1 (hnn (x + y))).2
  have h2 := (Complex.nonneg_iff.1 (hnn (x + Complex.I • y))).2
  have hx := (Complex.nonneg_iff.1 (hnn x)).2
  have hy := (Complex.nonneg_iff.1 (hnn y)).2
  simp only [star_add, add_mul, mul_add, map_add, star_smul, smul_mul_assoc, mul_smul_comm, map_smul,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, smul_eq_mul, Complex.star_def,
    Complex.conj_I, neg_mul, zero_mul, one_mul, neg_smul, map_neg, Complex.neg_im,
    Complex.neg_re, zero_add, Complex.mul_re] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- **Cauchy–Schwarz** for a positive functional: `|ρ (x* y)|² ≤ Re ρ (x* x) · Re ρ (y* y)`. -/
theorem posFun_norm_sq_le (hnn : ∀ a : A, 0 ≤ ρ (star a * a)) (x y : A) :
    ‖ρ (star x * y)‖ ^ 2 ≤ (ρ (star x * x)).re * (ρ (star y * y)).re := by
  set_option linter.style.haveILetI false in
  letI c : PreInnerProductSpace.Core ℂ A :=
    { inner := fun x y => ρ (star x * y)
      conj_inner_symm := fun x y => by
        show conj (ρ (star y * x)) = ρ (star x * y)
        exact (posFun_star_mul ρ hnn y x).symm
      re_inner_nonneg := fun x => (Complex.nonneg_iff.1 (hnn x)).1
      add_left := fun x y z => by
        show ρ (star (x + y) * z) = ρ (star x * z) + ρ (star y * z)
        rw [star_add, add_mul, map_add]
      smul_left := fun x y r => by
        show ρ (star (r • x) * y) = conj r * ρ (star x * y)
        rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul]
        rfl }
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) x y
  have h' : ‖ρ (star y * x)‖ = ‖ρ (star x * y)‖ := by
    rw [posFun_star_mul ρ hnn x y, Complex.norm_conj]
  change ‖ρ (star x * y)‖ * ‖ρ (star y * x)‖ ≤ (ρ (star x * x)).re * (ρ (star y * y)).re at h
  rw [h', ← sq] at h
  exact h

end PositiveFunctional

end Lightlike.OperatorAlgebras.QuasiFreeState
