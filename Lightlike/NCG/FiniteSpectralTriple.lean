import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite spectral triples and their real structures

T. Krajewski, *Classification of finite spectral triples*, arXiv:hep-th/9701081, Section 2, pp. 2-9, and M. Paschke,
A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029, Section 2, pp. 2 and 5 (read): a finite
spectral triple is a finite-dimensional real `*`-algebra `A` (Krajewski's real case, p. 2; a complex algebra is in
particular real) with a faithful real-linear `*`-representation `π` on a finite-dimensional complex Hilbert space `H` and
a self-adjoint operator `D` on `H`. A real structure is an antiunitary
involution `J` such that `π(a)` commutes with `J π(b) J` (order zero) and with `[D, π(a)]` (first order), and `DJ = JD`;
a grading is a self-adjoint involution `γ` commuting with `π(A)` and `J` and anticommuting with `D`. These are the
signs of KO-dimension `0` (`J² = 1`, `JD = DJ`, `Jγ = γJ`).

* `FiniteSpectralTriple A H`;
* `FiniteSpectralTriple.comm`, `RealStructure T` (`J`, `inner_J`, `J_J`, `order_zero`, `first_order`, `D_J`);
* `Grading T R` (`γ`, `γ_γ`, `γ_J`, `γ_π`, `D_γ`).
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

/-- **A finite spectral triple** (Krajewski, Section 2, p. 2; Paschke-Sitarz, Section 2, p. 2): a faithful real-linear
`*`-representation `π` of a finite-dimensional real `*`-algebra `A` on a finite-dimensional complex Hilbert space `H`,
and a self-adjoint operator `D` on `H`. -/
structure FiniteSpectralTriple (A H : Type*) [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H] where
  /-- The representation. -/
  π : A →⋆ₐ[ℝ] (H →L[ℂ] H)
  /-- `π` is faithful. -/
  injective_π : Function.Injective π
  /-- The Dirac operator. -/
  D : H →L[ℂ] H
  /-- `D` is self-adjoint. -/
  isSelfAdjoint_D : IsSelfAdjoint D

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

namespace FiniteSpectralTriple

/-- The commutator `[S, T] = S T - T S` of two operators. -/
def comm (S T : H →L[ℂ] H) : H →L[ℂ] H := S * T - T * S

end FiniteSpectralTriple

open FiniteSpectralTriple

/-- **A real structure of KO-dimension `0`** (Krajewski, Section 2.1, p. 3, and Section 2.4, p. 9; Paschke-Sitarz,
Section 2, p. 2, and (2), p. 5): an antiunitary involution `J` (`⟪J x, J y⟫ = ⟪y, x⟫`, `J² = 1`) such that `J π(b) J` commutes
with `π(a)` (order zero) and with `[D, π(a)]` (first order), and `D J = J D`. -/
structure RealStructure (T : FiniteSpectralTriple A H) where
  /-- The charge conjugation, an antilinear map. -/
  J : H →ₗ⋆[ℂ] H
  /-- `J` is antiunitary. -/
  inner_J : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- `J² = 1`. -/
  J_J : ∀ x, J (J x) = x
  /-- The order-zero condition `[π(a), J π(b) J] = 0`. -/
  order_zero : ∀ a b x, T.π a (J (T.π b (J x))) = J (T.π b (J (T.π a x)))
  /-- The first-order condition `[[D, π(a)], J π(b) J] = 0`. -/
  first_order : ∀ a b x, comm T.D (T.π a) (J (T.π b (J x))) = J (T.π b (J (comm T.D (T.π a) x)))
  /-- `D J = J D`. -/
  D_J : ∀ x, T.D (J x) = J (T.D x)

/-- **A grading** (Paschke-Sitarz, Section 2, p. 2, and `Dγ = -γD`, p. 5): a self-adjoint involution `γ` commuting
with `π(A)` and `J` and anticommuting with `D`. -/
structure Grading (T : FiniteSpectralTriple A H) (R : RealStructure T) where
  /-- The grading operator. -/
  γ : H →L[ℂ] H
  /-- `γ` is self-adjoint. -/
  isSelfAdjoint_γ : IsSelfAdjoint γ
  /-- `γ² = 1`. -/
  γ_γ : γ * γ = 1
  /-- `γ J = J γ`. -/
  γ_J : ∀ x, γ (R.J x) = R.J (γ x)
  /-- `γ π(a) = π(a) γ`. -/
  γ_π : ∀ a, γ * T.π a = T.π a * γ
  /-- `D γ = -γ D`. -/
  D_γ : T.D * γ = -(γ * T.D)

end Lightlike.NCG
