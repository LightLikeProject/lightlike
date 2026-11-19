import Lightlike.OperatorAlgebras.FockReduction

/-!
# Task T-OP2-P5

A Bogoliubov transformation is implemented in a Fock representation iff there is a vector with Gaussian characteristic function exp(-|T f|^2/4)

The statement is `Lightlike.OperatorAlgebras.implements_iff_exists_gaussian_vector`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. `⇒`: `Ψ = U⁻¹ Ω` has `⟪Ψ, W f Ψ⟫ = ⟪Ω, W (T f) Ω⟫`. `⇐`: the vectors `W (T f) Ω` and `W f Ψ` have the same Gram matrix (the transformation preserves the symplectic form), `Ψ` is cyclic by irreducibility, and the Gram unitary (`exists_unitary_of_gram_eq`) intertwines.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

## References

Milestone OP2 (CCR and CAR algebras), ROADMAP section "Operator algebras and quantum information".
Source: O. Bratteli and D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd
ed., Springer (1997), Chapter: Continuous Quantum Systems. I (`bratteli-robinson-1997` in
docs/tasks/sources.yaml).
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

/-- **The cyclic-vector reduction of Shale's criterion**: a Bogoliubov transformation `T` is implemented by a unitary
of a Fock representation iff there is a vector `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)` for all `f`.

This is the library's own reduction of the question whether a Bogoliubov transformation is implemented to the existence of a vector with Gaussian characteristic function; it is not a statement of a source and is not attributed to one. -/
theorem implements_iff_exists_gaussian_vector {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) (T : Bogoliubov h) :
    Implements R.toCCRRep T ↔
      ∃ Ψ : K, ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ)) := by
  exact implements_iff_gaussian_vector R T

end Lightlike.OperatorAlgebras
