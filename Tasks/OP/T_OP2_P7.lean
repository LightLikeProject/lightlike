import Lightlike.OperatorAlgebras.Weyl

/-!
# Task T-OP2-P7

Shale's criterion, sufficiency: a Bogoliubov transformation with Hilbert-Schmidt antilinear part is implementable

The statement is `Lightlike.OperatorAlgebras.shale_sufficiency`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Build the squeezed vector `Ψ` (a vector with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)`) as a limit of finite-mode squeezed vectors, whose Cauchy estimate is `∑ ‖β eᵢ‖² < ∞`; then `T-OP2-P5` gives the unitary.

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

/-- **Shale's criterion, sufficiency**: if the antilinear part `β` of a Bogoliubov transformation `T` is Hilbert-Schmidt,
`T` is implemented by a unitary of the Fock representation.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the Fock
representation is the cyclic vacuum characterization of `FockRep`, not the symmetric Fock space;
`IsHilbertSchmidt` requires `∑ ‖β bᵢ‖² < ∞` for every Hilbert basis; `h` is an arbitrary complex Hilbert
space here (whether the source assumes it separable is not checked). -/
theorem shale_sufficiency {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) (T : Bogoliubov h) (hβ : IsHilbertSchmidt T.betaPart) :
    Implements R.toCCRRep T := by
  sorry

end Lightlike.OperatorAlgebras
