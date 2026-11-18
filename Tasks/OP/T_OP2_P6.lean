import Lightlike.OperatorAlgebras.Weyl

/-!
# Task T-OP2-P6

Shale's criterion, necessity: an implementable Bogoliubov transformation has Hilbert-Schmidt antilinear part

The statement is `Lightlike.OperatorAlgebras.shale_necessity`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. By `T-OP2-P5` there is `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)`. The overlap `|⟪Ω, Ψ⟫|²` is the limit over finite-dimensional subspaces of the Gaussian averages of `W f`, which is `∏ (1 + ‖β eᵢ‖²)⁻¹` for a Hilbert basis `eᵢ`; it is positive, so `∑ ‖β eᵢ‖² < ∞`.

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

/-- **Shale's criterion, necessity**: if a Bogoliubov transformation `T` is implemented in the Fock representation, its
antilinear part `β` is Hilbert-Schmidt.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the Fock
representation is the cyclic vacuum characterization of `FockRep`, not the symmetric Fock space;
`IsHilbertSchmidt` requires `∑ ‖β bᵢ‖² < ∞` for every Hilbert basis; `h` is an arbitrary complex Hilbert
space here (whether the source assumes it separable is not checked). -/
theorem shale_necessity {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) (T : Bogoliubov h) (hT : Implements R.toCCRRep T) :
    IsHilbertSchmidt T.betaPart := by
  sorry

end Lightlike.OperatorAlgebras
