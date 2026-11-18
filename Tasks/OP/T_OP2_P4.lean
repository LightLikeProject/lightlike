import Lightlike.OperatorAlgebras.FockIrreducible

/-!
# Task T-OP2-P4

Every nonzero vector of a Fock representation is cyclic for the Weyl unitaries (the Fock representation is irreducible)

The statement is `Lightlike.OperatorAlgebras.fockRep_cyclic_of_ne_zero`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. The closed span of `W f ψ` is invariant, so its projection commutes with every `W f`; the projection onto the vacuum is a limit of Gaussian averages of the Weyl unitaries (over the span of finitely many vectors), which shows that the commutant is trivial.

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

/-- **Irreducibility of the Fock representation**: every nonzero vector `ψ` is cyclic for the Weyl unitaries,
`closure (span {W f ψ}) = ⊤`.

This is a step of the library's proof of Shale's criterion (`T-OP2-P3`, source as there), stated for the cyclic vacuum characterization `FockRep`; it is not claimed to match a statement of another source. -/
theorem fockRep_cyclic_of_ne_zero {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) {ψ : K} (hψ : ψ ≠ 0) :
    (Submodule.span ℂ (Set.range fun f => R.W f ψ)).topologicalClosure = ⊤ := by
  exact fockRep_cyclic R hψ

end Lightlike.OperatorAlgebras
