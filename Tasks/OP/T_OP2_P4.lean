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

**Differences from the source** (not yet read at the cited location, and no numbered result has been looked up:
the comparison is pending): (a) the source states irreducibility of the Weyl operators on Fock space (a
trivial commutant); "every nonzero vector is cyclic" is equivalent to it, since the closed span of an orbit
`{W f ψ}` is invariant by the Weyl relations, and a closed invariant subspace contains the closed span of each
of its vectors (kind: representation); (b) the Fock representation is the cyclic vacuum (GNS) characterization
`FockRep` of the Weyl relations with the Fock expectation, unique up to unitary equivalence
(`fockRep_unique`), not the symmetric Fock space (kind: representation); `h` is an arbitrary complex
inner product space here, and whether the source assumes it complete is not checked (a generalization). -/
theorem fockRep_cyclic_of_ne_zero {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) {ψ : K} (hψ : ψ ≠ 0) :
    (Submodule.span ℂ (Set.range fun f => R.W f ψ)).topologicalClosure = ⊤ := by
  exact fockRep_cyclic R hψ

end Lightlike.OperatorAlgebras
