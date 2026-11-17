import Lightlike.OperatorAlgebras.Weyl

/-!
# Task T-OP2-P2

The Fock representation is unique up to unitary equivalence.

The statement is `Lightlike.OperatorAlgebras.fockRep_unique`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. The map `W f Ω ↦ W' f Ω'` preserves inner products by the Weyl relation and the vacuum
expectation; extend by cyclicity.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Weyl.lean`: `OperatorAlgebras.FockRep`, `OperatorAlgebras.FockRep.Ω`,
  `OperatorAlgebras.CCRRep.W`, `OperatorAlgebras.FockRep.toCCRRep`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.FockRep.cyclic` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.vacuum_expectation` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.norm_Ω` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.inj` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.injEq` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.sizeOf_spec` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.CCRRep.weyl` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.CCRRep.W_zero` (`Lightlike/OperatorAlgebras/Weyl.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.fockRep_unique

## References

Milestone OP2 (CCR and CAR algebras), ROADMAP section "Operator algebras and quantum information".
Source: O. Bratteli and D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, 2nd
ed., Springer (1997), Chapter: Continuous Quantum Systems. I (`bratteli-robinson-1997` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

universe u

namespace Lightlike.OperatorAlgebras

/-- **Uniqueness of the Fock representation**: two Fock representations of the same `h` are unitarily
equivalent, by a unitary that maps the vacuum to the vacuum and intertwines the Weyl unitaries.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the
representation is the cyclic vacuum characterization of `FockRep`, not the symmetric Fock space. -/
theorem fockRep_unique {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
    {K₁ K₂ : Type*} [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
    [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
    (R : FockRep h K₁) (S : FockRep h K₂) :
    ∃ U : K₁ ≃ₗᵢ[ℂ] K₂, U R.Ω = S.Ω ∧ ∀ f ψ, U (R.W f ψ) = S.W f (U ψ) := by
  sorry

end Lightlike.OperatorAlgebras
