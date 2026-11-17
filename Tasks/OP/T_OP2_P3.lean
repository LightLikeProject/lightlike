import Lightlike.OperatorAlgebras.Weyl

/-!
# Task T-OP2-P3

Shale's criterion: a Bogoliubov transformation is implementable in the Fock representation iff its
antilinear part is Hilbert–Schmidt.

The statement is `Lightlike.OperatorAlgebras.shale`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Implementability by the unitary built from the Bogoliubov coefficients (Shale 1962;
Bratteli–Robinson 2, Chapter 5); the converse by the number operator and the vacuum's image.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Weyl.lean`: `OperatorAlgebras.FockRep`, `OperatorAlgebras.Bogoliubov`,
  `OperatorAlgebras.Implements`, `OperatorAlgebras.FockRep.toCCRRep`,
  `OperatorAlgebras.IsHilbertSchmidt`, `OperatorAlgebras.Bogoliubov.betaPart`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.FockRep.cyclic` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.vacuum_expectation` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.norm_Ω` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.inj` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.injEq` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.Bogoliubov.mk.inj` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.Bogoliubov.symp_map` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.Bogoliubov.mk.injEq` (`Lightlike/OperatorAlgebras/Weyl.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.shale

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

/-- **Shale's criterion**: a Bogoliubov transformation `T` of `h` is implemented by a unitary of the Fock
representation iff its antilinear part `β` is Hilbert–Schmidt.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the Fock
representation is the cyclic vacuum characterization of `FockRep`, not the symmetric Fock space;
`IsHilbertSchmidt` requires `∑ ‖β bᵢ‖² < ∞` for every Hilbert basis, `β` being the antilinear part
`(T f + i T (i f)) / 2` of the real-linear map `T`; `h` is an arbitrary complex Hilbert space here; whether the source assumes it separable is not checked. -/
theorem shale {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (R : FockRep h K) (T : Bogoliubov h) :
    Implements R.toCCRRep T ↔ IsHilbertSchmidt T.betaPart := by
  sorry

end Lightlike.OperatorAlgebras
