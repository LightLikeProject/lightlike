import Lightlike.OperatorAlgebras.FockExists

/-!
# Task T-OP2-P1

A Fock representation of the Weyl relations exists on every complex Hilbert space.

The statement is `Lightlike.OperatorAlgebras.fockRep_exists`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Symmetric Fock space `⨁ₙ Sym^n h` with the Weyl operators `exp(i φ(f))` (Bratteli–Robinson 2,
Section 5.2.3), or the GNS representation of the quasi-free state `ω(W f) = exp(-‖f‖²/4)`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Weyl.lean`: `OperatorAlgebras.FockRep`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.FockRep.mk.inj` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.norm_Ω` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.cyclic` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.injEq` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.mk.sizeOf_spec` (`Lightlike/OperatorAlgebras/Weyl.lean`)
* `OperatorAlgebras.FockRep.vacuum_expectation` (`Lightlike/OperatorAlgebras/Weyl.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.fockRep_exists

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

/-- **Existence of the Fock representation**: every complex Hilbert space `h` has a Fock representation of
the Weyl relations on some complex Hilbert space.

**Differences from the source** (not yet read at the cited location; the comparison is pending): a Fock
representation is characterized as a cyclic vacuum representation of the Weyl relations with the Fock
expectation `exp (-‖f‖² / 4)`, not built on the symmetric Fock space. -/
theorem fockRep_exists (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K),
      Nonempty (FockRep h K) := by
  exact ⟨FockSpace h, inferInstance, inferInstance, inferInstance, ⟨fockRepOf h⟩⟩

end Lightlike.OperatorAlgebras
