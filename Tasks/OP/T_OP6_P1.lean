import Lightlike.OperatorAlgebras.CompactDualIso

/-!
# Task T-OP6-P1

The dual of the compact operators is the trace class: every continuous functional on the compact
operators is a trace pairing with a unique trace-class operator of the same norm.

The statement is `Lightlike.OperatorAlgebras.TraceClass.compact_dual_eq_traceClass`, at the end of
this file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. Finite-rank operators are dense in the compact ones; a functional on them gives a bounded
sesquilinear form on rank-one operators (`TraceClass.sesquilinearFormOfFunctional`), hence a bounded
operator by Riesz, and its polar decomposition shows it is trace class with `‖T‖₁ = ‖f‖` (Reed-Simon
I, Theorem VI.26).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/TraceClass/Banach.lean`: `OperatorAlgebras.TraceClass.TraceClass`
* `Lightlike/OperatorAlgebras/TraceClass/Pairing.lean`:
  `OperatorAlgebras.TraceClass.TraceClass.tracePairing`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.compactFunctional_eq` (`Lightlike/OperatorAlgebras/CompactDualIso.lean`)
* `OperatorAlgebras.compactFunctional_rankOne` (`Lightlike/OperatorAlgebras/CompactDualIso.lean`)
* `OperatorAlgebras.compactFunctional_finiteRank` (`Lightlike/OperatorAlgebras/CompactDualIso.lean`)
* `OperatorAlgebras.compact_dual_eq_traceClass_proof` (`Lightlike/OperatorAlgebras/CompactDualIso.lean`)
* `OperatorAlgebras.TraceClass.TraceClass.norm_tracePairing` (`Lightlike/OperatorAlgebras/TraceClass/TracePairingNorm.lean`)
* `OperatorAlgebras.TraceClass.TraceClass.tracePairing_apply` (`Lightlike/OperatorAlgebras/TraceClass/Pairing.lean`)
* `OperatorAlgebras.TraceClass.TraceClass.norm_tracePairing_le` (`Lightlike/OperatorAlgebras/TraceClass/Pairing.lean`)
* `OperatorAlgebras.TraceClass.TraceClass.tracePairing_rankOne` (`Lightlike/OperatorAlgebras/TraceClass/TracePairingNorm.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.TraceClass.compact_dual_eq_traceClass

## References

Milestone OP6 (Trace-class and Hilbert–Schmidt operators), ROADMAP section "Operator algebras and
quantum information".
Source: M. Reed and B. Simon, Methods of Modern Mathematical Physics I: Functional Analysis,
Academic Press (1972), Chapter: Bounded Operators (`reed-simon-1972` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

universe u

namespace Lightlike.OperatorAlgebras.TraceClass

/-- **`𝒦(H)* ≅ 𝒮₁(H)`**: every continuous linear functional `f` on the compact operators of a complex Hilbert space `H` is
the trace pairing `K ↦ Tr (K T)` with a trace-class operator `T`, which is unique and has trace norm `‖f‖`.

**Differences from the source** (not yet read at the cited location; the comparison is pending): none known. -/
theorem compact_dual_eq_traceClass {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : (compactOperator (RingHom.id ℂ) H H) →L[ℂ] ℂ) :
    ∃ T : TraceClass H, (∀ K : compactOperator (RingHom.id ℂ) H H, f K = TraceClass.tracePairing K.1 T) ∧
      ‖T‖ = ‖f‖ ∧
      ∀ T' : TraceClass H, (∀ K : compactOperator (RingHom.id ℂ) H H, f K = TraceClass.tracePairing K.1 T') →
        T' = T := by
  exact Lightlike.OperatorAlgebras.compact_dual_eq_traceClass_proof f

end Lightlike.OperatorAlgebras.TraceClass
