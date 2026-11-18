import Lightlike.OperatorAlgebras.TraceClass.TracePairingSurjectivity

/-!
# Task T-OP6-P1

The dual of the compact operators is the trace class: every continuous functional on the compact operators of a Hilbert
space is `K ↦ Tr (K T)` for a unique trace-class operator `T`, with `‖T‖₁ = ‖f‖`.

The statement is `Lightlike.OperatorAlgebras.TraceClass.compact_dual_eq_traceClass`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other change (CONTRIBUTING.md).

Route: the trace pairing is isometric (`tracePairingLinearIsometry` in the other direction: `(S¹)* ≅ B(H)` is in the library);
here finite-rank operators are dense in the compact ones, a functional on them gives a sesquilinear form on rank-one
operators, hence a bounded operator, and its polar decomposition shows it is trace class with the same norm.

Partial results, as helper lemmas in separate pull requests, are welcome.

## References

Milestone OP6 (Trace-class and Hilbert-Schmidt operators), ROADMAP section "Operator algebras and quantum
information".
Source: M. Reed and B. Simon, Methods of Modern Mathematical Physics I, Functional Analysis, Academic Press (1972),
Chapter: Bounded Operators (`reed-simon-1972` in docs/tasks/sources.yaml); the location of this statement in the chapter
has not been read, the comparison is pending.
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
  sorry

end Lightlike.OperatorAlgebras.TraceClass
