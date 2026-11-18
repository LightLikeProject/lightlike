# OP6: the trace-class layer is a port, and what is compared

The trace-class and Hilbert-Schmidt layer (`Lightlike/OperatorAlgebras/TraceClass/`, 14 modules, about 4000 lines) is ported from
Physlib (the `TraceClass` subtree of `PhyslibAlpha/ProbabilisticTheory/HilbertSpace` and the trace-pairing files of
`PhyslibAlpha/ProbabilisticTheory/WStarAlgebra`, Physlib commit `cdfa6094`, Apache 2.0, copyright Tom Ole Diem), with module headers
removed and the namespace `Lightlike.OperatorAlgebras.TraceClass`. No Physlib module of this subtree is imported (a dependency build in the
shared queue was avoided).

Covered, with the Lean names (milestone OP6 "done when"): the trace class `S¹` and the Hilbert-Schmidt operators `S²` as two-sided ideals
(`HilbertSchmidt` and `GeneralIdeal`/`IdealNorm` modules), `S² · S² ⊆ S¹` (`isTraceClass_mul_of_isHilbertSchmidt`), the trace is
independent of the basis and cyclic for Hilbert-Schmidt factors (`HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap`), `(S¹)* ≅ B(H)`
(`TraceClass.tracePairingLinearIsometry`, `TraceClass.tracePairing_surjective_concrete`).

Not covered: `K* ≅ S¹` (the dual of the compact operators), stated as the proof task `T-OP6-P1` (`Tasks/OP/T_OP6_P1.lean`); the trust check
"the diagonal operator with eigenvalues `1/n` is Hilbert-Schmidt and not trace class" (needs an explicit `ℓ²`); done: the identity of an
infinite-dimensional space is not Hilbert-Schmidt (`not_isHilbertSchmidt_one`), rank-one trace, finite-dimensional trace class.

Comparison with a source: none made. The source of the milestone, Reed and Simon, Methods of Modern Mathematical Physics I, Chapter VI "Bounded
Operators" (trace class and Hilbert-Schmidt operators, the duality theorem), has not been read at a location; the statements ported are those of
Physlib, whose docstrings cite no source ("References: None"). The comparison with Reed-Simon is therefore pending and no catalogue entry is
claimed as compared.
