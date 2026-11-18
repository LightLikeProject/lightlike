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

## Source read: Kostenko, "Trace Ideals with Applications" (lecture notes, University of Ljubljana)

Read (the free PDF, Chapter 3 "Trace Ideals"): Theorem 3.2.3 (the trace class `S¹` is a two-sided symmetric ideal, `‖BA‖₁ ≤ ‖B‖‖A‖₁`,
`‖AB‖₁ ≤ ‖B‖‖A‖₁`), Theorem 3.2.4 (for `A ∈ S¹` the sum `∑ (Aφₙ, φₙ)` converges absolutely and is independent of the orthonormal basis; `tr (AB) = tr (BA)`
for `B` bounded), Theorem 3.3.1 (`S²` is a two-sided symmetric ideal; `∑ (B*Aφₙ, φₙ)` independent of the basis; `S²` a Hilbert space) and
Remark 3.2.1 (iii) (`S∞(H)* = S¹(H)`, `S¹(H)* = B(H)`, with the proof deferred to another book). The source works on a separable Hilbert space.

Match: ideal property, basis independence and cyclicity of the trace are the statements of Theorems 3.2.3, 3.2.4, 3.3.1 (the ported versions are for
Hilbert bases of any complex Hilbert space, and the cyclicity is stated for Hilbert-Schmidt factors `R`, `S`, not for `S¹` times bounded). The duality
`(S¹)* = B(H)` is Remark 3.2.1 (iii) (a remark, proof not in these notes); `K* = S¹` is the same remark and is not proved here (task `T-OP6-P1`).

Differences: separable versus arbitrary Hilbert space; cyclicity for `S¹ · B(H)` of the source is not stated in this form by the ported lemma
(only for Hilbert-Schmidt pairs); the source's `S¹`-ideal norm inequalities are in the ported `IdealNorm` module and were not compared line by line.

## Plan for the proof of `T-OP6-P1` (`K* ≅ S¹`), bricks

(1) done: `FiniteRankApprox.exists_finiteRank_approx` (compact operators are norm limits of finite-rank operators). (2) from `f ∈ K*` the bounded
sesquilinear form `s (x, y) = f (|x⟩⟨y|)` (`‖|x⟩⟨y|‖ = ‖x‖ ‖y‖`) and the bounded operator `T` it defines (as in the ported
`sesquilinearFormOfFunctional`, there for functionals on the trace class). (3) `T` is trace class with `‖T‖₁ ≤ ‖f‖`: for finite orthonormal
families `φₙ`, `ψₙ`, `∑ |⟪ψₙ, T φₙ⟫| = |f (∑ cₙ |φₙ⟩⟨ψₙ|)| ≤ ‖f‖` with unimodular `cₙ`, since `‖∑ cₙ |φₙ⟩⟨ψₙ|‖ ≤ 1`; the trace-norm
characterisation by such sums is in `IdealNorm` (`traceNorm_eq_tsum_norm_inner_polarFactor`). (4) `f K = Tr (K T)` on finite-rank `K` by (2), on compact `K`
by (1) and continuity; `‖T‖₁ = ‖f‖` by the pairing isometry; uniqueness by the injectivity of the trace pairing.
