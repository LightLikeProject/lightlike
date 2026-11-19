# T-HA5 Peter–Weyl: source check and proof route

Status of this note: written on the branch `spinfoam/ha5-peterweyl`, 18 November 2026.

## What was checked against a source

Primary text read (opened and read, 18 November 2026): T. Tao, "The Peter–Weyl theorem, and non-abelian Fourier
analysis on compact groups", blog post of 23 January 2011,
https://terrytao.wordpress.com/2011/01/23/the-peter-weyl-theorem-and-non-abelian-fourier-analysis-on-compact-groups/
(§1 "Proof of the Peter–Weyl theorem": Lemma 2 (Schur), Corollaries 3–5, Propositions 6–8, Theorem 1; §2). The
page text was read up to character 100000 of 139891; §2 beyond that point was not read. Hypotheses there: `G`
compact Hausdorff, Haar probability measure; second countability is not assumed.

| Formal statement (Lean) | Source location (Tao) | Match |
| --- | --- | --- |
| `schur_zero_or_equivalent` (intertwiner between irreducible unitary matrix representations is `0` or an isomorphism) | Lemma 2 | match; Tao's proof is by the spectral theorem for `T*T`, ours by kernel and range of `T` being invariant (finite dimension) |
| `schur_scalar` (an endomorphism commuting with an irreducible representation is a scalar) | Lemma 2 / Corollary 4 | match (finite-dimensional case, algebraic closedness of `ℂ`) |
| `schur_orthogonality_eq` (`∫ ρ_{ij} conj ρ_{lk} = δ_{il} δ_{jk}/dim`) | Corollary 5 (`(1/dim) tr(T) I = ∫ ρ(g) T ρ(g)* dμ`) and the computation in Proposition 8 | match, entrywise form |
| `schur_orthogonality_ne` | Corollary 3 (subrepresentations of different isomorphism classes are orthogonal), Proposition 8 | match, entrywise form |
| proof route of `exists_matrixCoeff_ne` (compact self-adjoint convolution operator, finite-dimensional invariant eigenspaces, approximate identity) | Proposition 7 | same strategy; Tao argues by the orthogonal complement of the isotypic components, ours produces matrix coefficients that separate points, then Stone–Weierstrass |
| Hilbert basis of `L²(G)` from the coefficients of irreducible representations (to do) | Proposition 7 (`L²(G) = ⊕ L²(G)_ξ`), Proposition 8 (`dim(V_ξ)^{1/2} ι_ξ` unitary) | formalised as `peterWeyl_hilbertBasis` and `peterWeyl_isHilbertSum`; see the table under "Additions" below |

Tao does not state the density of the matrix coefficients in `C(G)`; that statement is checked against
MathWorld / Bröcker–tom Dieck as below.

Source read: the MathWorld article "Peter–Weyl Theorem" (https://mathworld.wolfram.com/Peter-WeylTheorem.html),
which lists Bröcker–tom Dieck, *Representations of compact Lie groups* (Springer GTM 98, 1985), Chapter III,
"Representative Functions" (https://rd.springer.com/chapter/10.1007/978-3-662-12918-0_3) among its references. The
chapter's abstract and the MathWorld statement were read; the text of the book chapter (theorem and equation
numbers) was **not** read.

| Formal statement (Lean) | Source statement | Match |
| --- | --- | --- |
| `peterWeyl_dense_continuous`: the span of the matrix coefficients of finite-dimensional continuous unitary representations is dense in `C(G, ℂ)` in the sup norm, `G` compact Hausdorff | MathWorld, Theorem part 1: for compact `G`, the representative functions are dense in the continuous functions in the supremum norm | representation: the source takes all continuous representations on `ℂⁿ` (the span is the same for compact groups by Weyl's unitary trick, which we do not use); our set is smaller, so the Lean statement implies the source statement. The source says Lie group, we assume a compact Hausdorff group (as the milestone text) |
| `peterWeyl_dense_L2`: the classes of the coefficients are dense in `L²(G, μ)`, `μ` a regular Haar measure | MathWorld part 2: dense in `L²(G)` for a Haar measure | convention: the Lean statement carries `[μ.Regular]` (Mathlib's `IsHaarMeasure` does not give regularity in the non-second-countable case) |

Checked against Tao's post after this was written: see "Additions" below. Still not checked against a
source: the character form as stated on MathWorld (part 3).
The MathWorld page does not state the Hilbert-space decomposition; the book chapter has to be read for it.

## Proof route (not in the source)

The source proof goes through the compact self-adjoint convolution operator. In Lean:

1. `MatrixCoefficient.lean`: the span of the matrix coefficients is a star subalgebra (Kronecker product,
   conjugate, trivial representation); Stone–Weierstrass reduces density to separation of points.
2. `ConvolutionOperator.lean`, `KernelOperator.lean`, `KernelAdjoint.lean`, `ConvolutionSelfAdjoint.lean`: the
   operators `T_k` with continuous kernel on `L²`, compact by Arzelà–Ascoli; the adjoint formula
   `(T_k)* = T_{k†}` by Stone–Weierstrass on `G × G` (no Fubini, so no second countability).
3. `LeftTranslation.lean`, `ConvolutionEigen.lean`, `InvariantRep.lean`: `K_φ` commutes with left translations,
   its eigenspaces for nonzero eigenvalues are finite-dimensional, left invariant, consist of continuous
   functions, and carry a unitary matrix representation.
4. `ApproxIdentity.lean`, `PeterWeylSeparation.lean`: approximate identities and the spectral theorem for
   compact self-adjoint operators (Mathlib) give separation of points.
5. `PeterWeyl.lean`: the two density statements.

## Additions on `fable2/ha5-peterweyl` (18 November 2026, stream fable2)

Tao's post was read again on 18 November 2026 (characters 0 to 100000 of 139891; the rest of §2 not read).
Statements read there: "Throughout these notes, G is a fixed compact group" (topological groups Hausdorff,
normalised Haar measure); Theorem 1 (the regular representation on `L²(G)` is the direct sum of the irreducible
representations `ρ_ξ`, each with multiplicity `dim V_ξ`); Proposition 7 (`L²(G) = ⊕_ξ L²(G)_ξ`, where
`L²(G)_ξ` is spanned by the functions `g ↦ ⟨v, ρ_ξ(g) w⟩`); Proposition 8 (`dim(V_ξ)^{1/2} ι_ξ` is unitary
`HS(V_ξ) → L²(G)_ξ`, with `ι_ξ(T)(g) = ⟨T, ρ_ξ(g)*⟩_HS`); and, in §2, that the characters `χ_ξ` form an
orthonormal basis of the class functions `L²(G)^G`.

| Formal statement (Lean) | Source location (Tao) | Match |
| --- | --- | --- |
| `peterWeyl_isHilbertSum`: `L²(G, μ)` is the Hilbert sum (`IsHilbertSum`) of the subspaces `isotypic μ π`, `π` a class of irreducible unitary matrix representations | Proposition 7 | match. Representation: `isotypic μ π` is the span of the entries `g ↦ ρ(g)_{ij}` of a representative, Tao's `L²(G)_ξ` the span of `g ↦ ⟨v, ρ_ξ(g) w⟩`; the same space (entries are the case of basis vectors, and `isotypic_eq_span_of_mem` shows independence of the representative). Our statement needs `[μ.Regular]` (convention, as for `peterWeyl_dense_L2`) |
| `finrank_isotypic`: `dim isotypic μ π = (dim π)²` | Proposition 8 (`L²(G)_ξ ≅ HS(V_ξ)`) | weaker in form: the source gives a unitary `HS(V_ξ) → L²(G)_ξ`; we state the dimension and, in `peterWeyl_hilbertBasis`, that the functions `√(dim π) ρ_{ij}` are an orthonormal basis (the images of the matrix units under `√dim · ι_ξ`, up to the index convention). The map `ι_ξ` itself is not defined |
| `peterWeyl_hilbertBasis`: the functions `√(dim π) · π_{ij}` form a Hilbert basis of `L²(G, μ)` | Propositions 7 and 8 together | representation: basis form of "`L² = ⊕ L²(G)_ξ` and `√dim ι_ξ` unitary" |
| `character_orthogonality_eq`, `character_orthogonality_ne`: `∫ χ_ρ conj χ_σ = 1` or `0` | §2 (characters orthonormal in `L²(G)^G`), from Corollary 5 by taking traces | match for the orthonormality; the statement that the characters span the class functions is not formalised |

Checks (not source statements): `circle_hilbertBasis`, `circle_irreducible_classification` (U(1));
`su2_character_orthogonality`, `su2_schur_orthogonality` (SU(2), using `Lightlike.SU2.spinRep`);
`not_forall_memLp_two_of_measure_univ_eq_top`, `not_memLp_two_of_unique` (infinite Haar measure, e.g. `ℝ`).

Mathlib (pinned v4.35.0 tree, grep on 18 November 2026): no Peter–Weyl theorem and no Schur orthogonality for
compact groups; `Mathlib/RepresentationTheory/Character.lean` has `char_orthonormal` for finite groups only.
Reused: Stone–Weierstrass (`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`), the
spectral theorem for compact self-adjoint operators, `ContinuousMap.toLp_denseRange`, `HilbertBasis.mk`,
`IsHilbertSum.mkInternal`, `Module.End.exists_eigenvalue`. Aligned with: `Representation.IsIrreducible`
(`UnitaryMatrixRep.isIrreducible_iff_toRepresentation`); Mathlib's `fourierBasis` on `AddCircle` is the same
statement as `circle_hilbertBasis` on a different model of the circle. Not read: Bröcker–tom Dieck, Chapter III
(no access to the text; no theorem numbers from it are cited).

On `fable2/ha5-followup`: `exists_isotypic_isometry` is Tao's Proposition 8 (read, see above): the map
`T ↦ √(dim ρ) tr(T ρ(·))` is a linear isometric isomorphism onto the isotypic component. Representation: the
Hilbert–Schmidt space `HS(V_ξ)` is `EuclideanSpace ℂ (ι × ι)` (matrix entries with the Frobenius inner product),
and Tao's `ι_ξ(T)(g) = ⟨T, ρ_ξ(g)*⟩_HS` is written as `tr(T ρ(g)) = ∑ i j, T (i, j) ρ(g) j i`. Equivariance of
the map under `G × G` is not stated. `real_not_forall_memLp_two`, `real_character_not_memLp_two`: the check for
`ℝ` (no source statement).
