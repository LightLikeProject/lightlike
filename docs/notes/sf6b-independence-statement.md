# SF6b: the statement of the independence of the EPRL state sum from the vertex order

Milestone: SF6b, item p2 (the dependence of the state sum on the vertex order).

## What is the object

`amplitudeI 1 K cut` (`Lightlike/SpinFoam/EPRLStateSum/IntrinsicVertex.lean`): the sum over the triangle colourings `col ≤ cut` of the
face weights `Π_f (col f + 1)` times the sum over the sorted labels of the tetrahedra of the product of the vertices of the
4-simplices. The vertex of a 4-simplex is `simpEIAux (J, z) = (-1)^(triPart J) Σ_l Π_a nodeI J a (z a) (l a) · ampP J l`, with the node
matrices `nodeI` of the sorted legs of each tetrahedron and `ampP` the Ooguri vertex amplitude. On a closed complex
`amplitudeI_one_eq_signed_ooguri` writes it as `Σ_col Σ_L [triangle constraints] · linkSign K col · weight K (col, L)`.

## The statement (to be proved)

For every closed 4-complex `K` on a linearly ordered vertex set `V`, every cutoff `cut` and every permutation `σ` of `V`
(a reordering of the vertices):

`amplitudeI 1 (K.relabel σ) (fun f => cut (f.map σ.symm)) = amplitudeI 1 K cut`,

where `K.relabel σ` has the 4-simplices `σ s` (definition to be added; for `∂Δ⁵` with `σ` any permutation of `Fin 6` the complex is
mapped to itself and the statement reads `amplitudeI 1 sphere6 (fun f => cut (f.map σ.toEmbedding)) = amplitudeI 1 sphere6 cut`).
Equivalently, the amplitude is the same for every linear order on the vertex set (the transport along an order isomorphism, `σ` as
an isomorphism from the new order to the old, is a separate lemma). The stronger per-colouring form: the summand of a colouring
(face weights times the sum over the tetrahedron labels of the vertex products) is unchanged by the relabelling of the colouring.

Variant with the form `ε` on the legs: gluing the tetrahedron by the pairing of an intertwiner with its dual through `ε` instead of the
identity multiplies the summand by `(-1)^(Σ_t J_t / 2)` (`fourJ_neg`), a function of the colouring only; the statement holds for
that gluing too.

## Evidence (MEASURED, numerical)

`docs/notes/sf6b-basis-free-gluing.md`: on `∂Δ⁵`, 14 colourings (colours up to 2) × 4 relabellings, the ratio of the summand is `1` to
`3e-15`; the bone cutoff of every one of the fifteen edges is `5`. The corrected vertex (the exact basis change `nodeT`) agrees with the
basis-free vertex to `4e-16` on 3600 vertex entries. Not a proof.

## Route (pieces, in order) and why the statement is true

Per colouring `col` the summand is the contraction of the vertex tensors of the 4-simplices along the tetrahedra, with the sum over the
sorted labels of a tetrahedron equal to the projector `P_t = Σ_z ι_z ⊗ ι_z` onto the invariants of its four legs, which does not depend
on the order of the legs (`sum_fourJT_mul_perm`). The only data that depend on the order are the orientations of the ten links of each
vertex (which end of the link reads the projection `m`, which `-m`, with the form `edgeSign (J, m) = (-1)^((J - m)/2)`). Relabelling the
vertices by `σ` reverses the orientation of the link `{p, q}` of the simplices containing `p, q` exactly when `σ` reverses the order of
`p, q`, and reversing a link multiplies the contraction by `(-1)^J` (`edgeSign_neg`, on the support of the parity). So the summand of
`σ K, col ∘ σ⁻¹` is the summand of `K, col` times `(-1)^e` with `e = Σ_{{p,q} inverted by σ} Σ_{s ∋ p, q} col (s ∖ {p, q})`.
Each inner sum is even, for every edge `{p, q}`: the triangles `f` with `f ∪ {p, q}` a 4-simplex form the link of the edge; the sum over
the tetrahedra `{p} ∪ f` of the four leg colours is even (the tetrahedron parity of the triangle constraints) and counts each triangle
`f` once and each side triangle `{p} ∪ e`, for an edge `e` of the link, twice (every tetrahedron `e ∪ {p, q}` lies in exactly two
4-simplices of a closed complex). So the summand is unchanged, with no sign. Steps:

1. the contraction `contract5` of five node tensors on `K₅` and `fifteenJSimplex = contract5` of the cyclic-order intertwiners;
2. the sorted vertex `simpEIAux` as the contraction of the sorted-leg intertwiners (the overlap `nodeT` with the signs `nodeEta`);
3. the vertex written with projections indexed by vertices (antisymmetric `M_s(p, q)`), independent of the positions;
4. the sum over the tetrahedron labels of the complex as the network with the projectors `P_t` (incidence bijection, `Finset.prod_univ_sum`);
5. the covariance of the network under a relabelling, with the sign `(-1)^J` per reversed link of a 4-simplex;
6. the parity lemma above (a statement on closed complexes: `Σ_{s ∋ p, q} col (s ∖ {p, q})` is even when every tetrahedron has an even leg sum);
7. the assembly over the colourings and cutoffs and the closedness of the relabelled complex.

## Limits

Nothing of the route beyond item 1 (a file with a `sorry`, not gated) is proved yet; the parity lemma and the covariance are checked on paper and by the numerics, not in Lean. The source of the model (arXiv:0711.0146v2) fixes
no order or sign convention, so "independent of the vertex order" is a property of the definition above, which is the basis-free
contraction of the source's definition (`sf6b-source-vertex-order.md`).
