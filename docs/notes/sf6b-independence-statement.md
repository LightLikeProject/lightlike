# SF6b: the EPRL state sum at γ = 1 is independent of the order of the vertices

Milestone: SF6b, item p2 (the independence of the state sum from the vertex order of the 4-simplices).

## What is the object

`amplitudeI 1 K cut` (`Lightlike/SpinFoam/EPRLStateSum/IntrinsicVertex.lean`): the sum over the triangle colourings `col ≤ cut` of the
face weights `Π_f (col f + 1)` times the sum over the sorted labels of the tetrahedra of the product of the vertices of the
4-simplices. The vertex of a 4-simplex is `simpEIAux (J, z) = Σ_l Π_a nodeI J a (z a) (l a) · (-1)^(triPart J) ampP J l`, with the node
matrices `nodeI` of the sorted legs of each tetrahedron and `ampP` the Ooguri vertex amplitude; the basis change `nodeT` between the
sorted and the cyclic channel carries the sign `nodeEta` of `fourJ_swap₁₂`, `fourJ_swap₃₄` and `fourJ_swapPairs`.

## The statement (proved)

For every closed 4-complex `K` on a linearly ordered vertex set `V`, every cutoff `cut` and every permutation `σ` of `V` (a reordering of
the vertices):

`amplitudeI 1 (relabelComplex K σ) (fun f => cut (f.map σ.symm)) = amplitudeI 1 K cut`

(`amplitudeI_one_relabel`, `Lightlike/SpinFoam/EPRLStateSum/RelabelAmplitude.lean`), where `relabelComplex K σ` has the 4-simplices `σ s`.
For `∂Δ⁵` and any permutation `σ` of `Fin 6` the complex is mapped to itself and the statement reads
`amplitudeI 1 sphere6 (fun f => cut (f.map σ.toEmbedding)) = amplitudeI 1 sphere6 cut`; the bone cutoff of every edge gives `5`
(`amplitudeI_sphere6_relabel`). Equivalently, the amplitude is the same for every linear order on the vertex set. The per-colouring form:
the network `Znet K col` of a colouring is unchanged by the relabelling of the colouring (`Znet_relabel_eq`).

Variant with the form `ε` on the legs: gluing the tetrahedron by the pairing of an intertwiner with its dual through `ε` instead of the
identity multiplies the summand by `epsSign K col = Π_t (-1)^(J_t / 2)` with `J_t` the sum of the four leg colours (`fourJ_neg`), a function of
the colouring only; the state sum `amplitudeIeps` with this sign is independent of the vertex order too (`amplitudeIeps_relabel`).

At `γ = 1` the amplitude is the Ooguri state sum on the same complex and cutoffs, with no sign: `amplitudeI_one_eq_ooguriSum`. The sign
`linkSign = (-1)^(Σ_s triPart J_s)` of the link orientations is `1` on every colouring with even tetrahedron sums (`linkSign_of_tetPar`),
for every order of the vertices.

## Why it is true, and the proof

1. The corrected vertex is the contraction `contract5` of the five intertwiners of the sorted legs along the ten links of `K₅`, each link
   read with the form `edgeSign (J, m) = (-1)^((J - m)/2)` from its lower to its higher end (`simpEIAux_eq_contract5`).
2. The sum over the labels of the tetrahedra of a complex is a network: the sum over the projections of the links of the product of the
   edge weights and, for each tetrahedron, the sum over its label of the product of the node factors of its two incidences (`tetSum_network`).
3. Relabelling the vertices by `σ` permutes the positions in every 4-simplex (`phi`, from `posPerm`). The sum over the label of a tetrahedron
   is the projector onto the invariants of its four legs, which does not depend on the order of the legs (`sum_fourJT_mul_perm`,
   `kernel_relabel`); the links `{p, q}` that `σ` inverts are reversed, and reversing a link multiplies the contraction by `(-1)^J`
   (`edgeSign_neg`, on the parity support): `Znet_relabel` gives the sign `(-1)^e` with `e = Σ_s invSum J_s φ_s`, the number of reversed links
   counted with the colours (`contract5_perm`, `edgeW_perm`, `invSum_eq`).
4. The exponent is even on a closed complex: it is `Σ_{{x, y} inverted by σ} Σ_{s ∋ x, y} col (s ∖ {x, y})`, and the triangles `s ∖ {x, y}`
   form the link of the edge `{x, y}`. The sum over the tetrahedra `s ∖ {y}` of their four leg colours is even (tetrahedron parity) and
   counts the triangle of every `s` once and every other triangle twice, since every tetrahedron of a closed complex lies in two 4-simplices
   (`link_sum_even`, `invSum_total_even`). A colouring with an odd tetrahedron has no invariant network (`Znet_eq_zero`), so the sign
   never matters (`Znet_relabel_eq`).
5. The sum over the colourings is carried by the bijection `c ↦ c ∘ σ⁻¹` of the colourings (`sum_colourings_relabel`), with the face weights
   permuted (`faceProd_relabel`).
6. `linkSign = 1`: modulo `2`, `triPart J` of a 4-simplex is the sum of the leg colours of the tetrahedra omitting the positions `2` and `3`
   plus the sum over its five tetrahedra of their legs `0` and `1` (`triPart_local`); the first two are even and the last counts every
   tetrahedron of a closed complex twice (`triPart_total_even`).

## Evidence

Numerical controls (MEASURED): `docs/notes/sf6b-basis-free-gluing.md` (the basis-free gluing on `∂Δ⁵`, 14 colourings (colours up to 2) × 4
relabellings: the ratio of the summand is `1` to `3e-15`; the bone cutoff of each of the fifteen edges is `5`). These are controls of the
definitions, not proofs; the proofs are the Lean theorems above, with the standard axioms only (`#print axioms`).

## Limits

- The statement is for closed 4-complexes (every tetrahedron in exactly two 4-simplices), the hypothesis `IsClosed4`; a 4-complex with
  boundary is not covered.
- The source of the model (arXiv:0711.0146v2) fixes no order or sign convention, so "independent of the vertex order" is a property of the
  definition above, which is the basis-free contraction of the source's definition (`sf6b-source-vertex-order.md`).
- `amplitudeIeps` is defined by the sign `epsSign`; the equality of the `ε`-glued network with this sign times the network is the statement of
  `fourJ_neg` for one tetrahedron, not a separate theorem on complexes.
