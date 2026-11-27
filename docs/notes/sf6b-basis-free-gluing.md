# SF6b: the basis-free gluing of the vertex amplitudes is independent of the vertex order, the library's gluing is not

Milestone: SF6b, item p2 (the dependence of the state sum on the vertex order).

## Question

The state sum at `γ = 1` glues the vertex amplitudes of two 4-simplices at a shared tetrahedron by a sum over an intertwiner
basis of the tetrahedron. Summed over an orthonormal basis `Σ_z ι_z ⊗ ι_z` is the projector onto the invariants of the legs,
independent of the basis and of any numbering of the vertices; only the orientation of the links can enter. Is the library's
gluing (`amplitudeI`, sorted labels, transition matrices `nodeT`) this contraction? If it is not, is the contraction itself
independent of the vertex order?

## Method

`scripts/spinfoam/eprl_free_gluing_check.py` computes, on the boundary of the 5-simplex, for a fixed colouring of the triangles
by spins (face weights `Π_f (J_f + 1)` times the sum over the tetrahedron labels), two state sums:

- the library gluing: the intrinsic vertex of `IntrinsicVertex.lean` (15j with positional labels, rewritten in the sorted
  basis of each tetrahedron by `nodeT`), the same sorted label in the two adjacent vertices;
- the basis-free gluing: the node tensor of a tetrahedron is the intertwiner of its legs in the sorted order of the legs (the
  same tensor from both adjacent 4-simplices), the five nodes of a vertex are contracted along the ten links with the
  bilinear form `ε(m, m') = (-1)^((j - m)/2) δ_{m', -m}` (the first end of a link is the lower position), and the labels of a
  tetrahedron are summed.

14 random admissible colourings (colours 0 and 1, and a colour 2 on some; the fixed seed of the script) and 4 random relabellings of the
six vertices each; the ratio of the summand after and before the relabelling (`--full` run of the script).

## Results (MEASURED, numerical, not a proof)

- Basis-free gluing: the ratio is `1.0000` for all 56 (colouring, relabelling) pairs, including the colourings with a colour 2;
  the maximal deviation from `1` is `2.7e-15` (floating point; the script checks `< 1e-6`). Not even a sign changes. (`--full` run of the script; the default run is a subset.)
- Library gluing: the ratio is `±1` for 7 of the 14 colourings (those with colours `≤ 1`) and not `±1` for the other 7
  (`0.5`, `-0.5`, `±2`, `0.2857`, `1.4286`, ...).
- Bone cutoff of each of the fifteen edges of the 5-simplex: basis-free amplitude `5.0` for all fifteen edges; library
  amplitude `5.0` or `-3.0` (`w - u` odd or even), as in `sf6b-order-dependence.md`.
- On one fixed ordering (the identity order), the library summand and the basis-free summand of the 14 colourings agree for 6
  colourings, are opposite for 3, and differ in magnitude for 5 (library `-8`, free `16`; library `37.33`, free `53.33`): they
  differ already on a fixed order, so the library's gluing is not the basis-free contraction. The difference is a sign for
  spins `≤ 1/2` and a change of magnitude when a tetrahedron has legs of spin `1` (an intertwiner space of dimension `> 1`).

## Reading

The order dependence of the library's amplitude comes from its gluing at the tetrahedra (the transition matrix `nodeT` from the
sorted to the positional channel does not map the sorted basis vectors to the same vectors from both adjacent simplices), not
from the vertex amplitude, the face amplitude or the link orientation. Where exactly `nodeT` differs from the overlap of the two
orthonormal bases of the invariant space is not decided here; the numerics only show that replacing the node tensors by the
sorted-leg intertwiners removes the dependence, for the 14 colourings and 15 bone cutoffs tried.

## Limits

- Numerical evidence on one complex (`∂Δ⁵`), 14 colourings and 4 relabellings each, spin `≤ 1` (one colour `2`); not a proof.
- The basis-free gluing defined here pairs the same tensor on both sides; the pairing with the form `ε` on the legs changes the
  result by the sign `(-1)^(Σ_t J_t / 2)`, a function of the colouring only (`fourJ_neg`).
- The comparison with the source (arXiv:0711.0146v2, p. 5, Eqs. (31)-(34)) cannot decide the convention: the paper does not state
  one (`sf6b-source-vertex-order.md`).
