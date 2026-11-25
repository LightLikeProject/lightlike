# Spin(4), its representations and the EPRL map

## Abstract (Alpha)

This API treats Spin(4) = SU(2) × SU(2) as the double cover of SO(4) and as the spin group of a
Clifford algebra, classifies its unitary irreducible representations, and builds on them the
kinematics of the Euclidean EPRL spin foam model: the EPRL map for Barbero–Immirzi parameter
`0 < γ < 1`, the simplicity constraints, the fusion coefficients, and coherent states and coherent
intertwiners.

## Content (Alpha)

Spin(4) acts on the quaternions by left and right multiplication, which gives a surjective
homomorphism onto SO(4) [1] whose kernel is `{(1, 1), (−1, −1)}` [1]. This map is a covering map
[1]. The spin group of the Clifford algebra of four-dimensional Euclidean space, as defined in
Mathlib, is isomorphic to Spin(4) [2].

The representation with labels `(j₊, j₋)` is the tensor product of two SU(2) spin
representations. It is unitary, irreducible, and of dimension `(2j₊+1)(2j₋+1)` [3], and every
continuous irreducible finite-dimensional representation of Spin(4) is equivalent to one of them
[4]. Restricted to the diagonal SU(2), it decomposes by the Clebsch–Gordan rule [5].

For `0 < γ < 1` the EPRL map embeds the SU(2) spin `j` into the Spin(4) representation with
`j± = |1 ± γ| j / 2` as its highest diagonal spin {1}. It is equivariant and isometric [6]. Its
image satisfies the linear simplicity constraint weakly [6], only EPRL labels have this property
[6], and the constraint does not hold strongly [6]. The fusion coefficients factor through the
EPRL recoupling coefficients [7]. On intertwiners the map is injective exactly when the sum of the
doubled spins is even or there are no SU(2) intertwiners {2} [7].

SU(2) and Spin(4) coherent states resolve the identity, and the EPRL map sends an SU(2) coherent
state to a Spin(4) coherent state, and the overlaps of coherent states are powers of a matrix entry [8].
Coherent intertwiners are defined by group averaging {3}, which is an orthogonal projection, and they have an
overlap formula and a resolution of the identity, for SU(2) and for Spin(4) [9]. For two links their norm is given by the normals [10], and at any valence, normals that do
not close are exponentially suppressed as the spins grow [11].

The Euclidean EPRL vertex amplitude, for `γ < 1`, is the contraction along the 4-simplex of the
five node tensors, each the image of an SU(2) intertwiner under the EPRL map {1} [12]. It is a sum
over the Spin(4) intertwiner labels of products of fusion coefficients and two SU(2) 15j symbols,
one self-dual and one anti-self-dual, which is the spin-network form of {1} [12]; the fusion
coefficients are also written as products of two 9j symbols [12]. The vertex vanishes unless the
self-dual and the anti-self-dual spins add up to even numbers at every node, it is `1` at spin zero,
it is real, and with trivial anti-self-dual spins it is the SU(2) 15j symbol of BF theory [12].
Exact values at small spins are checked, and a wrong simplicity constraint gives a different value
[13]. The large-spin asymptotics of the coherent vertex integral are in the asymptotics API, but
equality of that integral with this vertex is not yet formalized. [TODO]

## Lean References

1. Lightlike/Spin4/SO4.lean - `Spin4.toSO4`, `Spin4.toSO4_surjective`,
   `Spin4.toSO4_eq_one_iff`, `Spin4.isCoveringMap_toSO4Mat`
2. Lightlike/Spin4/Clifford.lean - `Spin4.spinEquiv`, `Spin4.spinGroup_conj_ι`
3. Lightlike/Spin4/Rep.lean - `Spin4.spin4Rep`, `Spin4.spin4Mat_mem_unitaryGroup`,
   `Spin4.spin4Representation_isIrreducible`, `Spin4.finrank_tensorSpace`
4. Lightlike/Spin4/Completeness.lean - `Spin4.spin4Rep_complete`
5. Lightlike/Spin4/ClebschGordan.lean - `Spin4.spin4_diag_clebschGordan`
6. Lightlike/Spin4/EPRL.lean - `Spin4.eprlMap`, `Spin4.eprlMap_equivariant`,
   `Spin4.eprlMap_isometry`, `Spin4.eprl_weak_simplicity`, `Spin4.weak_simplicity_iff`,
   `Spin4.eprl_not_strong_simplicity`
7. Lightlike/Spin4/Fusion.lean - `Spin4.fusion_eq`, `Spin4.eprlIntertwiner_injective_iff`
8. Lightlike/Spin4/Coherent.lean - `Spin4.cohState`, `Spin4.inner_cohState`, `Spin4.normSq_inner_cohState`,
   `Spin4.inner_cohState4`, `Spin4.resolution_cohState`, `Spin4.resolution_cohState4`,
   `Spin4.eprlMap_cohState`
9. Lightlike/Spin4/CoherentIntertwiner.lean - `Spin4.cohInt`, `Spin4.avgP_mul_avgP`,
   `Spin4.cohInt_isInvariantN`, `Spin4.inner_cohInt`, `Spin4.resolution_cohInt`,
   `Spin4.cohInt4_invariant`, `Spin4.inner_cohInt4`, `Spin4.resolution_cohInt4`
10. Lightlike/Spin4/CoherentTwoValent.lean - `Spin4.norm_sq_cohInt_two`
11. Lightlike/Spin4/CoherentSuppression.lean - `Spin4.normSq_cohInt_le_exp`,
    `Spin4.cohInt_suppressed`
12. Lightlike/Spin4/Vertex.lean - `Spin4.eprlNode`, `Spin4.eprlNode_eq_eprlIntertwiner`,
    `Spin4.eprlVertex`, `Spin4.eprlVertex_eq_sum`, `Spin4.eprlVertex_eq_fifteenJ`,
    `Spin4.eprlVertex_eq_vertexNineJ`, `Spin4.eprlVertex_eq_zero_of_not_even_left`,
    `Spin4.eprlVertex_eq_zero_of_not_even_right`, `Spin4.eprlVertex_zero`, `Spin4.eprlVertex_im`,
    `Spin4.eprlVertex_zero_right`
13. Lightlike/Spin4/VertexTests.lean - `Spin4.VertexTests.eprlVertex_cycle_selfDual`,
    `Spin4.VertexTests.eprlVertex_cycle_third`, `Spin4.VertexTests.vertexNineJ_wrong_simplicity`,
    `Spin4.VertexTests.eprlVertex_ne_wrong_simplicity`

## References

1. J. Engle, E. Livine, R. Pereira, C. Rovelli, LQG vertex with finite Immirzi parameter,
   *Nucl. Phys. B* 799 (2008) 136.
2. W. Kamiński, M. Kisielowski, J. Lewandowski, The kernel and the injectivity of the EPRL map,
   *Class. Quantum Grav.* 29 (2012) 085001, Theorem 2.
3. E. R. Livine, S. Speziale, A new spinfoam vertex for quantum gravity, *Phys. Rev. D* 76 (2007)
   084028.
