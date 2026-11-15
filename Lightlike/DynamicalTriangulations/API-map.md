# Dynamical triangulations: Dehn–Sommerville relations

## Abstract (Alpha)

This API proves the Dehn–Sommerville relations of closed combinatorial manifolds, which cut the
face numbers of a triangulation in dimension 4 down to two independent ones. It proves that a face
with `n` vertices lies in exactly two top faces, that twice the number of faces with `n` vertices is
`n + 1` times the number of top faces, and that for a closed combinatorial 4-manifold
`2N₃ = 5N₄` and `2N₁ − 3N₂ + 6N₃ − 10N₄ = 0`. The boundary of the 5-simplex satisfies them with
`N = (6, 15, 20, 15, 6)`, and two 4-simplices glued along a tetrahedron violate the first.

## Content (Alpha)

The relations are the combinatorial input of four-dimensional dynamical triangulations {1} {2}
{3}: a triangulation of a closed 4-manifold has `N₀, …, N₄` vertices, edges, triangles,
tetrahedra and 4-simplices, and the relations leave `N₀` and `N₄` free once the Euler
characteristic is fixed. In this library `N_k` is the number of faces with `k + 1` vertices of a
complex in `Lightlike.PL`.

The proof follows the standard route. A face with `n` vertices of a closed combinatorial
`n`-manifold has a link that is a PL 0-sphere, which has two vertices; so it lies in exactly two
top faces. Counting the pairs (face with `n` vertices, top face containing it) both ways gives
`2N_{n-1} = (n + 1) N_n`. The link of a vertex is a PL 3-sphere, whose Euler characteristic is 0;
summing this over the vertices, each face of `K` is counted once per vertex, which gives
`2N₁ − 3N₂ + 4N₃ − 5N₄ = 0`, and with `2N₃ = 5N₄` the second relation follows [1].

The checks are the boundary of the 5-simplex, a closed combinatorial 4-manifold with
`N = (6, 15, 20, 15, 6)` computed by the kernel, and the complex of two 4-simplices glued along a
tetrahedron, which is not a manifold and does not satisfy `2N₃ = 5N₄` [5].

The Einstein–Regge action of a triangulation is `−κ₂N₂ + κ₄N₄`. With `N₂ = 2N₀ + 2N₄ − 2χ`, which
follows from the relations above, it equals `−2κ₂N₀ + (κ₄ − 2κ₂)N₄ + 2κ₂χ`, so for fixed `χ` it
depends only on `N₀` and `N₄`. The 2-4, 3-3 and 4-2 moves keep `N₀` and change the action by
`(#σ − #τ)(κ₄ − 2κ₂)`, so the 3-3 move leaves it unchanged; the 1-5 move adds a vertex
and four 4-simplices and changes it by `−2κ₂ + 4(κ₄ − 2κ₂)`; the sphere check gives
`−20κ₂ + 6κ₄`, while dropping `χ` gives `−24κ₂ + 6κ₄` [2] [5].

A triangulation is layered by a time function on the vertices when every 4-simplex spans two
consecutive times, as in causal dynamical triangulations {1} {3}. A tetrahedron is spacelike when
all its vertices have one time. A layered 4-simplex has at most one spacelike tetrahedron, and
every spacelike tetrahedron of a closed combinatorial manifold lies in two 4-simplices, so twice
the number of spacelike tetrahedra is the number of 4-simplices of type (4,1) or (1,4) [3] [5].

The Monte Carlo of dynamical triangulations is ergodic if the five Pachner moves connect all
triangulations of a manifold. A bistellar move `κ(A, B)` of a closed combinatorial 4-manifold has
`#A + #B = 6`, because the link of `A` is a sphere of dimension `4 − #A` and equals `∂B`; so it is
one of the five 4D moves. Pachner's theorem for the generated simplicial complexes therefore gives
that stellar equivalent closed combinatorial 4-manifolds are connected by a chain of moves and
inverse moves [4]. A single move is a step of the PL layer, and the statement is Pachner's theorem
of the PL layer [6] for every closed combinatorial 4-manifold, including the empty one. Lifting the
complexes to the vertex type `V ⊕ ℕ`, which has unlimited new vertices, removes the assumption of an
infinite vertex type: for every `V`, the lifts of two closed combinatorial 4-manifolds are connected
by moves iff the generated complexes are stellar equivalent. The Euler characteristic is invariant
along such chains, so the chain connects only triangulations of one `χ`; the move from a 4-simplex
to a subdivision with a new vertex gives a connected pair, and a single 4-simplex is not connected
to the boundary of the 5-simplex [5].

In three dimensions the same method gives the relations of closed combinatorial 3-manifolds given
by their tetrahedra [7]. Every triangle lies in two tetrahedra, so `N₂ = 2N₃`, and the vertex links
are PL 2-spheres of Euler characteristic 2, so `2N₁ − 3N₂ + 4N₃ = 2N₀` and `N₁ = N₀ + N₃`; the
Euler characteristic `N₀ − N₁ + N₂ − N₃` vanishes. The action of equilateral tetrahedra is
`−κ₁N₁ + κ₃N₃`, which equals `−κ₁N₀ + (κ₃ − κ₁)N₃` for a closed manifold [8] {4}. It changes by `κ₃ − κ₁`
under the 2-3 move, by `κ₁ − κ₃` under the 3-2 move, by `3κ₃ − 4κ₁` under the 1-4 move and by
`4κ₁ − 3κ₃` under the 4-1 move [8]. Pachner's theorem of the PL layer [6] gives ergodicity: for a
nonempty closed combinatorial 3-manifold, the lifts of two triangulations to `V ⊕ ℕ` are connected
by 2-3, 3-2, 1-4 and 4-1 moves iff the generated complexes are stellar equivalent, and the moves keep
closed combinatorial 3-manifolds [9]. The boundary of the 4-simplex has `N = (5, 10, 10, 5)`, and two
tetrahedra glued along a triangle violate `N₂ = 2N₃` [10].

## Lean References

1. Lightlike/DynamicalTriangulations/DehnSommerville.lean -
   `PL.SComplex.card_mul_eq_sum_cofaces`, `PL.SComplex.sum_card_link`,
   `PL.SComplex.IsClosedCombManifold.card_cofaces`,
   `PL.SComplex.IsClosedCombManifold.two_mul_card_eq`, `PL.SComplex.euler_eq_sum_card`,
   `PL.SComplex.IsClosedCombManifold.euler_link`,
   `PL.SComplex.IsClosedCombManifold.dehnSommerville_link`,
   `PL.SComplex.IsClosedCombManifold.dehnSommerville`
2. Lightlike/DynamicalTriangulations/Action.lean - `DynamicalTriangulations.dtAction`
   (the action), `PL.IsCombManifold4.card_triangles`,
   `DynamicalTriangulations.dtAction_eq`, `FourD.Complex4.card_faces_zero_move`,
   `DynamicalTriangulations.dtAction_move` (change under 2-4, 3-3 and 4-2 moves),
   `FourD.Complex4.card_faces_zero_move_one_five`, `DynamicalTriangulations.dtAction_move_one_five`
3. Lightlike/DynamicalTriangulations/Causal.lean - `DynamicalTriangulations.IsSpacelike`,
   `DynamicalTriangulations.IsLayered`, `DynamicalTriangulations.IsLayered.spatial_unique`,
   `DynamicalTriangulations.two_mul_card_spatial_tets`
4. Lightlike/DynamicalTriangulations/Ergodicity.lean - `DynamicalTriangulations.MoveEquiv`,
   `DynamicalTriangulations.IsCombManifold4In`,
   `DynamicalTriangulations.IsCombManifold4In.card_add_card`,
   `DynamicalTriangulations.isCombManifold4In_move_iff`,
   `DynamicalTriangulations.MoveEquiv.euler4_eq`,
   `DynamicalTriangulations.moveEquiv_of_bistellarEquivIn`,
   `DynamicalTriangulations.moveEquiv_iff_bistellarEquivIn`,
   `DynamicalTriangulations.moveEquiv_of_stellarEquivIn`, `FourD.Complex4.lift`,
   `DynamicalTriangulations.moveEquiv_lift_iff_stellarEquiv`
5. Lightlike/DynamicalTriangulations/Tests.lean -
   `DynamicalTriangulations.boundary_fin6_dehnSommerville`,
   `DynamicalTriangulations.twoSimplices_not_dehnSommerville`,
   `DynamicalTriangulations.twoSimplices_not_closedCombManifold`,
   `DynamicalTriangulations.dtAction_sphere`, `DynamicalTriangulations.layered_single`,
   `DynamicalTriangulations.not_layered_single`, `DynamicalTriangulations.sphere7_move`,
   `DynamicalTriangulations.sphere7_isCombManifold4`,
   `DynamicalTriangulations.simplex_not_moveEquiv_sphere`,
   `DynamicalTriangulations.sphere7_lift_moveEquiv`,
   `DynamicalTriangulations.sphere7_dtAction_move`,
   `DynamicalTriangulations.dtAction_sphere_ne_without_euler`
6. Lightlike/PL/PachnerMoves.lean - `PL.Move4Step`, `PL.pachner4`, `PL.Move3Step`, `PL.pachner3`
7. Lightlike/DynamicalTriangulations/DehnSommerville3.lean -
   `PL.SComplex.IsClosedCombManifold.dehnSommerville3_link`,
   `PL.SComplex.IsClosedCombManifold.dehnSommerville3`, `PR.IsCombManifold.card_tris`,
   `PR.IsCombManifold.card_edges`, `PR.IsCombManifold.euler_eq_zero`
8. Lightlike/DynamicalTriangulations/Action3.lean - `DynamicalTriangulations.dtAction3`,
   `DynamicalTriangulations.dtAction3_eq`, `DynamicalTriangulations.card_tets_move23`,
   `DynamicalTriangulations.card_edges_move23`, `DynamicalTriangulations.dtAction3_move23`,
   `DynamicalTriangulations.dtAction3_move32`, `DynamicalTriangulations.card_tets_move14`,
   `DynamicalTriangulations.card_edges_move14`, `DynamicalTriangulations.dtAction3_move14`,
   `DynamicalTriangulations.dtAction3_move41`
9. Lightlike/DynamicalTriangulations/Ergodicity3.lean - `DynamicalTriangulations.MoveEquiv3`,
   `DynamicalTriangulations.MoveEquiv3.isCombManifold_iff`,
   `DynamicalTriangulations.moveEquiv3_lift_iff_stellarEquiv`
10. Lightlike/DynamicalTriangulations/Tests3.lean - `DynamicalTriangulations.S3_counts`,
    `DynamicalTriangulations.dtAction3_S3`, `DynamicalTriangulations.dtAction3_S3_14`,
    `DynamicalTriangulations.twoTets_not_dehnSommerville`,
    `DynamicalTriangulations.twoTets_not_isCombManifold`

## References

1. J. Ambjørn, J. Jurkiewicz, R. Loll, Dynamically triangulating Lorentzian quantum gravity,
   *Nucl. Phys. B* 610 (2001) 347.
2. J. Ambjørn, B. Durhuus, T. Jónsson, *Quantum Geometry: A Statistical Field Theory Approach*,
   Cambridge University Press (1997).
3. R. Loll, Quantum gravity from causal dynamical triangulations: a review, *Class. Quantum
   Grav.* 37 (2020) 013002.
4. J. Ambjørn, J. Jurkiewicz, R. Loll, Non-perturbative 3d Lorentzian quantum gravity,
   *Phys. Rev. D* 64 (2001) 044011.
