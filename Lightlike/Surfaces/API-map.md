# Closed triangulated surfaces

## Abstract (Alpha)

This API classifies closed combinatorial surfaces up to 2D bistellar moves. Every closed
triangulated surface is related by moves to exactly one standard model, a sphere with handles or a
connected sum of projective planes, and the model is determined by orientability and the Euler
characteristic. This is the two-dimensional case of the statement that bistellar moves generate
PL homeomorphism. It makes a state sum that is invariant under 2D moves into a function of the
genus and orientability alone.

## Content (Alpha)

A closed surface is a finite set of triangles in which every edge lies in two triangles, every
vertex link is a connected cycle and the 1-skeleton is connected; bistellar moves preserve it,
orientability and the Euler characteristic [1]. Vertex links of a closed surface are cycles, so a
vertex of degree three is either the boundary of a tetrahedron or can be removed, and an edge at
a vertex can be flipped whenever its far side is not already an edge [2]. Contracting an edge at
a vertex of degree three is a sequence of moves [3]. Chains of moves inside a larger complex are
checked by computation on a small labelled region and transported by an embedding [4]. Mod-2
homology bounds the Euler characteristic of a closed surface by two {1} [5].

The connected sum glues two surfaces along a triangle; it adds Euler characteristics minus two
and is orientable exactly when both summands are [6]. The pieces are the 6-vertex projective plane
and the 9-vertex torus, with their Euler characteristics and (non-)orientability [7]. The standard
models are iterated connected sums of these pieces at fixed sites, `stdModel true g` with `g`
handles and `stdModel false k` with `k + 1` crosscaps [8].

When no edge at a vertex can be flipped, the vertex link crosses itself and gives a closed curve
of three edges that bounds no triangle {2}. Arcs in vertex links [9] and splitting a vertex along
an arc [10] are the local steps; checked surgery replaces a region by a template and keeps the
surface closed [11]. Cutting along a non-facial 3-cycle removes a tube or a Möbius band and caps
the holes, raising the Euler characteristic by two or by one [12].

A connected sum with a good piece does not depend on the gluing triangle up to moves: the piece
can be moved to an adjacent triangle, and hence along a path in the dual graph, which is
connected [13] [14]; both pieces are good [15] and moves of the surface lift to moves of the sum
[16]. Checked flip chains move a tube one layer and close it [17]. A cut
along a two-sided curve splits off a torus or Klein bottle summand, and a cut along a one-sided
curve a projective plane; the Klein bottle is two projective planes [18].

The main theorem: every closed surface is related by moves to a standard model, and conversely
everything related to a standard model is a closed surface {3} [19]. Dyck's relation, a torus
plus a projective plane is three projective planes, turns torus summands on a non-orientable
surface into crosscaps {4} [19]. The model is unique, and it exists exactly when orientability and
the Euler characteristic match [19]. Kernel-checked surface certificates give the known values for
the projective plane, the 9-vertex torus and Möbius' independent 7-vertex torus {5}, and wrong
models (the Klein bottle and the sphere for a torus) and wrong inputs (a single triangle, two
disjoint spheres) are rejected [20].

The classification up to PL homeomorphism of the underlying spaces, rather than up to moves,
needs the identification of moves with PL homeomorphism in dimension two, which is not formalized
here. [TODO]

## Lean References

1. Lightlike/Surfaces/Basic.lean - `Surfaces.IsSurface`, `Surfaces.IsOrientable`,
   `Surfaces.isSurface_iff_of_eqvGen`, `Surfaces.isOrientable_iff_of_eqvGen`,
   `Surfaces.euler2_eq_of_eqvGen`
2. Lightlike/Surfaces/Local.lean - `Surfaces.IsSurface.eq_bdry`,
   `Surfaces.IsSurface.remove_deg3`, `Surfaces.IsSurface.flip_lowers`
3. Lightlike/Surfaces/Contract.lean - `Surfaces.IsSurface.contract_eqvGen`
4. Lightlike/Surfaces/Check.lean - `Surfaces.checkChain`, `Surfaces.liftK`,
   `Surfaces.checkChain_sound`
5. Lightlike/Surfaces/Homology.lean - `Surfaces.IsSurface.euler_le`
6. Lightlike/Surfaces/Sum.lean - `Surfaces.csum`, `Surfaces.IsGlue`, `Surfaces.euler2_csum`,
   `Surfaces.isOrientable_csum`
7. Lightlike/Surfaces/Pieces.lean - `Surfaces.P6`, `Surfaces.T9`, `Surfaces.euler2_P6`,
   `Surfaces.euler2_T9`, `Surfaces.isOrientable_T9`, `Surfaces.not_isOrientable_of_P6`
8. Lightlike/Surfaces/Models.lean - `Surfaces.model`, `Surfaces.stdModel`,
   `Surfaces.euler2_stdModel_true`, `Surfaces.euler2_stdModel_false`,
   `Surfaces.isOrientable_stdModel`
9. Lightlike/Surfaces/Arc.lean - `Surfaces.IsSurface.exists_arc`
10. Lightlike/Surfaces/Split.lean - `Surfaces.splitV`, `Surfaces.IsSurface.split_steps`
11. Lightlike/Surfaces/Surgery.lean - `Surfaces.SurgCtx`, `Surfaces.IsSurface.surgery`,
    `Surfaces.SurgCtx.euler2_surg`
12. Lightlike/Surfaces/Cut.lean - `Surfaces.CutTo`, `Surfaces.IsSurface.cut`
13. Lightlike/Surfaces/Dual.lean - `Surfaces.IsSurface.dconn`,
    `Surfaces.IsSurface.exists_path_avoid`
14. Lightlike/Surfaces/Glue.lean - `Surfaces.GoodPiece`, `Surfaces.GoodPiece.step`,
    `Surfaces.GoodPiece.homog`
15. Lightlike/Surfaces/Slides.lean - `Surfaces.goodPiece_P6`, `Surfaces.goodPiece_T9`
16. Lightlike/Surfaces/Add.lean - `Surfaces.IsSurface.lift_move`, `Surfaces.GoodPiece.add`
17. Lightlike/Surfaces/Chains.lean - `Surfaces.chain_tslide`, `Surfaces.chain_layer`,
    `Surfaces.chain_cc`, `Surfaces.chain_dyck`
18. Lightlike/Surfaces/Tube.lean - `Surfaces.handle_of_cut`, `Surfaces.crosscap_of_cut`,
    `Surfaces.twist_of_KB`
19. Lightlike/Surfaces/Classify.lean - `Surfaces.classify`, `Surfaces.isSurface_iff_classify`,
    `Surfaces.dyck_step`, `Surfaces.classify_unique`, `Surfaces.exists_eqvGen_stdModel_iff`
20. Lightlike/Surfaces/Tests.lean - `Surfaces.isSurface_of_cert`, `Surfaces.T7`,
    `Surfaces.T7_model`, `Surfaces.T7_not_klein`, `Surfaces.torus_not_klein`,
    `Surfaces.two_spheres_no_model`

## References

1. A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002).
2. G. K. Francis and J. R. Weeks, Conway's ZIP proof, *Amer. Math. Monthly* 106 (1999) 393.
3. H. R. Brahana, Systems of circuits on two-dimensional manifolds, *Ann. of Math.* 23 (1921)
   144.
4. W. Dyck, Beiträge zur Analysis situs, *Math. Ann.* 32 (1888) 457.
5. F. H. Lutz, Triangulated manifolds with few vertices: Combinatorial manifolds,
   arXiv:math/0506372 (2005).
