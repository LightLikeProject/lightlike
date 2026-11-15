# PL topology of simplicial complexes

## Abstract (Alpha)

This API develops piecewise-linear topology for finite abstract simplicial complexes in every
dimension, in the stellar setting of Lickorish: links, stars, joins and cones, stellar
subdivisions and welds, bistellar moves, PL spheres and balls, and combinatorial manifolds. Its
main result is Pachner's theorem in stellar form, which is what makes state sums that are
invariant under bistellar moves into invariants of combinatorial manifolds.

## Content (Alpha)

A simplicial complex is a finite family of finite vertex sets closed under taking subsets [1]. The
link of a face is defined as usual, and the star of a face is the join of the face with its link
[1]. A stellar subdivision inserts a new vertex in a face, a weld is its inverse, and stellar
equivalence is the equivalence relation they generate {1} [2]. A bistellar move replaces the star
`A * ∂B` of a face `A` by `∂A * B`, and every bistellar move is a stellar equivalence [3].

A PL sphere is a complex stellar equivalent to the boundary of a simplex, a PL ball is one stellar
equivalent to a simplex, and a combinatorial manifold is a complex whose vertex links are PL
spheres or balls [4]. The boundary of a simplex is a PL sphere and a simplex is a PL ball [4].

Pachner's theorem, stellar version: two closed combinatorial manifolds are stellar equivalent
exactly when they are related by bistellar moves {2} [5]. This is the formulation of Friedl and
Hannes, who state the theorem as "closed combinatorial n-manifolds are bistellar equivalent if and
only if they are stellar equivalent" and prove it without topology {3}. Newman's theorem
gives the version with PL homeomorphism in place of stellar equivalence: PL homeomorphic complexes
are stellar equivalent [21]. Combined with the stellar version, closed combinatorial manifolds are
PL homeomorphic exactly when they are related by bistellar moves, for complexes with the empty
face [22].

Towards Newman's theorem, the library slices a geometric complex by affine functionals into cells,
each with a closed part, an open part and a chosen interior point [8]. For a slicing, the closed
and open parts of a cell are polytopes, described by the barycentric coordinates of its simplex,
extended to affine functions on the whole space [16], and by the slicing functionals [9] [10]. The cells of a slicing refine the complex, so the slices
form a subdivision [11]. A radial projection from an interior point maps the boundary of a
polytope bijectively onto the boundary of a simplex [12] [13], and a subdivision of a simplex
boundary is made to fit the polytope by a gauge-compatible subdivision [14]. Together these show
that the boundary of a bounded polytope in an affine subspace is a stellar sphere, given that
subdivisions of lower dimension are stellar equivalent [15]. Applied to a cell, this makes its
derived boundary a stellar sphere of dimension at most that of the complex [17]. When a further
functional cuts a cell, the cells below each of its two new halves form such a sphere, which is
what the walk through the splitting needs [18]. Cutting by one functional after another, a geometric complex is stellar equivalent to its slicing by any finite family of functionals, given stellar equivalence of subdivisions of dimension one lower [19].
A geometric subdivision is cut out of the complex it subdivides by finitely many affine
functionals, for which the two slicings have the same cells as sets and hence isomorphic orders
[20]. With the slicing result this gives, by induction on the dimension, that every geometric
subdivision of a complex with the empty face is stellar equivalent to it [20], and from that
Newman's theorem [21]. With it, the sphere results above no longer assume stellar equivalence of
subdivisions of lower dimension [21].

The 3-complexes of the Ponzano–Regge API generate simplicial complexes, and its closed
combinatorial 3-manifolds are closed combinatorial 3-manifolds in this sense [6]. The same
construction applies to the 4-complexes of the four-dimensional API, with closed combinatorial
4-manifolds defined by their vertex links [7].

A closed polygon in the plane is a cyclic list of vertices, its edges are the segments between
consecutive vertices, and it is simple when edges are nondegenerate, non-consecutive edges are
disjoint, and consecutive edges meet only at their shared vertex [23]. The crossing parity of a
point off the polygon counts the edges met by the horizontal ray to its right, with a half-open
rule at the endpoints, and it is locally constant off the polygon [23]. The carrier of a polygon is
closed, nonempty and connected, and near each of its points it is one or two rays, which cut a
small disc into two sectors on which the parity differs [24]. Each parity class is therefore
connected, and the parity vanishes outside a ball containing the vertices. This gives the polygonal
Jordan curve theorem: the complement of a simple closed polygon is the disjoint union of two
nonempty, open, connected sets, one bounded and one unbounded, and the polygon is the frontier of each [24] {4} {5}.

## Lean References

1. Lightlike/PL/Complex.lean - `PL.SComplex`, `PL.SComplex.link`, `PL.SComplex.star_eq_join`
2. Lightlike/PL/Stellar.lean - `PL.SComplex.starAt`, `PL.SComplex.weld`,
   `PL.SComplex.StellarEquiv`
3. Lightlike/PL/Bistellar.lean - `PL.SComplex.bistellar`, `PL.SComplex.StellarEquiv.bistellar`
4. Lightlike/PL/Manifold.lean - `PL.SComplex.IsPLSphere`, `PL.SComplex.IsPLBall`,
   `PL.SComplex.IsCombManifold`, `PL.SComplex.isPLSphere_boundary`, `PL.SComplex.isPLBall_simplex`
5. Lightlike/PL/PachnerMain.lean - `PL.SComplex.pachner`
6. Lightlike/PL/Complex3.lean - `PL.ofComplex3`, `PL.isClosedCombManifold_ofComplex3`
7. Lightlike/PL/Complex4.lean - `PL.ofComplex4`, `PL.IsCombManifold4`
8. Lightlike/PL/CellGeom.lean - `PL.CellStructure`, `PL.CellStructure.pt_injOn`
9. Lightlike/PL/SliceGeom.lean - `PL.SComplex.sliceStructure`, `PL.SComplex.sliceHull`
10. Lightlike/PL/CellPolytope.lean - `PL.SComplex.sliceHull_eq`, `PL.SComplex.cellSet_eq`,
    `PL.SComplex.exists_facet`
11. Lightlike/PL/SliceSubdiv.lean - `PL.SComplex.isSubdivision_slice`
12. Lightlike/PL/RadialBoundary.lean - `PL.SComplex.isSB_of_radial`
13. Lightlike/PL/RadialPolytope.lean - `PL.SComplex.projMap_image_boundary`,
    `PL.SComplex.injOn_projMap_boundary`
14. Lightlike/PL/RadialGauge.lean - `PL.SComplex.exists_gauge_subdivision`
15. Lightlike/PL/RadialCell.lean - `PL.SComplex.isSB_of_polytope_boundary`,
    `PL.SComplex.exists_refSimplex`
16. Lightlike/PL/Barycentric.lean - `PL.exists_barycentric`
17. Lightlike/PL/RadialSphere.lean - `PL.SComplex.derivedBoundary_isSphere`
18. Lightlike/PL/CutSpheres.lean - `PL.SComplex.cutSpheres`, `PL.SComplex.isSB_map'`
19. Lightlike/PL/SliceStellar.lean - `PL.SComplex.SliceEq`, `PL.SComplex.sliceEq_ext`,
    `PL.SComplex.stellarEquiv_slice`
20. Lightlike/PL/SubdivCells.lean - `PL.SComplex.exists_cutting`,
    `PL.SComplex.cell_le_iff_segments`, `PL.SComplex.stellarEquiv_of_cutting`,
    `PL.SComplex.subdivStellar`
21. Lightlike/PL/Newman.lean - `PL.SComplex.StellarEquiv.of_plHomeomorphic`,
    `PL.SComplex.derivedBoundary_isSphere_of_infinite`, `PL.SComplex.cutSpheres_of_infinite`,
    `PL.SComplex.isSB_of_polytope_boundary_of_infinite`
22. Lightlike/PL/PachnerPL.lean - `PL.SComplex.pachner_plHomeomorphic`,
    `PL.SComplex.isClosedCombManifold_iff_plHomeomorphic`
23. Lightlike/PL/Polygon.lean - `PL.Polygon`, `PL.Polygon.edge`, `PL.Polygon.carrier`,
    `PL.Polygon.IsSimple`, `PL.Polygon.three_le_of_isSimple`, `PL.Polygon.parity`, `PL.Polygon.eventually_parity_eq`
24. Lightlike/PL/PolygonJordan.lean - `PL.Polygon.isClosed_carrier`,
    `PL.Polygon.isPreconnected_carrier`, `PL.Polygon.local_data`, `PL.Polygon.exists_sectors`,
    `PL.Polygon.isPreconnected_parity_class`, `PL.Polygon.parity_eq_zero_far`,
    `PL.Polygon.polygon_jordan`, `PL.Polygon.carrier_subset_closure_class`,
    `PL.Polygon.frontier_class`
25. Lightlike/PL/PolygonInside.lean - `PL.Polygon.inside`, `PL.Polygon.outside`,
    `PL.Polygon.isBounded_inside`, `PL.Polygon.not_isBounded_outside`,
    `PL.Polygon.eq_inside_of_isBounded`
26. Lightlike/PL/PolygonTriangle.lean - `PL.Polygon.affineIndependent_of_isSimple`,
    `PL.Polygon.carrier_eq_frontier_hull`, `PL.Polygon.inside_eq_interior_hull`

## References

1. W. B. R. Lickorish, Simplicial moves on complexes and manifolds, *Geom. Topol. Monogr.* 2 (1999)
   299.
2. U. Pachner, P.L. homeomorphic manifolds are equivalent by elementary shellings,
   *European J. Combin.* 12 (1991) 129.
3. S. Friedl and J. Hannes, Pachner's theorem, in *MATRIX Annals 2021–22*, MATRIX Book Series,
   Springer (2024).
4. E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Graduate Texts in Mathematics 47,
   Springer (1977).
5. C. Thomassen, The Jordan–Schönflies theorem and the classification of surfaces,
   *Amer. Math. Monthly* 99 (1992) 116.
