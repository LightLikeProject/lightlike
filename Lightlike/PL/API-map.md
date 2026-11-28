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
exactly when they are related by bistellar moves {2} [5], [69]. This is the formulation of Friedl and
Hannes, who state the theorem as "closed combinatorial n-manifolds are bistellar equivalent if and
only if they are stellar equivalent" and prove it without topology {3}. Newman's theorem
gives the version with PL homeomorphism in place of stellar equivalence: PL homeomorphic complexes
are stellar equivalent [21]. Combined with the stellar version, closed combinatorial manifolds are
PL homeomorphic exactly when they are related by bistellar moves, for complexes with the empty
face [22]. On a closed combinatorial `n`-manifold every bistellar move `κ(A, B)` has `#A + #B = n + 2`,
so it is a move of Lickorish's Definition 2.3 [72].

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
subdivisions of lower dimension [21]. Conversely a stellar subdivision is a PL homeomorphism of the
realisations, and so is any chain of subdivisions and welds {1} [55]. The Euler characteristic is
invariant under stellar equivalence, so complexes with different Euler characteristics are not stellar
equivalent, and, when both or neither contain the empty face, their realisations are not PL
homeomorphic [56] [21].

The 3-complexes of the Ponzano–Regge API generate simplicial complexes, and its closed
combinatorial 3-manifolds are closed combinatorial 3-manifolds in this sense [6]. Pachner's theorem holds for the 3- and 4-complexes given by their top simplices, with their moves, on copies with new vertices [68]. In dimension two, a connected graph with two
edges at every vertex is reached from the boundary of a triangle by subdividing edges, and so
generates a PL 1-sphere [54]; this identifies the vertex links of the closed surfaces of
the surface API as PL 1-spheres. The same
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

The inside of a polygon is the set of points off it with odd crossing parity, and the outside is the
set with even parity. Both are open, the inside is bounded and the outside is not, and if the
complement is the union of two connected sets, one of them unbounded, the other is the inside [25].
For a simple triangle the vertices are affinely independent, the carrier is the frontier of the
convex hull, and the inside is the interior of the convex hull [26].

A simple polygon with at least four vertices has an interior diagonal, a pair of non-neighbouring vertices whose open segment lies in the inside. Let `v` be the lexicographically smallest vertex (leftmost, ties broken by lowest). Its two edge vectors are not parallel, the left half-plane lies in the outside, and, since the parity differs between the two sectors at `v`, the points close to `v` inside the angle of the two edges lie in the inside [27]. A segment that leaves the open region where finitely many affine functions are positive meets its boundary, and a segment from a boundary point towards a point where a vanishing function is positive enters the region [28]. In the frame of the two neighbours `u`, `w` of `v`, no edge meets an open wedge at `v` that contains no vertex [29]. If a vertex other than `u`, `v`, `w` lies in the closed triangle `u v w`, the diagonal runs from `v` to the one nearest to `v`; otherwise it runs from `u` to `w` [30].

Cutting along such a diagonal gives two polygons, made of the edges from the vertex `0` to the vertex `b` and from `b` back to `0`, each closed by the diagonal. The ray crossing test does not depend on the direction of an edge, so the diagonal is counted twice and the parities of the two parts add up to that of the polygon [31]. Both parts are simple, the inside of the polygon is the union of their insides and the open diagonal, and the two insides are disjoint [31]. The proof uses that the outside of the polygon is connected, and needs no analysis of the sectors along the diagonal. By induction on the number of vertices, every simple polygon has a triangulation by triangles whose vertices are vertices of the polygon: the faces form a geometric complex whose underlying set is the closed region bounded by the polygon, and every edge of the polygon is a face {4} [32]. Such a polygon also has two ears, interior diagonals between the vertices `k` and `k + 2` with non-neighbouring `k`, by induction from the splitting: a triangle part has its ear at the diagonal, and a part with at least four vertices has two ears, of which at most one touches the diagonal [33]. Attaching a triangle on a new vertex along a boundary edge that lies in exactly one triangle of a complex gives a stellar equivalent complex: subdivide the edge at the new vertex and flip the edge from the new vertex to the opposite vertex [34]. Clipping an ear, the triangulation can be chosen so that every edge of the polygon lies in exactly one triangle, and then the complex is a PL ball {4} [35]. The induction also carries that every edge of the complex that is not an edge of the polygon lies in two triangles. A face whose link is a PL ball then lies in a single triangle, by the signed count of the link, and so the boundary of the complex, the faces inside a face with a ball for a link, is exactly the set of faces inside an edge of the polygon; its underlying set is the polygon [36]. This is the polygonal Schoenflies theorem: the closed region bounded by a simple closed polygon is the underlying set of a geometric complex that is a PL ball whose boundary is the polygon {4} [36].

A geometric complex is PL homeomorphic to its abstract realisation, by the linear map that sends the weights `x` to `∑ x v • v`: the faces are affinely independent and meet in common faces, which gives injectivity {1} [37]. A PL ball of dimension `n` is PL homeomorphic to the simplex on any `n + 1` vertices, since a permutation of the vertex type carries one vertex set to the other [38]. Composing with the stellar equivalence of the triangulated region of a polygon to a simplex, the closed region bounded by a simple closed polygon is PL homeomorphic to a triangle {4} [39]. The homeomorphism is not shown to map the polygon onto the boundary of the triangle.

A simple chain is a list of points in the plane whose consecutive segments meet only at shared vertices; simple chains glue and reverse, and the set of a chain is its union of segments [40]. The ray crossing parity of a chain is additive under gluing and, modulo 2, invariant under reversal, which links the parity of a polygon built from a list to that of its chains [41]. The carrier of a polygon made of two arcs is the union of the two arcs, the parity of a ray crossing jumps across an arc near its interior points, and the interior of a simple chain without its ends is preconnected [42]. If a simple closed polygon is made of two arcs, a chord joining an interior point of the first arc to an interior point of the second, with its ends removed and meeting the arcs only at those points, cannot lie on the same side of the polygon as a second chord joining the two ends: the proof compares the parities of the three theta pieces and needs no orientation [43] {5}. Take the six-cycle of a drawing of `K₃,₃` as a hexagon with three chords; each chord lies inside or outside the hexagon, so two of them lie on the same side, and after a rotation of the labels they are neighbouring chords, which is impossible [44]. Hence six points joined across two classes of three by nine simple polygonal arcs that meet only in their common endpoints do not exist [45]. A simple chain contains, in its set, a simple chain with the same first and last point [46], and a continuous arc is approximated, within any distance, by such a chain [47]. Trimming each arc outside small balls around the six points, approximating the trimmed pieces by chains and joining them to the points by straight segments gives a polygonal drawing from any drawing by continuous arcs, so there is none [48]. An arc is the image of an injective continuous map of the unit interval; arcs reverse, split at a point and glue, and two points of a connected open set of the plane are joined by a chain in the set [49] {5}. Taking a highest and a lowest point of a circle embedded in the plane, which splits it into two arcs, and joining the two arcs by a horizontal segment and by an outer polygonal arc, with an arc through the complement if it were connected, gives nine arcs of a drawing of `K₃,₃`; the complement of an embedded circle is therefore not connected, which is the weak Jordan theorem [50] {5}. That the complement has exactly two components with the circle as boundary of each is not proved. A connected compact set that contains both ends of an arc and lies near it is near every point of it, because the inverse of an arc is uniformly continuous [51]. With it a Jordan curve is approximated, within any distance and in both directions, by a simple closed polygon [52]. The complement of a Jordan curve has exactly one unbounded component and a bounded component whose frontier lies in the curve [53]; that it has exactly one bounded component is open, as it needs the Arc Theorem.

Further results of this area in the results catalogue:
A chain on a grating with boundary two vertices joins them [57]. A path in the complement of a compact
set gives a chain of a grating that avoids it [58]. A cycle on a grating bounds a 2-chain, and
Alexander's theorem [59]. Two compact sets meeting in one point do not separate two points that neither
separates [60]. An arc does not separate the plane [61]. Every component of the complement of a Jordan
curve has the whole curve as its frontier [62]. The index of a loop about a point, and the Theta Lemma
[63]. The index of a loop is constant along a path avoiding it, and zero for a loop in a half plane
[64]. Lemma 9.14 of the theta configuration of a Jordan curve [65]. The index of a triangle about an
interior point, and of loops about points outside them [66]. The Jordan curve theorem [67]. The geometric realisation of a finite simplicial complex is a geometric complex, its simplices being the convex hulls of affinely independent basis vectors [70]. A PL sphere is a closed combinatorial manifold, and the link of every nonempty face of a closed combinatorial manifold is stellar equivalent to the boundary of a simplex [71].

## Lean References

1. Lightlike/PL/Complex.lean - `PL.SComplex`, `PL.SComplex.link`, `PL.SComplex.star_eq_join`,
   `PL.SComplex.link_cone_apex`, `PL.SComplex.link_link`
2. Lightlike/PL/Stellar.lean - `PL.SComplex.starAt`, `PL.SComplex.weld`, `PL.SComplex.weld_starAt`,
   `PL.SComplex.starAt_weld`, `PL.SComplex.StellarEquiv`
3. Lightlike/PL/Bistellar.lean - `PL.SComplex.bistellar`, `PL.SComplex.StellarEquiv.bistellar`,
   `PL.SComplex.bistellar_bistellar`
4. Lightlike/PL/Manifold.lean - `PL.SComplex.IsPLSphere`, `PL.SComplex.IsPLBall`,
   `PL.SComplex.IsCombManifold`, `PL.SComplex.isPLSphere_boundary`, `PL.SComplex.isPLBall_simplex`
5. Lightlike/PL/PachnerMain.lean - `PL.SComplex.pachner`,
   `PL.SComplex.StellarEquivIn.bistellarEquivIn`
6. Lightlike/PL/Complex3.lean - `PL.ofComplex3`, `PL.isBistellar_move23`, `PL.isBistellar_move32`,
   `PL.isBistellar_move14`, `PL.isBistellar_move41`, `PL.isClosedCombManifold_ofComplex3`
7. Lightlike/PL/Complex4.lean - `PL.ofComplex4`, `PL.IsCombManifold4`, `PL.isBistellar_move4`,
   `PL.ofComplex4_move`, `PL.isMove_of_isBistellar`, `PL.isCombManifold4_move_iff`
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
    `PL.SComplex.not_plHomeomorphic_of_euler_ne`,
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
27. Lightlike/PL/PolygonDiagonal.lean - `PL.Polygon.exists_extreme`, `PL.Polygon.corner_cross_ne`,
    `PL.Polygon.carrier_near_vertex`, `PL.Polygon.left_subset_outside`,
    `PL.Polygon.inside_near_corner`
28. Lightlike/PL/WedgeChord.lean - `PL.exists_boundary_point`, `PL.exists_interior_point`
29. Lightlike/PL/PolygonWedge.lean - `PL.wl`, `PL.wm`, `PL.wf`, `PL.Polygon.edge_meet_cases`,
    `PL.Polygon.wedge_disjoint_carrier`
30. Lightlike/PL/PolygonDiagonal3.lean - `PL.Polygon.exists_uw_diagonal`,
    `PL.Polygon.exists_diagonal`
31. Lightlike/PL/PolygonSplit.lean - `PL.crossesRay_symm`, `PL.Polygon.left`, `PL.Polygon.right`,
    `PL.Polygon.parity_left_add_right`, `PL.Polygon.isSimple_left`, `PL.Polygon.isSimple_right`,
    `PL.Polygon.inside_split`, `PL.Polygon.exists_split`
32. Lightlike/PL/PolygonTriangulation.lean - `PL.Polygon.IsTriangulation`,
    `PL.Polygon.exists_triangulation`, `PL.SComplex.isGeom_closure_union`,
    `PL.Polygon.isTriangulation_triangle`, `PL.Polygon.isTriangulation_union`
33. Lightlike/PL/PolygonEars.lean - `PL.Polygon.Ear`, `PL.Polygon.TwoEars`,
    `PL.Polygon.two_ears`
34. Lightlike/PL/Attach.lean - `PL.SComplex.stellarEquivIn_closure_insert`
35. Lightlike/PL/PolygonBall.lean - `PL.Polygon.EdgeUnique`, `PL.Polygon.ball_step`,
    `PL.Polygon.exists_ball_triangulation`
36. Lightlike/PL/PolygonBoundary.lean - `PL.Polygon.link_mem_iff`, `PL.Polygon.signedCount_link`,
    `PL.Polygon.unique_triangle_of_ball`, `PL.Polygon.mem_bd_closure_iff`,
    `PL.Polygon.bd_space_eq_carrier`, `PL.Polygon.polygon_schoenflies`
37. Lightlike/PL/RealGeom.lean - `PL.SComplex.linearSum`, `PL.SComplex.bary_unique`,
    `PL.SComplex.isPLHomeo_real_geom`
38. Lightlike/PL/Relabel.lean - `PL.SComplex.PLHomeomorphic.simplex_relabel`,
    `PL.SComplex.PLHomeomorphic.of_isPLBallIn`
39. Lightlike/PL/PolygonPLHomeo.lean - `PL.Polygon.polygon_plHomeo_triangle`
40. Lightlike/PL/SimpleChain.lean - `PL.chainSet`, `PL.IsSimpleChain`, `PL.isSimpleChain_append`,
    `PL.isSimpleChain_reverse`
41. Lightlike/PL/Chain.lean - `PL.chainParity_append`, `PL.chainParity_reverse`,
    `PL.Polygon.ofList`, `PL.Polygon.parity_ofList`
42. Lightlike/PL/Theta.lean - `PL.carrier_two_arcs`, `PL.Polygon.near_two`
43. Lightlike/PL/Interlaced.lean - `PL.no_interlaced_chord`
44. Lightlike/PL/HexFalse.lean - `PL.Hex.false`
45. Lightlike/PL/K33.lean - `PL.PLDrawing`, `PL.no_PL_K33`
46. Lightlike/PL/LoopErase.lean - `PL.exists_simple_sub`
47. Lightlike/PL/ArcApprox.lean - `PL.exists_simple_chain_near`
48. Lightlike/PL/ContK33.lean - `PL.ContDrawing`, `PL.no_K33`
49. Lightlike/PL/ArcSet.lean - `PL.IsArc`, `PL.exists_chain_in_open`
50. Lightlike/PL/WeakJordanCircle.lean - `PL.weak_jordan`
51. Lightlike/PL/ArcDensity.lean - `PL.arc_density`, `PL.exists_inverse_modulus`
52. Lightlike/PL/PolygonApprox.lean - `PL.exists_two_chains`, `PL.exists_polygon_near`
53. Lightlike/PL/JordanComponents.lean - `PL.jordan_components`
54. Lightlike/PL/Cycle.lean - `PL.CycleGraph`, `PL.CycleGraph.isSphere1`,
    `PL.CycleGraph.isPLSphere`, `PL.isPLSphere_closure_of_isSphere1`
55. Lightlike/PL/StellarHomeo.lean - `PL.SComplex.PLHomeomorphic.starAt`,
    `PL.SComplex.PLHomeomorphic.of_stellarEquivIn`,
    `PL.SComplex.PLHomeomorphic.of_stellarEquiv`
56. Lightlike/PL/Euler.lean - `PL.SComplex.StellarEquiv.euler_eq`,
    `PL.SComplex.not_stellarEquiv_of_euler_ne`
57. Lightlike/PL/Grating.lean - `PL.Grating`, `PL.Grating.bdy`, `PL.Grating.bdy_symmDiff`,
    `PL.Grating.reach_of_bdy`, `PL.Grating.joinedIn_of_bdy`
58. Lightlike/PL/GratingPath.lean - `PL.Grating.exists_grating`, `PL.Grating.exists_chain_box`,
    `PL.Grating.exists_chain_of_joinedIn`
59. Lightlike/PL/Alexander.lean - `PL.Grating.bdy₂`, `PL.Grating.bdy_bdy₂`, `PL.Grating.alexander`,
    `PL.Grating.exists_bdy₂`
60. Lightlike/PL/UnionLemma.lean - `PL.joinedIn_union_compl`
61. Lightlike/PL/ArcNotSeparating.lean - `PL.arc_not_separating`
62. Lightlike/PL/JordanFrontier.lean - `PL.jordan_frontier`
63. Lightlike/PL/Index.lean - `PL.exists_isLog`, `PL.logInc`, `PL.logInc_trans`, `PL.loopIndex`,
    `PL.theta_lemma`
64. Lightlike/PL/IndexConstancy.lean - `PL.loopIndex_eq_of_joinedIn`,
    `PL.loopIndex_eq_zero_of_halfplane`
65. Lightlike/PL/IndexTheta.lean - `PL.Theta`, `PL.Theta.lemma_9_14`, `PL.theta_arc`,
    `PL.joinedIn_compl_range`
66. Lightlike/PL/IndexTriangle.lean - `PL.logInc_segPath`, `PL.triangle_log_sum`,
    `PL.loopIndex_triangle`, `PL.loopIndex_eq_zero_of_above`, `PL.loopIndex_eq_zero_of_below`,
    `PL.loopIndex_eq_zero_of_far`
67. Lightlike/PL/JordanCurve.lean - `PL.jordan_at_most_two`, `PL.jordan_at_most_two_prod`,
    `PL.jordan_curve_theorem`
68. Lightlike/PL/PachnerMoves.lean - `PL.pachner3`, `PL.pachner4`
69. Lightlike/PL/Pachner.lean - `PL.SComplex.BistellarEquiv.stellarEquiv`
70. Lightlike/PL/Realisation.lean - `PL.SComplex.isGeom_real`
71. Lightlike/PL/Links.lean - `PL.SComplex.IsPLSphere.isClosedCombManifold`,
    `PL.SComplex.IsClosedCombManifold.link_face`
72. Lightlike/PL/MoveDimension.lean - `PL.SComplex.IsClosedCombManifold.card_add_card_of_isBistellar`

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
