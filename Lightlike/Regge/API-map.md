# Regge calculus

## Abstract (Alpha)

This API formalizes Regge calculus, the discretisation of general relativity on triangulations
whose edges carry lengths, in three and four dimensions: dihedral angles computed from edge
lengths, deficit angles, the Regge action, Schläfli's identity, and the Regge equations as the
discrete vacuum Einstein equations. It also contains geodesics of a Riemannian metric in a chart
and the expansion of the squared geodesic distance, which relate edge lengths to a continuum
metric, and the recognition of triangulated discs.

## Content (Alpha)

The dihedral angles of a tetrahedron are computed from its six edge lengths, and this formula
agrees with Euclidean geometry for every tetrahedron in `ℝ³` [1]. Deficit angles and the Regge
action are defined on a triangulation with edge lengths {1} [2]. Deficit angles vanish for
triangulations embedded in `ℝ³` [3]. A test file shows that a wrong angle formula gives the wrong
deficits on a cube [4].

Schläfli's identity holds at every non-degenerate tetrahedron [5]. As a consequence, for
non-degenerate lengths the Regge action is stationary under variations that fix the boundary
lengths exactly when the deficit angle vanishes at every interior edge [6]. Triangulations
embedded in `ℝ³` solve these equations [7].

In four dimensions the dihedral angles of a 4-simplex are computed from its ten edge lengths and
agree with Euclidean geometry [8], deficit angles are defined at triangles [9], Schläfli's identity
holds [10], the Regge equations are the vanishing of the interior deficits [11], and flat
triangulations solve them [12]. The convergence of the Regge action to the Einstein–Hilbert action
under refinement is not yet formalized. [TODO]

For a Riemannian metric in a chart, geodesics exist locally and are unique, and the exponential
map satisfies `‖exp_x v − x − v‖ ≤ C‖v‖²` [13]. The squared geodesic distance has an explicit
expansion to fifth order in the displacement, uniformly on compact sets [14], and an expansion to
sixth order, in which the terms of odd order vanish about the midpoint of the two points [15].

A 2-complex with boundary is a disc in the combinatorial sense exactly when it is an intrinsic
triangulated disc [16].

## Lean References

1. Lightlike/Regge/Dihedral.lean - `Regge.dihedral_dist`
2. Lightlike/Regge/Complex.lean - `Regge.deficit`, `Regge.reggeAction`
3. Lightlike/Regge/Embedded.lean - `Regge.IsGeometric.deficit_eq_zero`
4. Lightlike/Regge/Tests.lean - `Regge.Tests.cube_exterior_fails`,
   `Regge.Tests.cube_faceAngle_fails`
5. Lightlike/Regge/Schlaefli.lean - `Regge.schlaefli`
6. Lightlike/Regge/ReggeEquations.lean - `Regge.reggeAction_stationary_iff`
7. Lightlike/Regge/FlatSolution.lean - `Regge.IsGeometric.reggeAction_stationary`
8. Lightlike/Regge/D4/Dihedral.lean - `Regge4.dihedral4_dist`
9. Lightlike/Regge/D4/Complex.lean - `Regge4.deficit4`
10. Lightlike/Regge/D4/Schlaefli.lean - `Regge4.schlaefli4`
11. Lightlike/Regge/D4/ReggeEquations.lean - `Regge4.reggeAction4_stationary_iff`
12. Lightlike/Regge/D4/FlatSolution.lean - `Regge4.IsGeometric4.reggeAction4_stationary`
13. Lightlike/Regge/Geodesic/Exp.lean - `Geodesic.exists_expMap`
14. Lightlike/Regge/Geodesic/DistExpansion.lean - `Geodesic.IsRiemMetric.dist_sq_expansion`,
    `Geodesic.IsRiemMetric.dist_sq_expansion_midpoint`
15. Lightlike/Regge/Geodesic/Sixth.lean - `Geodesic.IsRiemMetric.dist_sq_expansion6`,
    `Geodesic.IsRiemMetric.dist_sq_expansion_midpoint6`
16. Lightlike/Regge/Disc.lean - `Regge.isDisc2_iff_isSurfaceDisc`

## References

1. T. Regge, General relativity without coordinates, *Nuovo Cimento* 19 (1961) 558.
