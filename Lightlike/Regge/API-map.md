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
triangulations solve them [12].

In dimension 2, for a Riemannian metric on a region of the plane, the deficit angles of fat vertex
stars of bounded valence, with geodesic edge lengths and weighted by a Lipschitz function, differ
from the integral of the function against the Gauss curvature by at most a constant times the mesh
size [17]; Cheeger, Müller and Schrader prove convergence of the curvature in every dimension {2}.
The angle bound of the stars follows from fatness. For an explicit triangulation, given by vertex
positions and corner maps, the vertex cells are built from the triangles, and the same bound holds
against the integral over the triangles with all corners interior [18]. A 4×4 grid with four
interior vertices meets every hypothesis with an interior region of positive area, and a clockwise
star fails the fatness hypothesis [19]. The bound is stated for every Riemannian metric on the
plane [19]. For the flat metric its integral term is 0. The hyperbolic plane `dx² + e^{2x} dy²`
is a Riemannian metric with scalar curvature `-2`, computed from the library's curvature
definitions [25]; on the same grid the integral over the interior triangles is strictly
negative, and the bound holds [26]. The `n × n` grids of the unit square, with mesh `1/n`, form
a refining family: the hypotheses hold for every `n` with constants independent of `n`, so one
constant serves all `n`, and on the hyperbolic plane the integral term is at most `-1/4` for
`n ≥ 4` [27]. The round unit 2-sphere in the chart `(θ, φ)`, `dθ² + sin² θ dφ²` on the strip
`0 < θ < π`, is a Riemannian metric with scalar curvature `2`, and the curvature integral over the
chart cell `(0, π) × (0, 2π)` is `4π` [37]. The convergence of the Regge action in higher
dimensions is not yet formalized.

In the linearized theory of dimension 2, the edge data of a perturbation `h` of the flat metric
are the first variation `∫_e h(τ,τ)` of the squared lengths, as in the finite-element Regge
calculus {4}{5}. The first variation of the angle of a triangle is explicit [28]. The linearized
vertex deficit of the diagonal grid star is the derivative of `2π` minus the sum of the angles,
and vanishes for the flat star [29]. For a quadratic perturbation it equals the mesh squared
times `∂₀∂₁ h₀₁ - ½(∂₁² h₀₀ + ∂₀² h₁₁)` exactly, which is half of `∂ᵢ∂ⱼ hᵢⱼ - Δ tr h` [30]. If
the entries of `h` are within `K s³` of their quadratic Taylor polynomials on the cube of radius
`s`, the error is at most `336 K s³` [31]; smooth compactly supported functions satisfy this
with one `K` for all base points [32]. The Riemann sums of a Lipschitz compactly supported
function over the lattice of mesh `1/n` differ from its integral by at most a constant over `n`
[33]. Together, for smooth compactly supported symmetric `h` and a `C¹` weight `f`, the weighted
sum of the linearized vertex deficits differs from the integral of `f` times the linearized
curvature by at most a constant over `n` [34]. A concrete `h` and weight give a positive limit,
and without the `∂₀∂₁ h₀₁` term the limit would be `0` and is not approached [35]. The distance
of the hyperbolic metric along an `x`-line is the coordinate difference [36].

For a Riemannian metric in a chart, geodesics exist locally and are unique, and the exponential
map satisfies `‖exp_x v − x − v‖ ≤ C‖v‖²` [13]. The squared geodesic distance has an explicit
expansion to fifth order in the displacement, uniformly on compact sets [14], and an expansion to
sixth order, in which the terms of odd order vanish about the midpoint of the two points [15];
the order six is sharp [20]. The chart distance is Mathlib's Riemannian distance `riemannianEDist`
for the Riemannian bundle of the metric whenever an admissible curve joins the two points [21].

In area Regge calculus {3} the ten triangle areas of a 4-simplex replace its ten edge lengths. The
squared area of a triangle is Heron's formula in the squared edge lengths, and its first-order
change is given by an explicit Jacobian, with the second-order term exact since the formula is
quadratic [22]. The Jacobian is the Fréchet derivative of the squared-area map [23]. At the regular
4-simplex it is invertible, with an explicit inverse [22]; hence the squared areas, and the areas,
determine the squared lengths in a neighbourhood of the regular simplex [23]. The areas do not
always determine the lengths: at the simplex with `s₀ᵢ = 1`, `sᵢⱼ = 2` the Jacobian is singular
[22], and two different Euclidean 4-simplices (Gram matrices positive definite by the leading
minors) have the same ten areas [22]; both are realised by explicit affinely independent points
of `ℝ⁴`, so they are actual simplices of non-zero volume [24]. Numerical cross-check:
`scripts/regge/area_jacobian_check.py`.

In dimension 3, on the Kuhn triangulation of the cube grid (six congruent tetrahedra per cube, the
orthoscheme `0, e₁, e₁+e₂, e₁+e₂+e₃` and its coordinate permutations; seven edge classes and 36
incidences of a tetrahedron with one of its edges), the dihedral angle as a function of the six
squared lengths is differentiable along affine lines with an explicit derivative [38]. The six
dihedral angles of the orthoscheme are `π/4, π/2, π/3, π/2, π/2, π/4`, and the angles at the
hinges of each of the seven edge classes add up to `2π` [39]. Under the first-order squared-length
variation `-(1/3) Rm(y, z, y, z)` of an algebraic curvature tensor of dimension 3, the sum over the
36 incidences of the edge length times the variation of the dihedral angle is `-R/2`; weighting by
the squared length, or by `1`, gives a different value [39]. Numerical cross-check:
`scripts/regge/regge3d_core.py`. In a diagonal chart `diag(a², b², c²)` the identity holds exactly
for any symmetric Ricci tensor: the Gram identity and the geometry of one incidence [40] make the
edge length times the variation of the dihedral angle a rational function of the squared lengths,
with a closed form for each of the 36 incidences [41], [42], [43], [44], [45], [46], and the closed
forms sum to `-R·abc/2` [47]. An example chart checks the value and that it differs from the
orthonormal one [47]. The squared dihedral angle of a tetrahedron is smooth on the nondegenerate edge lengths and has a uniform second-order Taylor bound on compact sets of them [48], and it is unchanged when all squared lengths are multiplied by the same positive number [49]. The angle is also `C³` there, and a `C³` function on an open subset of a proper normed space has a Taylor remainder of third order after the Hessian term, uniformly on compact sets, which gives a uniform third-order expansion of the dihedral angle [53] (the one-dimensional bound it rests on needs derivatives only on the unit interval [52]). Along a curve `L + ε c + ε² ρ` of admissible squared lengths the angle has an expansion to order `ε²` with a uniform cubic remainder, also after the common rescaling `ε²` of the lengths [54]. For a star of simplices around an edge class, given as a named hypothesis `JetStarCore` that the angles of the flat star sum to `2π`, that the first-order coefficients sum to zero and that the second-order coefficients, weighted by the edge length, sum to `-(R/2)√det g`, the class sum of the angles at scale `ε` is `2π + ε² c₂` up to `M ε³` [54]. The jet-level star identity is proved on the slice of normal-coordinate jets (identity metric, vanishing first derivatives, second derivatives of curvature form): the Gram, first-order and second-order edge coefficients are those of the orthoscheme, zero, and the first variations of `kuhn_regge_core`, so the class angle sums are `2π` and the weighted second-order terms add up to `-R/2`; the flat metric is a non-vacuity example [55]. The algebraic core also holds on the curvature tensor of the product of the hyperbolic plane with a line, with value `-R/2 = 1`, and both wrong hinge weights give a different value there [56]. A function with a uniform `C/N` error against a Lipschitz limit has a lattice sum within `(C + Lf)/N` of the integral of the limit over the unit cube [57]. In any dimension the squared geodesic distance between two points near a vertex equals, up to a uniform error of fifth order in the mesh size, a polynomial in the metric and its first two derivatives at the vertex [50]. For the Euclidean metric the polynomial reproduces the squared distance exactly, and a polynomial without its leading term does not [51]. For a general linear chart the identity is checked numerically
(`scripts/regge/regge3d_affine.py`), not proven, and the convergence of the Regge action itself in
dimension 3 is not yet formalized.

For a general positive definite Gram matrix `G` at the centre of a Kuhn cell, the dihedral-angle
derivative combination is a polynomial in the squared lengths [58], and for the second-order
lengths of the algebraic form `-(1/3) Rm(y, z, y, z)` the sum over the 36 incidences equals
`det G · tr (adj G · B) / 2` as an exact polynomial identity, first for the six symmetric basis
matrices and then for a general `B` [59], [60], [61], [62]. In a chart, the Christoffel symbols and
the Riemann tensor of a smooth metric at a point are explicit expressions in the metric, its inverse
and its first and second partial derivatives [63]. For every positive definite `G` the 36 Gram
tetrahedra are admissible and the dihedral angles in each of the seven edge classes add up to `2π`:
each class is a fan around the hinge axis, and the complex coordinate in the plane quotient turns the
angle sum into the argument of a product [64]. At a point where all first partial derivatives of a
Riemannian 3-metric vanish (for example the centre of normal coordinates), but for any positive
definite metric matrix and any second derivatives, the weighted sum over the 36 incidences of the
first variation of the dihedral angle along the second-order lengths is a rational expression [65]
that equals `det R / 2` [66], and therefore the jet-level star identity `JetStarCore` holds there
with scalar curvature `R` [67]. This is not the general chart: the first derivatives of the metric
are zero at the point, and the convergence of the 3D Regge action needs the same statement at
every hinge. Trust checks: the Euclidean metric satisfies the hypotheses; for sphere-like second
derivatives the sum is `3`, not `0` and not `6` [68]. The identity of [66] is generated and checked
in exact arithmetic by `scripts/regge/gen_flat_star.py`, and the fans of [64] by
`scripts/regge/gen_star_angle.py`.

At a point of a Riemannian 3-metric where the first derivatives need not vanish, the edge polynomial
splits into the squared length of the vertices displaced by `ε Γ(k, k)/2` and the flat second-order part of
the shifted second derivatives `Sdd = ∂∂g - g ΓΓ` [69], and the derivative of the Christoffel symbols in terms of `Sdd` [77]. The complex-number lemmas of closed fans, of pinning
a multiple of `2π` by continuity, and of vanishing expansion coefficients [70], [71] show that a closed
fan of displaced vectors keeps its angle sum `2π` for small displacement [72]; applied to the seven edge
classes of the Kuhn star this gives angle sum `2π` for small `ε` in each class [73], and the first- and
second-order coefficients of the displaced angle sums vanish [74]. With the flat identity applied to `Sdd`
and the scalar curvature at a point written with `Sdd` [75], the jet-level star identity `JetStarCore`
holds at every point of a Riemannian metric, with no condition on the first derivatives [75]. This says
nothing about the convergence of the Regge action itself or about a triangulation of a manifold. Trust
checks: the Euclidean metric and `diag(exp x₀, 1, 1)`, which has a nonzero first derivative at the origin
(so the flat theorem does not apply to it), satisfy the general theorem [76]. The seven displaced-class
statements are generated by `scripts/regge/gen_chart_change.py`.

The integral over the unit cube of the divergence of a periodic `C¹` field of `ℝ³` is zero [78], the divergence theorem of Mathlib
on the box with the opposite faces cancelling. With it the Saint-Venant form of the linearized Regge limit and the Fierz–Pauli density
of a periodic smooth symmetric field have the same integral over the unit cube [79]: their difference is the divergence of an explicit
periodic field, and the identity of the densities is pointwise and polynomial. This is the integration by parts on the torus only;
that the `η²` coefficient of the integrated curvature density of `1 + η h` is half the integral of the Fierz–Pauli density (the integral itself is the second `η`-derivative) is proved separately [87].

The scalar curvature of a coordinate metric at a point is an explicit function of the inverse metric and its first and second
derivatives [80]. For the metric `1 + η h` of a smooth symmetric field `h` this function, times `√det / 2`, is a smooth function
`Feta` of the jet `(η, h, ∂h, ∂∂h)` where the determinant is positive [80]; it vanishes at `η = 0` [80]. Dimension 3, smooth `h`;
no expansion in `η` and no integral yet.

The curvature density `Feta` of `1 + η h` expands to second order in `η`, with a cubic remainder that is uniform on compact
sets of jets [81]; the two coefficients are defined as derivatives and not yet computed.

Second-order expansions at `η = 0` of real functions are closed under sums, products, inverses and square roots, and their
coefficients are unique [82] [83]. With them the curvature density of `1 + η h` is expanded from its explicit formula: the inverse
metric, the Christoffel symbols and their derivatives, and the scalar curvature have explicit first and second coefficients, and the
coefficients `F1`, `F2` of the uniform expansion [81] are `R1 / 2` and `R2 + R1 tr h / 2` [84]. For symmetric jets `F1` is half the
linearized scalar curvature and `F2` is the Fierz–Pauli density of `∂h` plus the divergence of an explicit field [85]. The identities
are polynomial; they are also checked with exact arithmetic in `scripts/regge/eh_jet_poly_check.py`, with a control that fails.
Nothing here is an integral statement.

The cube integral of the scalar-curvature density `(R/2) √det` of `1 + η h`, for a smooth symmetric periodic field `h`, equals
`(η²/2)` times the cube integral of the Fierz–Pauli density of `∂h`, up to `C |η|³` [87]; the first coefficient integrates to zero
and the second differs from the Fierz–Pauli density by an explicit periodic divergence [86]. This is a statement about the integrated
density of `1 + η h`: nothing about the Regge action, about geodesic or interpolated edge lengths, or about triangulations.

For a non-zero periodic field, `cos (2π y₀) E₁₂`, the cube integral of the Fierz–Pauli density is `-π²` [88]. The hinge density with
the volume weights replaced by `1` integrates to `-7π²/3` for the same field, so it does not give the Fierz–Pauli integral, twice the `η²` coefficient [88]; the
exact-arithmetic computation of both densities is `scripts/regge/eh_wrong_model_check.py`.

**Status of T-RC3 (partial).** In dimension 3 the library proves an energy-level limit on the periodic Kuhn complex of the
3-torus: the sum `Q_n` of the linearized Regge action, built from the interpolated degrees of freedom of Christiansen (2011),
eq. (5), converges to the Saint-Venant form (`Qn_converges`), and that limit is the second `η`-derivative (twice the `η²` coefficient) of the
integrated curvature density of `1 + η h` (`eh_eta_sq_coeff`). This is a limit of a quadratic form on one triangulation family. Christiansen's Theorem 4.7
is the convergence of eigenpairs for shape-regular families on tori; it is not proved here, and neither are the comparison of
geodesic with interpolated lengths nor a non-fat counterexample. The milestone stays open.

In two dimensions the deficit angles of a closed triangulated surface with Euclidean triangles add up to `2π (V - E + F)`
[89]: the angles sum to `π` per triangle, so the angle sum over all vertices is `π F`, and `3 F = 2 E` when every edge lies in
two triangles. The octahedron inscribed in the unit sphere (chordal edge lengths) has deficit sum `4π`, and the octahedron with
one face removed has `5π`, not `2π χ`, so the closedness is needed [89]. This is a combinatorial check of the round-sphere
value `4π`, not a convergence theorem and not a statement about triangulations of other surfaces.

A 2-complex with boundary is a disc in the combinatorial sense exactly when it is an intrinsic
triangulated disc [16].

Further results of this area in the results catalogue:
Lorentzian Regge calculus with Sorkin's complex angles: flat Minkowski regions have zero deficit angles
and solve the Regge equations [90]. For non-degenerate squared lengths the Lorentzian Regge action is
stationary under boundary-fixed variations exactly when the area-derivative-weighted deficits vanish at
every interior edge [101]. The 3D Regge action of the Kuhn triangulation of a grid converges to
half the Einstein-Hilbert action of a Riemannian metric (the Kuhn-grid case of the convergence theorem
of Cheeger, Mueller and Schrader) [91]. The Regge action of a flat closed 3-complex is a quadratic form
in the first variations of the lengths up to third order [92]. The Regge action of the periodic Kuhn
complex of the 3-torus with geodesic lengths of a periodic Riemannian metric tends to half the
Einstein-Hilbert action [93]. The sum Q_n of the linearized Regge action of the periodic Kuhn complex
converges to the Saint-Venant form [94]. The linearized deficit angle at a vertex of a flat positively
oriented star under a displacement field with a metric perturbation t is -t times the area of the star,
independent of the gauge, covariant under scaling, and zero if and only if t = 0 [95]. Fatness is
needed: thin triangles have unbounded angle sensitivity, so the angles are not uniformly Lipschitz in
the edge lengths [96]. A flat background gives zero linearized deficit [97]. In dimension 4 the
area-weighted sum over the 240 hinge incidences of Kuhn's orthoscheme triangulation of the first
variation of the dihedral angle for a curvature operator K is -scal(K)/2 [98]. Trust checks of the
dimension 4 Regge sum: a flat curvature operator gives zero, and the sum without the area weights does
not vanish for a scalar-flat curvature operator [99]. Mathlib form of the fifth-order expansion of the
squared geodesic distance: for a Riemannian coordinate metric on an open subset U of Rⁿ, viewed as a
Riemannian manifold, the square of Mathlib's riemannianEDist equals the quartic jet F_x(y − x) up to
O(‖y − x‖⁵), uniformly for x in a compact set, and the same about the midpoint with no cubic term [100].

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
17. Lightlike/Regge/CMS/Final.lean - `Geodesic.IsRiemMetric.cms_convergence`
18. Lightlike/Regge/CMS/Triangulation.lean - `Geodesic.IsRiemMetric.cms_convergence_triangulation`
19. Lightlike/Regge/CMS/GridExample.lean - `CMS.grid_bound_general`,
    `CMS.grid_triangulation_bound`, `CMS.grid_interior_positive`, `CMS.reversed_star_not_fat`
20. Lightlike/Regge/Geodesic/Tests.lean - `Geodesic.dist_sq_expansion_midpoint6_sharp`,
    `Geodesic.cubicShear_dist_sq_expansion_midpoint6`
21. Lightlike/Regge/Geodesic/Riemannian.lean - `Geodesic.IsRiemMetric.riemannianEDist_eq`,
    `Geodesic.IsRiemMetric.riemannianEDist_eq_iInf`,
    `Geodesic.IsRiemMetric.riemannianEDist_eq_of_isPreconnected`
22. Lightlike/Regge/AreaRegge/Basic.lean - `AreaRegge.areaSq_add`, `AreaRegge.triAreaSq_right`,
    `AreaRegge.triAreaSq_wrong`, `AreaRegge.jac_regular_isUnit`, `AreaRegge.jac_corner_kernel`,
    `AreaRegge.jac_corner_det`, `AreaRegge.corner_pair`
23. Lightlike/Regge/AreaRegge/Deriv.lean - `AreaRegge.hasFDerivAt_areaSqMap`,
    `AreaRegge.hasStrictFDerivAt_areaSqMap`, `AreaRegge.areaSqMap_local_inj`,
    `AreaRegge.area_local_inj`
24. Lightlike/Regge/AreaRegge/Realization.lean - `AreaRegge.corner_pair_realized`,
    `AreaRegge.realizes_plus`, `AreaRegge.realizes_minus`
25. Lightlike/Regge/CMS/Hyperbolic.lean - `CMS.scalar_hyp`, `CMS.isRiemMetric_hyp`
26. Lightlike/Regge/CMS/HyperbolicGrid.lean - `CMS.hyp_integral_neg`, `CMS.hyp_grid_bound`
27. Lightlike/Regge/CMS/RefiningGrid.lean - `CMS.refining_grid_bound`,
    `CMS.hyp_refining_grid`
28. Lightlike/Regge/Linear/AngleDeriv.lean - `Regge.Linear.hasDerivAt_triAngle`
29. Lightlike/Regge/Linear/Deficit.lean - `Regge.Linear.hasDerivAt_vertexDeficit`,
    `Regge.Linear.flat_vertexDeficit`
30. Lightlike/Regge/Linear/Model.lean - `Regge.Linear.linDef_model`
31. Lightlike/Regge/Linear/Local.lean - `Regge.Linear.linDef_taylor`
32. Lightlike/Regge/Linear/Taylor.lean - `Regge.Linear.taylor_bound`
33. Lightlike/Regge/Linear/Riemann.lean - `Regge.Linear.riemann_sum`
34. Lightlike/Regge/Linear/Converge.lean - `Regge.Linear.linearized_regge_converges`
35. Lightlike/Regge/Linear/Tests.lean - `Regge.Linear.nonvacuity`, `Regge.Linear.wrong_model_fails`
36. Lightlike/Regge/CMS/HyperbolicDist.lean - `CMS.dist_hyp_xline`
37. Lightlike/Regge/CMS/Sphere.lean - `CMS.isRiemMetric_sph`, `CMS.scalar_sph`,
    `CMS.sph_integral`
38. Lightlike/Regge/Conv3/DihedralDeriv.lean - `Regge.Conv3.hasDerivAt_dihSq`
39. Lightlike/Regge/Conv3/KuhnCore.lean - `Regge.Conv3.h01_angle`, `Regge.Conv3.star_angle_sum`,
    `Regge.Conv3.kuhn_regge_core`, `Regge.Conv3.wrong_weight_sq`,
    `Regge.Conv3.wrong_weight_one`, `Regge.Conv3.kuhn_regge_core_identity`
40. Lightlike/Regge/Conv3/ChartBase.lean - `Regge.Conv3.gram_identity`, `Regge.Conv3.inc_geom`
41. Lightlike/Regge/Conv3/ChartCases0.lean - `Regge.Conv3.ldth_cf00`, `Regge.Conv3.ldth_cf01`,
    `Regge.Conv3.ldth_cf02`, `Regge.Conv3.ldth_cf03`, `Regge.Conv3.ldth_cf04`,
    `Regge.Conv3.ldth_cf05`
42. Lightlike/Regge/Conv3/ChartCases1.lean - `Regge.Conv3.ldth_cf10`, `Regge.Conv3.ldth_cf11`,
    `Regge.Conv3.ldth_cf12`, `Regge.Conv3.ldth_cf13`, `Regge.Conv3.ldth_cf14`,
    `Regge.Conv3.ldth_cf15`
43. Lightlike/Regge/Conv3/ChartCases2.lean - `Regge.Conv3.ldth_cf20`, `Regge.Conv3.ldth_cf21`,
    `Regge.Conv3.ldth_cf22`, `Regge.Conv3.ldth_cf23`, `Regge.Conv3.ldth_cf24`,
    `Regge.Conv3.ldth_cf25`
44. Lightlike/Regge/Conv3/ChartCases3.lean - `Regge.Conv3.ldth_cf30`, `Regge.Conv3.ldth_cf31`,
    `Regge.Conv3.ldth_cf32`, `Regge.Conv3.ldth_cf33`, `Regge.Conv3.ldth_cf34`,
    `Regge.Conv3.ldth_cf35`
45. Lightlike/Regge/Conv3/ChartCases4.lean - `Regge.Conv3.ldth_cf40`, `Regge.Conv3.ldth_cf41`,
    `Regge.Conv3.ldth_cf42`, `Regge.Conv3.ldth_cf43`, `Regge.Conv3.ldth_cf44`,
    `Regge.Conv3.ldth_cf45`
46. Lightlike/Regge/Conv3/ChartCases5.lean - `Regge.Conv3.ldth_cf50`, `Regge.Conv3.ldth_cf51`,
    `Regge.Conv3.ldth_cf52`, `Regge.Conv3.ldth_cf53`, `Regge.Conv3.ldth_cf54`,
    `Regge.Conv3.ldth_cf55`
47. Lightlike/Regge/Conv3/ChartCore.lean - `Regge.Conv3.ldth_eq_cf`, `Regge.Conv3.cf_sum`,
    `Regge.Conv3.diag_core`, `Regge.Conv3.diag_core_example`,
    `Regge.Conv3.diag_core_ne_orthonormal`
48. Lightlike/Regge/Conv3/DihedralTaylor.lean - `Regge.Conv3.contDiffAt_Dh`,
    `Regge.Conv3.isOpen_valid`, `Regge.Conv3.Dh_smul`, `Regge.Conv3.hasDerivAt_Dsq`,
    `Regge.Conv3.dihSq_taylor`
49. Lightlike/Regge/Conv3/DihedralScale.lean - `Regge.Conv3.cosSq_smul`,
    `Regge.Conv3.dihSq_smul`
50. Lightlike/Regge/Conv3/EdgePoly.lean - `Geodesic.edgePoly`,
    `Geodesic.IsRiemMetric.edge_sq_poly`
51. Lightlike/Regge/Conv3/EdgePolyTests.lean - `Geodesic.edgePoly_euclid`,
    `Geodesic.edgePoly_euclid_exact`, `Geodesic.edgePoly_euclid_wrong`
52. Lightlike/Regge/Linear/Taylor1DOn.lean - `Regge.Linear.abs_le_of_deriv_le_on`,
    `Regge.Linear.taylor2_line_on`
53. Lightlike/Regge/Conv3/DihedralTaylor2.lean - `Regge.Conv3.taylor3_uniform`,
    `Regge.Conv3.contDiffAt_Dsq`, `Regge.Conv3.fderiv_Dsq`, `Regge.Conv3.dihSq_taylor3`
54. Lightlike/Regge/Conv3/JetCore.lean - `Regge.Conv3.dihSq_curve_expansion`,
    `Regge.Conv3.dihSq_scaled_expansion`, `Regge.Conv3.class_sum_expansion`,
    `Regge.Conv3.JetStarCore`, `Regge.Conv3.JetStarCore.class_expansion`
55. Lightlike/Regge/Conv3/JetSlice.lean - `Regge.Conv3.NormalSlice`,
    `Regge.Conv3.NormalSlice.incQ_eq`, `Regge.Conv3.NormalSlice.incC_eq`,
    `Regge.Conv3.NormalSlice.incR_eq`, `Regge.Conv3.class_partition`,
    `Regge.Conv3.slice_core`, `Regge.Conv3.euclid_core`
56. Lightlike/Regge/Conv3/HypProductCore.lean - `Regge.Conv3.ricH2R`,
    `Regge.Conv3.h2r_core`, `Regge.Conv3.h2r_wrong_weight_sq`,
    `Regge.Conv3.h2r_wrong_weight_one`, `Regge.Conv3.h2r_wrong_weights_differ`
57. Lightlike/Regge/Conv3/LatticeSum.lean - `Regge.Conv3.riemann_sum_lipschitz`,
    `Regge.Conv3.lattice_sum_converges`
58. Lightlike/Regge/Conv3/KuhnBridge.lean - `Regge.Conv3.mul_Pp_eq`, `Regge.Conv3.mul_Nn_eq`,
    `Regge.Conv3.mul_diff_eq`
59. Lightlike/Regge/Conv3/KuhnBasis.lean - `Regge.Conv3.kuhn_basis_00`, `Regge.Conv3.kuhn_basis_01`,
    `Regge.Conv3.kuhn_basis_02`, `Regge.Conv3.kuhn_basis_11`, `Regge.Conv3.kuhn_basis_12`,
    `Regge.Conv3.kuhn_basis_22`, `Regge.Conv3.kuhn_assemble`
60. Lightlike/Regge/Conv3/KuhnLinear.lean - `Regge.Conv3.kuhn_lin_poly`,
    `Regge.Conv3.kuhn_lin_num1`, `Regge.Conv3.kuhn_lin_num2`, `Regge.Conv3.kuhn_lin_num3`
61. Lightlike/Regge/Conv3/KuhnLinear2.lean - `Regge.Conv3.kuhn_lin_num4`,
    `Regge.Conv3.kuhn_lin_num5`, `Regge.Conv3.kuhn_lin_num6`, `Regge.Conv3.kuhn_lin_rho`
62. Lightlike/Regge/Conv3/KuhnStar.lean - `Regge.Conv3.kuhn_star_identity`
63. Lightlike/Regge/Conv3/JetCurvature.lean - `Regge.Conv3.pd_inv`, `Regge.Conv3.pd_christoffel`,
    `Regge.Conv3.riemann_jet`, `Regge.Conv3.scalarCurvature_jet`
64. Lightlike/Regge/Conv3/StarAngle.lean - `Regge.Conv3.quad_fan`, `Regge.Conv3.hex_fan`,
    `Regge.Conv3.valid_incQ`, `Regge.Conv3.jet_angle_sum`
65. Lightlike/Regge/Conv3/FlatStar.lean - `Regge.Conv3.sqrt_Dh_inc`, `Regge.Conv3.Einc`,
    `Regge.Conv3.Rnum`
66. Lightlike/Regge/Conv3/FlatStarIdentity.lean - `Regge.Conv3.flat_star_identity`
67. Lightlike/Regge/Conv3/FlatStarJet.lean - `Regge.Conv3.scalar_flat`,
    `Regge.Conv3.jetStarCore_of_flat`
68. Lightlike/Regge/Conv3/FlatStarTests.lean - `Regge.Conv3.euclid_flat_core`,
    `Regge.Conv3.sphere_sum`, `Regge.Conv3.sphere_sum_ne_double`
69. Lightlike/Regge/Conv3/ChartChange.lean - `Regge.Conv3.edgeC_eq_chr`,
    `Regge.Conv3.edgeR_eq_displaced`, `Regge.Conv3.pd_g_eq_chr`, `Regge.Conv3.christoffel_symm_low`
70. Lightlike/Regge/Conv3/ClosedFan.lean - `Regge.Conv3.closed_fan_sum`,
    `Regge.Conv3.eventually_eq_of_int_mul`, `Regge.Conv3.coeffs_zero_of_expansion`
71. Lightlike/Regge/Conv3/ChartChangeFan.lean - `Regge.Conv3.Dsq_lens3`,
    `Regge.Conv3.dispLen_eq_lens3`
72. Lightlike/Regge/Conv3/ClassPin.lean - `Regge.Conv3.closed_class_pin`
73. Lightlike/Regge/Conv3/ChartChangeClasses.lean - `Regge.Conv3.cls0_disp`,
    `Regge.Conv3.cls1_disp`, `Regge.Conv3.cls2_disp`, `Regge.Conv3.cls3_disp`,
    `Regge.Conv3.cls4_disp`, `Regge.Conv3.cls5_disp`, `Regge.Conv3.cls6_disp`
74. Lightlike/Regge/Conv3/ChartChangeCoeffs.lean - `Regge.Conv3.disp_coeffs`
75. Lightlike/Regge/Conv3/ChartChangeGeneral.lean - `Regge.Conv3.scalar_eq_flat`,
    `Regge.Conv3.jetStarCore_of_chart`
76. Lightlike/Regge/Conv3/ChartChangeTests.lean - `Regge.Conv3.euclid_chart_core`,
    `Regge.Conv3.expMetric_core`, `Regge.Conv3.expMetric_not_flat`
77. Lightlike/Regge/Conv3/ChartChangeDChr.lean - `Regge.Conv3.dChr_eq_flat`,
    `Regge.Conv3.inv_contract`
78. Lightlike/Regge/Conv3/DivergencePeriodic.lean - `Regge.Conv3.integral_div_periodic`
79. Lightlike/Regge/Linear3/FierzPauli.lean - `Regge.Linear3.fpDens`, `Regge.Linear3.fp_identity`,
    `Regge.Linear3.div_Tfield`, `Regge.Linear3.saintVenant_eq_fierzPauli`
80. Lightlike/Regge/Conv3/CurvatureEta.lean - `Regge.Conv3.curvJ`, `Regge.Conv3.scalar_curvJ`,
    `Regge.Conv3.scalar_gEta`, `Regge.Conv3.Feta_eq`, `Regge.Conv3.contDiffOn_Feta`, `Regge.Conv3.Feta_flat`
81. Lightlike/Regge/Conv3/FetaTaylor.lean - `Regge.Conv3.F1`, `Regge.Conv3.F2`,
    `Regge.Conv3.feta_expansion`
82. Lightlike/Regge/Conv3/Exp2.lean - `Regge.Conv3.Exp2`, `Regge.Conv3.Exp2.poly`, `Regge.Conv3.Exp2.add`,
    `Regge.Conv3.Exp2.mul`, `Regge.Conv3.Exp2.sum`, `Regge.Conv3.Exp2.congr`
83. Lightlike/Regge/Conv3/Exp2Inv.lean - `Regge.Conv3.Exp2.inv`, `Regge.Conv3.Exp2.sqrt`,
    `Regge.Conv3.Exp2.unique`, `Regge.Conv3.poly2_unique`
84. Lightlike/Regge/Conv3/CurvatureCoeffs.lean - `Regge.Conv3.Gi_exp`, `Regge.Conv3.dchr_exp`,
    `Regge.Conv3.curv_exp`, `Regge.Conv3.feta_exp`, `Regge.Conv3.F_eq`
85. Lightlike/Regge/Conv3/CurvaturePoly.lean - `Regge.Conv3.divTp`, `Regge.Conv3.F2_poly`,
    `Regge.Conv3.F1_eq`, `Regge.Conv3.F2_eq`
86. Lightlike/Regge/Linear3/PeriodicDivergences.lean - `Regge.Linear3.div_S1field`, `Regge.Linear3.div_Tprime`,
    `Regge.Linear3.integral_F1_zero`, `Regge.Linear3.integral_F2_eq`
87. Lightlike/Regge/Linear3/EtaCoefficient.lean - `Regge.Linear3.eh_eta_sq_coeff`,
    `Regge.Linear3.eh_eta_sq_coeff_zero`
88. Lightlike/Regge/Linear3/EtaCoefficientTests.lean - `Regge.Linear3.integral_fpDens_hTest`,
    `Regge.Linear3.integral_wrongDens_hTest`, `Regge.Linear3.wrong_weights_ne`
89. Lightlike/Regge/GaussBonnet2D.lean - `Regge.discrete_gauss_bonnet`, `Regge.sum_angleOf`,
    `Regge.octahedron_deficit_sum`, `Regge.octOpen_deficit_sum_ne`
90. Lightlike/Regge/Lorentzian/FlatSolution.lean - `ReggeLor.IsGeometric4.lorReggeAction_stationary`
91. Lightlike/Regge/Conv3/ReggeConvergence.lean - `Regge.Conv3.reggeAction3`,
    `Regge.Conv3.regge3d_tendsto`
92. Lightlike/Regge/Linear3/SecondOrder.lean - `Regge.Linear3.regge_second_order`
93. Lightlike/Regge/Linear3/TorusConvergence.lean - `Regge.Linear3.torus_regge_converges`
94. Lightlike/Regge/Linear3/LinearizedLimit.lean - `Regge.Linear3.Qn_converges`
95. Lightlike/Regge/Linearized/DeficitLaw.lean - `Regge.Linearized.combStarDeficit_hasDerivAt_area`,
    `Regge.Linearized.combStarDeficit_gauge_independent`,
    `Regge.Linearized.combStarDeficit_scale_covariant`, `Regge.Linearized.combStarDeficit_zero_iff`
96. Lightlike/Regge/Linearized/ThinTriangle.lean -
    `Regge.Linearized.thin_triangle_sensitivity_unbounded`,
    `Regge.Linearized.thin_triangle_not_uniformly_lipschitz`
97. Lightlike/Regge/Linearized/Tests.lean - `Regge.Linearized.flat_background_zero`
98. Lightlike/Regge/CMS4/Kuhn4Core.lean - `Regge4.kuhn4_sum`
99. Lightlike/Regge/CMS4/Kuhn4Trust.lean - `Regge4.kuhn4_sum_flat`, `Regge4.kuhn4_unweighted_fails`
100. Lightlike/Upstream/GeodesicExpansion/Final.lean -
     `Upstream.GeodesicExpansion.IsRiemMetric.riemannianEDist_sq_expansion`,
     `Upstream.GeodesicExpansion.IsRiemMetric.riemannianEDist_sq_expansion_midpoint`
101. Lightlike/Regge/Lorentzian/ReggeEquations.lean - `ReggeLor.lorReggeAction_stationary_iff`

## References

1. T. Regge, General relativity without coordinates, *Nuovo Cimento* 19 (1961) 558.
2. J. Cheeger, W. Müller, R. Schrader, On the curvature of piecewise flat spaces, *Commun. Math.
   Phys.* 92 (1984) 405.
3. J. W. Barrett, M. Roček, R. M. Williams, A note on area variables in Regge calculus,
   *Class. Quantum Grav.* 16 (1999) 1373.
4. M. Roček, R. M. Williams, The quantization of Regge calculus, *Z. Phys. C* 21 (1981) 371.
5. S. H. Christiansen, On the linearization of Regge calculus, *Numer. Math.* 119 (2011) 613.
