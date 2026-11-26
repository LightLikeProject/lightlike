# Exact solutions of general relativity

## Abstract (Alpha)

This API states the vacuum Einstein equations, with a cosmological constant, for a metric given in
coordinates, and verifies two exact solutions: Minkowski space and the exterior Schwarzschild
metric. It builds on the coordinate curvature of the spacetime geometry API.

## Content (Alpha)

The Einstein tensor is built from the Ricci tensor and the scalar curvature, and the vacuum
Einstein equations with cosmological constant `Λ` say that the Einstein tensor plus `Λ g` vanishes
on an open set {1} [1]. For `Λ = 0` in any dimension other than two, they are equivalent to the
vanishing of the Ricci tensor [1]. Minkowski space solves them [1].

The exterior Schwarzschild metric of mass `M > 0`, in Schwarzschild coordinates on `r > 2M` and
`0 < θ < π`, has Lorentzian signature and solves the vacuum equations with `Λ = 0` {2} [2]. The Kerr metric of mass `M` and spin `a`, in Boyer–Lindquist coordinates, is a coordinate metric on `r > 0`,
`Δ ≠ 0`, `0 < θ < π` [53] and a vacuum solution of the Einstein equations with `Λ = 0` for every `M` and
`a` [54]; its line element and determinant are those of Visser {5}. For `0 < M` and `a² ≤ M²` the outer
horizon is `r₊ = M + √(M² − a²)`, the surface gravity (defined as `Δ'(r₊)/(2(r₊² + a²))`) is
`√(M² − a²)/(2 M r₊)`, and the Killing field `∂_t + Ω_H ∂_φ`, `Ω_H = a/(2 M r₊)`, has vanishing norm on
`r = r₊` [55]; its norm factors as `(r − r₊)` times an explicit quotient [56]. That `r = r₊` is a Killing
horizon, and the equation `∇_χ χ = κ χ`, are not formalized. De Sitter and other exact solutions are
not yet formalized. [TODO]

The Kruskal-Szekeres extension of the Schwarzschild metric: its four regions, the horizon `T = ±X`, the
radial null directions and the one-way property of the black hole region {3} [3]; the Kruskal coordinates of
the Schwarzschild exterior, which is region I {3} [4]; its Penrose diagram {3} [5]. The Kretschmann scalar of
the Schwarzschild metric is `48 M²/r⁶` [6] (the value printed in {3}, eq. (7.30), is `12 G²M²/r⁶`), also in
Eddington-Finkelstein and Kruskal coordinates, where it is unbounded near `r = 0` [7]; ingoing radial null
geodesics reach `r = 0` at a finite affine parameter [8], and the energy, the axial angular momentum and the
radial equation hold along all geodesics of the Eddington-Finkelstein chart [13]. In the global chart
of the Kruskal manifold the equations of motion of the geodesics are derived from Noether's formula [14], and
the boost charge, the squared angular momentum and `g(w, w)` are constant along them [15]. A geodesic on a finite interval whose radius is bounded below
has a limit in the manifold [15]. Hence a geodesic of an extension that starts in the Kruskal manifold
does not leave it [16]. The Kruskal-Szekeres spacetime is inextendible: it has no extension to a connected Hausdorff
Lorentzian manifold with a smooth metric {4} [17]. A point of the Kruskal chart reaches the infinity of region I
along a future-directed causal curve exactly when `T < X`, and the boundary `T = X` of that set is the event
horizon {3} [18]. The coordinate field `∂_T` is a time orientation of the Kruskal manifold [19]. The whole Kruskal manifold
`{X² - T² > -1} × S²` is given in one global chart as a Lorentzian manifold [9], of which `(T, X, θ, φ)` is a
chart [10]; it solves the vacuum equations [11], and in every extension of it, in the sense of {4}, a sequence
approaching the singularity has no limit [12].

Further results of this area in the results catalogue:
The null cone of complexified Minkowski space is the set of rank-one spinor matrices; a point is a
twistor line, determined by the point, every line off the plane at infinity is one, and two lines meet
iff their points are null separated; the Plücker coordinates of a line lie on the Klein quadric and
every point of the quadric is a line [20]. The twistor Hermitian form has signature (2,2); the twistor
line of a point is null iff the point is real; the stabilizer of the infinity twistor in SU(2,2) is the
Poincaré group SL(2,C) ⋉ {Hermitian translations} [21]. Projective twistor space CP^3 splits by the sign
of the (++−−) form into PT+, PN, PT−, each nonempty; the line of a point lies in PN iff the point is
real [22]. Lines of CP^3 (2-planes of C^4) are in bijection with the points of the Klein quadric; the
lines meeting the line at infinity are exactly the complement of the affine chart of complexified
Minkowski space, X^23 = I_AB X^AB = 0 [23]. A bispinor 2-form is ε F̃ + ε̄ F with symmetric SD and ASD
parts (a linear equivalence), and Maxwell's equations hold iff the parts satisfy the spin-1
zero-rest-mass equations [24]. Zero-rest-mass fields of every helicity; the components of a C² z.r.m.
field solve the wave equation; the momentum eigenstates p_{α1}⋯p_{α2|h|} e^{ik·x} are z.r.m. fields
[24]. Tensors with the symmetries of a Weyl tensor are exactly ε ε Ψ̃ + ε̄ ε̄ Ψ with Ψ, Ψ̃ totally
symmetric (the Weyl spinor decomposition) [25]. The Penrose transform by contour integrals is a
zero-rest-mass field of helicity −(n+1)/2, 0 and (n+1)/2 (differentiation under the integral sign), and
for twistor functions of homogeneity 2h−2 it does not depend on the section of the line; the elementary
solution 2πi/det x [26]. A complex momentum is null iff its bispinor is −λλ̃ᵀ, the factorization is
unique up to little-group scaling; ⟨pq⟩[pq] = 2p·q, s_ij = ⟨ij⟩[ji], and the Schouten identities [27].
Three-particle special kinematics (all angle or all square brackets vanish), and three-point amplitudes
fixed by little-group scaling, x_12 = h_3 − h_1 − h_2, with the mass-dimension selection between angle
and square brackets [28]. The Parke–Taylor colour-ordered MHV amplitudes are cyclic, reflect with
(−1)^n, satisfy the U(1) decoupling identity for every n and the five-point Kleiss–Kuijf relation, have
little-group weights t^{−2h}, and at four points equal `[34]^4/([12][23][34][41])` under momentum
conservation [29]. The U(N) colour algebra in the normalisation Tr TᵃTᵇ = δᵃᵇ — completeness (Fierz) for
U(N) and SU(N), the structure constants as traces of commutators, products of two structure constants as
single traces, and the Jacobi identity [30]. The BCFW shift preserves momentum conservation and
on-shellness and makes channel momenta squared linear in z; a rational function with simple poles
vanishing at infinity has Â(0) = −Σ Res Â(z)/z, and with factorized residues this is the on-shell
recursion; for the shifted Parke–Taylor amplitude the single residue factorizes into lower-point
amplitudes [31]. The Parke–Taylor formula ⟨ij⟩⁴/(⟨12⟩⋯⟨n1⟩) for any positions i ≠ j of the two
negative-helicity gluons by BCFW recursion, conditional on the BCFW large-z falloff (3.11), taken as a
hypothesis (conditional) [32]. First law of Kerr black-hole mechanics, dM = kappa/(8 pi) dA + Omega_H
dJ, along any differentiable family of non-extremal Kerr black holes [33]. Smarr formula for Kerr, M = 2
Omega_H J + kappa A/(4 pi), for 0 < M and a^2 <= M^2 [34]. The Lichnerowicz formula in a torsion-free
skew frame on R^n: D^2 f = -sum of second covariant derivatives plus (s/4) f, with s the scalar
curvature of the frame connection, given the pair symmetry and the first Bianchi identity of that
curvature (conditional) [35]. Friedrich's eigenvalue bound on the round sphere in the stereographic
chart: a nonzero compactly supported C^2 eigenspinor of the Dirac operator has lambda^2 at least n^2/4
(n at least 2) [36]. For every k and sign epsilon the radial spinor with polynomial profile solves D f =
epsilon (k+1) f for the Dirac operator of the unit 2-sphere in the stereographic chart [37]. The Connes
distance of the flat Dirac operator on R^n between two points is the Euclidean distance, for every skew
Clifford representation on a nontrivial space [38]. The Connes distance on the circle R/LZ for the Dirac
operator -i d/dx is the geodesic distance, the infimum over integers m of |p - q - m L| [39]. The heat
trace of the unit 2-sphere, Σ(2l+1)e^{-t l(l+1)}, has the expansion 1/t + 1/3 + t/15 + O(t²) as t → 0⁺
[40]. The heat trace Σ_{k∈ℤⁿ} e^{-t|k|²} of the flat n-torus has the asymptotic expansion π^{n/2}
t^{-n/2} with every other coefficient zero, in particular no t⁰ term [41]. On the round 2-sphere and
3-sphere, any expansion of the heat trace has a₁ = (4π)^{-n/2} V R/6, with R the scalar curvature of the
round metric computed by Lightlike's scalarCurvature (R = n(n-1)) [42]. The scalar curvature of the
round unit n-sphere in stereographic coordinates is n(n-1) [43]. The coefficients of an asymptotic expansion of a heat trace are unique, to any finite order [57]; the
expansion of the unit 2-sphere heat trace has the coefficients of the Seeley–DeWitt formulas with
`V = 4π`, `R = 2`, `|Ric|² = 2` and `|Riem|² = 4` [58]. Induced gravity from the heat kernel:
for D = -Δ + ξR the coefficient a₁ is proportional to (1-6ξ), it vanishes for the conformal coupling in
n = 4 and not in other dimensions, and the induced inverse Newton constant is (1-6ξ)/(12πε) with
proper-time cutoff ε [44]. Poisson summation with a real shift: Σ_n e^{-πa(n+s)²} = a^{-1/2} Σ_n e^{-πn²/a} e^{2πins}, and the sum differs from a^{-1/2} by at most a^{-1/2} times the Gaussian tail Σ_{n≠0} e^{-πn²/a} [52]. The on-shell recursion for the colour-ordered Feynman amplitudes of
Yang–Mills theory: under the large-z falloff of the shifted amplitude, A_n is the sum over the planar
channels of the product of the lower amplitudes at the poles divided by the propagator (conditional)
[45]. The Ward identity of the colour-ordered Feynman amplitudes holds at every gluon for every number
of gluons, and with it the factorization on the poles and the recursion hold without the Ward identity
as a hypothesis (conditional) [46]. The Dirac operator squares to minus the Laplacian on flat space: D(D
f) = -Δ f for a C² function with values in a Clifford module [47]. Lichnerowicz in a frame: for a frame
connection with antisymmetric connection form and a curvature with the Riemann symmetries, D² f = −Σ
∇²f(eᵢ, eᵢ) + (s/4) f, given the Ricci identity for the frame Hessian (conditional) [48]. On the unit
2-sphere the curvature term of the Lichnerowicz formula is s/4 and not s/2 [49]. For every k and sign
epsilon the eigenvalue epsilon (k+1) of the Dirac operator of the unit 2-sphere in the stereographic
chart has an injective linear image of k+1 copies of the spinor module among its eigenspinors [50].
Within the angular polynomial class, a flat eigenspinor of the Dirac operator of the unit 2-sphere in
the stereographic chart that is reduced and satisfies the decay condition has eigenvalue plus or minus s
and the radial profile of the family of the lower bound [50]. In the angular polynomial class,
boundedness of the half-density spinor at the pole of the sphere forces the decay condition, so a
reduced flat eigenspinor of the Dirac operator of the unit 2-sphere in the stereographic chart has
eigenvalue plus or minus s and the radial profile of the lower bound [51].

In the compactified coordinates `(T, R, θ, φ)` of Minkowski space, future null infinity is the set
`T + R = π/2`, `|T - R| < π/2`; it is exactly the set of the points of retarded time `u` and angles
`(θ, φ)` [59], the conformal factor vanishes on it, and outgoing null rays `t - r = u` converge to the
point of retarded time `u` [59]. Global anti-de Sitter space with `r = tan ρ` has the metric
`cos⁻² ρ (-dt² + dρ² + sin² ρ dΩ²)` [60], and the compactified metric restricts on the boundary
`ρ = π/2` to `-dt² + dθ² + sin² θ dφ²`, the metric of `ℝ × S²` [61].
A Lorentz matrix with positive time-time entry sends the future null vector `(1, n)`, `|n| = 1`, to `K (1, n')`
with `K > 0` and `|n'| = 1` [62].
The Poincaré transformations `x ↦ Λ x + a` act on the points `(u, n)` of null infinity by `(u / K + a₀ - n' · a⃗, n')`, with the group law [63].

## Lean References

1. Lightlike/GR/Einstein.lean - `einsteinTensor`, `IsVacuumSolution`,
   `vacuum_iff_ricci_eq_zero`, `minkowski_isVacuumSolution`
2. Lightlike/GR/Schwarzschild.lean - `sch_isLorentzian`, `sch_isVacuumSolution`
3. Lightlike/GR/KruskalRegions.lean - `kr_eq_two_mul_iff`, `kr_eq_kr_iff`, `kruskalI`, `kruskalII`,
   `kruskalIII`, `kruskalIV`, `kruskalU_eq_union`, `two_mul_lt_kr_iff_mem`, `kr_lt_two_mul_iff_mem`,
   `kruskalQuad_radial_eq_zero_iff`, `IsKruskalFutureCausal`, `kruskalII_of_futureCausal`,
   `kr_lt_of_futureCausal_kruskalII`
4. Lightlike/GR/KruskalExterior.lean - `kruskalChange_exterior`, `kruskalChange_exterior_div`,
   `kruskalChange_exterior_mem`, `exists_exterior_of_mem_kruskalI`
5. Lightlike/GR/KruskalPenrose.lean - `penroseMap`, `penroseU`, `bijOn_penroseMap`,
   `tan_mul_tan_eq_one_of_abs_add`, `penroseMap_horizon_iff`, `pullback_kruskal_penroseInv`,
   `penrose_conformalFactor_pos`
6. Lightlike/GR/SchwarzschildKretschmann.lean - `schRiem`, `riemann_sch`, `kretschmann_sch`
7. Lightlike/GR/KruskalKretschmann.lean - `kretschmann_congr_on`, `kretschmann_ef`, `kretschmann_kruskal`,
   `kretschmann_kruskal_unbounded`, `not_tendsto_of_isometric_chart`
8. Lightlike/GR/EFNullGeodesic.lean - `ef_ingoing_isGeodesicOn`, `ef_ingoing_null`,
   `tendsto_kretschmann_ef_ingoing`
9. Lightlike/GR/KruskalManifold.lean - `kruskalC`, `kruskalCMetric`, `kruskalC_isLorentzian`, `kruskalCOpen`,
   `kruskalManifoldMetric`
10. Lightlike/GR/KruskalSpherical.lean - `kruskalSph`, `jac_kruskalSph`, `pullback_kruskalC_sph`,
    `isChartChange_kruskalSph`
11. Lightlike/GR/KruskalManifoldCurvature.lean - `exists_kruskalSph_eq`, `ricci_kruskalC_eq_zero`,
    `kruskalC_isVacuumSolution`, `kretschmann_kruskalC`
12. Lightlike/GR/KruskalExtension.lean - `kretschmann_kruskalC_unbounded`, `not_tendsto_of_isometric_kruskal`,
    `IsLorentzianExtension.not_tendsto_kruskal`
13. Lightlike/GR/EFConstants.lean - `pd_eq_zero_of_invariant`, `ef_hasDerivAt_energy`, `ef_hasDerivAt_angular`,
    `ef_radial_identity`
14. Lightlike/GR/KruskalGeodesic.lean - `hasDerivAt_kG`, `hasDerivAt_kh`, `kQ`, `contraction_kruskalC`,
    `kruskalC_hasDerivAt_pT`, `kruskalC_hasDerivAt_pX`, `kruskalC_hasDerivAt_angular`
15. Lightlike/GR/KruskalGeodesicBound.lean - `kruskalC_hasDerivAt_r`, `kruskalC_hasDerivAt_boost`,
    `kruskalC_hasDerivAt_L2`, `kruskalC_hasDerivAt_kQ`, `radial_sq`, `kruskalC_radius_bounded`,
    `kruskalC_velocity_bounded`, `exists_tendsto_kruskalC_geodesic`
16. Lightlike/GR/KruskalInextendible.lean - `IsLorentzianExtension.false_of_geodesic_kruskal`
17. Lightlike/GR/KruskalMaximal.lean - `kruskal_isInextendible`
18. Lightlike/GR/KruskalHorizon.lean - `ReachesKruskalInfinity`, `reachesKruskalInfinity_iff`,
    `frontier_kruskal_past_of_infinity`
19. Lightlike/GR/KruskalOrientation.lean - `kruskalOrientation`, `kruskal_timeOrientable`
20. Lightlike/GR/ComplexMinkowski.lean - `qC_eq_zero_iff`, `qC_eq_zero_iff_tmul`,
    `isHermitian_spinorMat_iff`, `twistorLine_injective`, `exists_twistorLine_eq`,
    `twistorLine_inf_ne_bot_iff`, `plucker_klein`, `klein_decomposable`
21. Lightlike/GR/TwistorConformal.lean - `twistorNorm_inc_eq_zero_iff`, `twistorLine_null_iff`,
    `isSU22_and_fixesInfinity_iff`
22. Lightlike/GR/TwistorSpace.lean - `penroseHerm_signature`, `penroseNorm_incidence_eq_zero_iff`,
    `cp3_partition`, `mk_incidencePenrose_mem`
23. Lightlike/GR/TwistorKlein.lean - `kleinEquiv`, `compl_range_twistorLine`, `twistorLine_affine_chart`
24. Lightlike/GR/ZeroRestMass.lean - `Spinor.maxwell_decomposition`, `Spinor.maxwellEquiv`,
    `Spinor.maxwell_iff_zrm_D`, `Spinor.maxwell_iff_zrm`, `Spinor.IsZrmNeg`, `Spinor.IsZrmPos`,
    `Spinor.IsZrmNeg.box_eq_zero`, `Spinor.IsZrmPos.box_eq_zero`, `Spinor.planeWave_isZrmNeg`,
    `Spinor.planeWave_isZrmPos`, `Spinor.planeWave_isZrmScalar`
25. Lightlike/GR/WeylSpinor.lean - `Spinor.weyl_eq_weylOf`, `Spinor.weylOf_isWeyl`, `Spinor.weylEquiv`
26. Lightlike/GR/PenroseTransform.lean - `Spinor.hasFDerivAt_circleIntegral_twistorPt`,
    `Spinor.penroseNeg_isZrmNeg`, `Spinor.penroseScalar_isZrmScalar`, `Spinor.penrosePos_isZrmPos`,
    `Spinor.penroseNeg_rescale`, `Spinor.penroseScalar_rescale`, `Spinor.penrosePos_rescale`,
    `Spinor.penroseScalar_elementary`
27. Lightlike/GR/SpinorHelicity.lean - `SpinorHelicity.det_momBispinor`,
    `SpinorHelicity.mdot_self_eq_zero_iff`, `SpinorHelicity.exists_littleGroup_of_eq`,
    `SpinorHelicity.nullMom_littleGroup`, `SpinorHelicity.angleBr_mul_squareBr`,
    `SpinorHelicity.mandelstam_nullMom`, `SpinorHelicity.schouten_angleBr`,
    `SpinorHelicity.schouten_squareBr`
28. Lightlike/GR/ThreePointAmplitude.lean - `SpinorHelicity.conserved3_iff`,
    `SpinorHelicity.special_kinematics`, `SpinorHelicity.angleAnsatz_weights_iff`,
    `SpinorHelicity.three_point_dimension`, `SpinorHelicity.three_point_selection`
29. Lightlike/GR/ColourOrdered.lean - `SpinorHelicity.parkeTaylor_rotate`,
    `SpinorHelicity.parkeTaylor_rev`, `SpinorHelicity.eikonal_sum`,
    `SpinorHelicity.parkeTaylor_U1_decoupling`, `SpinorHelicity.parkeTaylor_littleGroup_plus`,
    `SpinorHelicity.parkeTaylor_littleGroup_minus`, `SpinorHelicity.parkeTaylor_KK5`,
    `SpinorHelicity.parkeTaylor_four_eq_square`
30. Lightlike/GR/ColourAlgebra.lean - `Colour.expand_generators`, `Colour.fierz`, `Colour.fierz_su`,
    `Colour.commutator_eq_structureConst`, `Colour.i_mul_eq_trace_sub`, `Colour.structureConst_mul_sum`,
    `Colour.jacobi_colour`
31. Lightlike/GR/BCFWFactorization.lean - `SpinorHelicity.conserved_bcfw`,
    `SpinorHelicity.mdot_momSum_bcfw`, `SpinorHelicity.mdot_momSum_bcfw_eq`,
    `SpinorHelicity.eval_div_nodal`, `SpinorHelicity.tendsto_residue`,
    `SpinorHelicity.tendsto_cocompact_zero`, `SpinorHelicity.eval_zero_eq_neg_sum_residues`,
    `SpinorHelicity.recursion_of_factorization`, `SpinorHelicity.ptShift_eq`,
    `SpinorHelicity.ptShift_rational`, `SpinorHelicity.ptShift_channel`,
    `SpinorHelicity.ptShift_onshell`, `SpinorHelicity.ptShift_factorization`
32. Lightlike/GR/ParkeTaylorAll.lean - `SpinorHelicity.IsBCFWFamilyMHV`,
    `SpinorHelicity.parkeTaylor_bcfw_far`, `SpinorHelicity.eq_parkeTaylor_of_bcfw_mhv`,
    `SpinorHelicity.eq_parkeTaylor_of_bcfw_mhv'`
33. Lightlike/GR/KerrFirstLaw/KerrFirstLaw.lean - `GR.KerrFirstLaw.kerr_first_law`
34. Lightlike/GR/KerrFirstLaw/KerrArea.lean - `GR.KerrFirstLaw.kerr_smarr`
35. Lightlike/Dirac/LichnerowiczGeneral.lean - `Dirac.lichnerowicz_general`
36. Lightlike/Dirac/StereoFriedrich.lean - `Dirac.eigen_sq_ge_friedrich_stereo`
37. Lightlike/Dirac/EigenGeneralK.lean - `Dirac.diracF_stereo_eigen_general`
38. Lightlike/Dirac/ConnesDistance2.lean - `Dirac.connesDist_eq_norm`
39. Lightlike/Dirac/ConnesDistance5.lean - `Dirac.circConnesDist_eq_iInf`
40. Lightlike/Geometry/HeatKernel/SphereTrace.lean - `HeatKernel.hasHeatExpansionTo_sphereTrace`
41. Lightlike/Geometry/HeatKernel/Torus.lean - `HeatKernel.hasHeatExpansion_torusTrace`
42. Lightlike/Geometry/HeatKernel/SphereCurvatureTie.lean - `HeatKernel.sphere2_a1_curv`,
    `HeatKernel.sphere3_a1_curv`, `HeatKernel.hasHeatExpansionTo_sphereTrace_curv`,
    `HeatKernel.hasHeatExpansionTo_sphere3Trace_curv`
43. Lightlike/Geometry/HeatKernel/StereoCurvature.lean - `HeatKernel.scalarCurvature_stereo`
44. Lightlike/Geometry/HeatKernel/InducedGravity.lean - `HeatKernel.heatCoeffsE_conformal_four_one`,
    `HeatKernel.heatCoeffsE_conformal_one_ne_zero`, `HeatKernel.conformalCoupling_eq_sixth_iff`,
    `HeatKernel.inducedInvG_spec`
45. Lightlike/GR/FeynmanRecursion.lean - `SpinorHelicity.eq_sum_div_sub_of_residues`,
    `SpinorHelicity.bgAmplitude_eq_sum_channels`
46. Lightlike/GR/FeynmanWard.lean - `SpinorHelicity.ward_all`, `SpinorHelicity.residue_factorization'`,
    `SpinorHelicity.bgAmplitude_eq_sum_channels'`
47. Lightlike/Dirac/Flat.lean - `Dirac.dirac_dirac`
48. Lightlike/Dirac/LichnerowiczFormula.lean - `Dirac.lichnerowicz_frame`
49. Lightlike/Dirac/LichnerowiczTests.lean - `Dirac.curvatureTerm_sphere`,
    `Dirac.sphere_half_formula_fails`
50. Lightlike/Dirac/EigenAngular.lean - `Dirac.sphere_dirac_lower_bound`, `Dirac.modeMap_injective`,
    `Dirac.modeMap_eigen`, `Dirac.sphere_eigen_mode`, `Dirac.angG_flat_eigen`, `Dirac.dirac_angular`,
    `Dirac.angular_class_complete`, `Dirac.angG_flat_converse`, `Dirac.mode_complete`,
    `Dirac.odeOp_unique`
51. Lightlike/Dirac/EigenPole.lean - `Dirac.angular_class_complete_bounded`, `Dirac.decay_of_bounded`,
    `Dirac.degree_le_of_bounded`, `Dirac.level_of_degree`
52. Lightlike/Geometry/HeatKernel/ShiftedTheta.lean - `HeatKernel.tsum_exp_neg_shift`,
    `HeatKernel.abs_tsum_shift_sub_le`, `HeatKernel.gaussTail`
53. Lightlike/GR/Kerr.lean - `kerrMetric`, `kerrU`, `isCoordMetric_kerr`
54. Lightlike/GR/KerrRicci.lean - `kerr_isVacuumSolution`
55. Lightlike/GR/KerrHorizon.lean - `kerrKappa`, `kerrOmega`, `kerrKappa_eq`, `kerr_chi_null`
56. Lightlike/GR/KerrHorizonKillingField/KerrSurfaceGravity.lean - `kerrChiNorm_eq`
57. Lightlike/Geometry/HeatKernel/Unique.lean - `HeatKernel.HasHeatExpansionTo.coeff_unique`,
    `HeatKernel.HasHeatExpansion.coeff_unique`
58. Lightlike/Geometry/HeatKernel/Consistency.lean - `HeatKernel.hasHeatExpansionTo_sphereTrace_geom`
59. Lightlike/GR/AdSConformalBoundary/ScriPlus.lean - `scriPlus_eq_range`, `scriFactor_scriPlus`,
    `compactify_tendsto_scriPoint`
60. Lightlike/GR/AdSConformal.lean - `pullback_adsGlobal`
61. Lightlike/GR/AdSConformalBoundary/AdSBoundary.lean - `adsCompact_boundary`
62. Lightlike/GR/AdSConformalBoundary/NullDirection.lean - `nullDirFactor_pos`, `mulVec_nullVec_eq`,
    `sum_sq_nullDirMap`
63. Lightlike/GR/AdSConformalBoundary/ScriAction.lean - `scriAct`, `scriAct_comp`, `nullDirFactor_mul`,
    `nullDirMap_mul`

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 4.
2. K. Schwarzschild, Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
   Theorie, *Sitzungsber. Preuss. Akad. Wiss.* (1916) 189.
3. S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7.
4. J. Sbierski, The C⁰-inextendibility of the Schwarzschild spacetime and the spacelike diameter in
   Lorentzian geometry, arXiv:1507.00601, Definition 2.15.
5. M. Visser, *The Kerr spacetime: A brief introduction*, arXiv:0706.0622, section 5 (eq. (57), the
   Boyer–Lindquist line element; eq. (106), the determinant) and the section on horizons
   (eqs. (112)–(114)).
