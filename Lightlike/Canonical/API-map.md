# The ADM constraints in coordinates

## Abstract (Alpha)

This API describes the Hamiltonian and momentum constraints of general relativity on a spatial slice,
in the coordinate form: a spatial metric and a momentum density on `ℝᵈ`, the constraints smeared against
test fields, and the brackets of the smeared constraints computed with Gateaux derivatives along compactly
supported variations. It proves part of the algebra of the constraints and checks the definitions on flat
data and on data that violate one constraint.

## Content (Alpha)

The Hamiltonian constraint density is `(tr (hπhπ) − (tr hπ)²/(d − 1))/√det h − √det h · R`, with the spatial
scalar curvature `R` of the coordinate formulas of the geometry API, and the momentum constraint is
`∇_k π^{ik} = 0` {1}; its smeared form is `∫ π^{ij} ℒ_ξ h_ij` [1]. The data `h = 1`, `π = 0` satisfy both
constraints, and neither constraint is implied by the other [2]. The bracket of two functionals is the derivative of
the first along the variation given by the `π`-gradient of the second, minus the same with the roles exchanged [1].
The `π`-gradient of the smeared momentum constraint is `ℒ_ξ h` [3].

The bracket of two smeared momentum constraints is the smeared constraint of the Lie bracket of the shifts [3] {1}.
The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint is the Hamiltonian constraint
smeared with the derivative of the lapse along the shift [4] {1}. For this the scalar curvature is a smooth function
of the 2-jet of the metric [5], it is covariant under the flow of a vector field [6], the kinetic term is a scalar
density [7], and the smeared Hamiltonian constraint can be differentiated under the integral sign along a compactly
supported variation [4]. The momentum constraint in the Lie-derivative form equals the ADM form, the integral of
`−2 ξ_i ∇_k π^{ik}` [8]. The bracket of two smeared Hamiltonian constraints is the smeared momentum constraint of the
shift `Y^i = h^{ij}(N ∂_j M − M ∂_j N)` [13]: the first-order form of the smeared constraint is differentiated along `M` times
the unit `π`-gradient [4], the terms without derivatives of the lapses cancel in the antisymmetrization [12], the remaining
coefficient is `−2 ∇_σ π^{bσ}` [12], by index algebra of the Christoffel symbols [9] and of the derivative of the unit
`π`-gradient [10] [11], and the momentum constraint in ADM form [8] closes the argument [13] {1}. On a hypersurface, a manifold without a global chart, the constraints are the sums over the atlas pieces of the chart integrals of tensor and density fields given by chart components with their change laws, and the bracket is the Gateaux derivative along chart families [14]; on `ℝᵈ` with constant chart families they are the chart constraints [15]; the three brackets on the hypersurface are open tasks (T-CA1-P4 to P6). [TODO]

A time function of a spacetime, a smooth function with a timelike gradient, gives without charts the ADM data of its
level sets: the lapse, the unit normal, the shift of a time vector, the induced metric and the extrinsic curvature
[16] {2}; the lapse is positive, the normal is a unit normal of the leaves, the time vector is the lapse times the normal
plus the shift, the induced metric vanishes on the normal, and the extrinsic curvature is symmetric for the
Levi-Civita connection [16]; the gradient of a smooth function is a smooth vector field, so the unit normal is smooth
and these hold without a smoothness hypothesis [18] {2}. On vectors tangent to the leaves the extrinsic curvature is minus
half the Lie derivative of the metric along the normal [22] {2}. For a Lorentzian metric the leaves are spacelike: the
induced metric is positive on nonzero tangent vectors [23]. In a chart whose first coordinate is the time function, the
coordinate components of the metric are `g₀₀ = −N² + β_kβ^k`, `g₀ᵢ = βᵢ` and `gᵢⱼ = γᵢⱼ`, so the spatial block of the
coordinate metric on a slice, the chart data `h` of the constraints, is the induced metric of the leaf [20] {2}; in
Minkowski space it is the Euclidean metric [21]. With the coordinate components of the extrinsic curvature the slice also
carries the momentum `π^{ij} = √det h (K h^{ij} − K^{ij})`, symmetric for the Levi-Civita connection [20] {2}; it
vanishes on the slices of Minkowski space [21]. In Minkowski space the time coordinate gives lapse one and the Euclidean induced metric [17].

Two exact solutions give initial data that satisfy the constraints [19]. The slice `t = 0` of Schwarzschild in
Schwarzschild coordinates carries the induced metric `diag((1 − 2M/r)⁻¹, r², r² sin²θ)` and zero momentum, since the
shift vanishes and the slice is static; its Ricci tensor is not zero but its scalar curvature is, so both constraints
hold {3}. The slice of spatially flat FLRW carries `a(t)² δ_ij` and the momentum `−2a'(t) δ^{ij}` of its extrinsic
curvature; the Hamiltonian constraint with the density of the comoving fluid holds exactly when the first Friedmann
equation does, and the momentum constraint holds {3} {4}; for a slice of spatial curvature `k`, with metric
`(a S)² δ_ij`, `S = 1/(1 + k|x|²/4)`, the scalar curvature is `6k/a²` and the constraint holds exactly when
`(a'/a)² = 8πGρ/3 − k/a² + Λ/3`, the cosmological constant entering as a fluid with `w = −1` [19] {4}.

In the connection variables of loop quantum gravity a co-triad `e` of the spatial metric gives the densitized triad
`E = |det e| e⁻¹`, the triad form `K^i_a` of the extrinsic curvature and the spin connection `Γ^i_a` of the co-triad,
built from the Christoffel symbols of the metric [24] {5} {6}. The spin connection is compatible with the triad
(`de + ε Γ ∧ e = 0`), the Ashtekar–Barbero connection is `A = Γ + γK`, and the Gauss constraint
`∂_a E^a_i + ε_ijk A^j_a E^a_k` vanishes on the variables of ADM data, its extrinsic-curvature part exactly because the
extrinsic curvature is symmetric [25] {5}. In four dimensions the spin connection of a tetrad is the gauge transform
of the Christoffel connection by the frame, and its curvature is the Riemann tensor in the frame [26] {6}. The Holst
action density adds to the Palatini term the dual term weighted by `1/γ`; on the tetrad connection the dual term
vanishes by the first Bianchi identity and the Palatini term is `det e · R`, so the Holst density is the
Einstein–Hilbert density for every `γ` [27] {5} {6}; the dual term of a constant rotation connection is not zero [27]. The densitized triad contracted with the variation of
the spin connection is a divergence, so `∫ E δΓ = 0` and the functional derivative of `∫ Γ E` is `Γ`, the fact behind
the canonical transformation to the Ashtekar–Barbero variables [28] {6}; the derivative of the spin connection along a
path of co-triads satisfies the linearised compatibility, so this holds for the actual variation of `Γ` [29]. So on the
whole triad phase space `∫ E δA = γ ∫ E δK`, and for a symmetric `K` (the Gauss constraint) the Ashtekar–Barbero
potential `∫ E δA` is `γ/2` times the ADM potential `∫ π δh` plus the exact term `γ δ∫ √h K` [30] {5}.

A connection in a local trivialisation, matrix-valued components `A_a(x)` on the chart, has along every `C¹` path a
parallel transport `U' = −A_a(e) ė^a U`, `U(t₁) = 1`, which exists on every interval and is unique (by the global
existence theorem for Lipschitz right-hand sides of `Lightlike/ODE/GlobalLipschitz.lean`); the holonomy `A(e)` along an
edge is its end value, and for an `su(2)` connection it lies in `SU(2)` [31] {5}. It is unchanged under orientation-preserving
reparametrisation, the reversed path has the inverse holonomy, and for piecewise `C¹` paths (lists of edges) the
holonomy of a composite is the product, `A(e₂ ∘ e₁) = A(e₂) A(e₁)` [32] {5}. Under a gauge transformation
`A ↦ g⁻¹ A g + g⁻¹ dg` the holonomy changes only at the end points, `A(e) ↦ g(e(t₂))⁻¹ A(e) g(e(t₁))` [33] {5}.

A grid computation in dimension two (`scripts/adm_algebra_check.py`) supports the three brackets; with the kinetic
coefficient `1/2` of dimension three, used in dimension two, the bracket of two Hamiltonian constraints differs from
the momentum constraint of the structure function.

## Lean References

1. Lightlike/Canonical/ADM.lean - `Lightlike.Canonical.hamiltonianDensity`, `Lightlike.Canonical.momentumDensity`, `Lightlike.Canonical.hamiltonianConstraint`,
   `Lightlike.Canonical.momentumConstraint`, `Lightlike.Canonical.admBracket`
2. Lightlike/Tests/ADM.lean - `Lightlike.Canonical.flat_hamiltonian`, `Lightlike.Canonical.flat_momentum`, `Lightlike.Canonical.wrong_momentum_violates`,
   `Lightlike.Canonical.wrong_hamiltonian_violates`
3. Lightlike/Canonical/MomentumBracket.lean - `Lightlike.Canonical.isPiGradient_momentumConstraint`, `Lightlike.Canonical.bracket_momentum_momentum`
4. Lightlike/Canonical/HamiltonianBracket.lean - `Lightlike.Canonical.admBracket_momentum_hamiltonian`
5. Lightlike/Canonical/CurvatureJet.lean - `Lightlike.Canonical.scalarCurvature_eq_Rjet`, `Lightlike.Canonical.differentiableAt_Rjet`
6. Lightlike/Canonical/CurvatureCovariance.lean - `Lightlike.Canonical.hasDerivAt_scalar_lie`
7. Lightlike/Canonical/KineticCovariance.lean - `Lightlike.Canonical.dkinJ_lie`
8. Lightlike/Canonical/MomentumADM.lean - `Lightlike.Canonical.momentumConstraint_eq_adm_of_smooth`
9. Lightlike/Canonical/HamiltonianAlgebra.lean - `Lightlike.Canonical.stage1`, `Lightlike.Canonical.Tnc_Ymat`
10. Lightlike/Canonical/HamiltonianPm.lean - `Lightlike.Canonical.pd_Pf`
11. Lightlike/Canonical/HamiltonianLink.lean - `Lightlike.Canonical.dP_sub_corr`, `Lightlike.Canonical.sum_Dpi`
12. Lightlike/Canonical/HamiltonianWEq.lean - `Lightlike.Canonical.W_eq`
13. Lightlike/Canonical/HamiltonianHHBracket.lean - `Lightlike.Canonical.bracket_hamiltonian_hamiltonian_of_smooth`
14. Lightlike/Canonical/Hypersurface.lean - `Lightlike.Canonical.momentumConstraintM`, `Lightlike.Canonical.hamiltonianConstraintM`, `Lightlike.Canonical.admBracketM`
15. Lightlike/Canonical/HypersurfaceBridge.lean - `Lightlike.Canonical.constraintM_bridge_global`
16. Lightlike/Canonical/Foliation.lean - `Lightlike.Canonical.lapse`, `Lightlike.Canonical.unitNormal`, `Lightlike.Canonical.shift`,
    `Lightlike.Canonical.spatialMetric`, `Lightlike.Canonical.extrinsicCurvature`, `Lightlike.Canonical.isUnitNormal`,
    `Lightlike.Canonical.g_time_time`, `Lightlike.Canonical.extrinsicCurvature_symm`
17. Lightlike/Canonical/TestsFoliation.lean - `Lightlike.Canonical.isTimeFunction_minkowski`, `Lightlike.Canonical.spatialMetric_minkowski`
18. Lightlike/Canonical/FoliationSmooth.lean - `Lightlike.Canonical.contMDiffAt_timeGrad`, `Lightlike.Canonical.smoothNear_unitNormal`,
    `Lightlike.Canonical.isUnitNormal_of_timeFunction`, `Lightlike.Canonical.extrinsicCurvature_symm_of_timeFunction`
19. Lightlike/Canonical/InitialData.lean - `Lightlike.Canonical.schSlice_hamiltonianConstraint`, `Lightlike.Canonical.schSlice_momentumConstraint`,
    `Lightlike.Canonical.flrw_hamiltonian_iff`, `Lightlike.Canonical.flrw_momentumConstraint`,
    `Lightlike.Canonical.scalarCurvature_flrwSliceK`, `Lightlike.Canonical.flrwK_hamiltonian_iff_Lambda`,
    `Lightlike.Canonical.flrwK_momentumConstraint`
20. Lightlike/Canonical/FoliationChart.lean - `Lightlike.Canonical.IsAdaptedChart`, `Lightlike.Canonical.coordMetric_adapted_00`,
    `Lightlike.Canonical.coordMetric_adapted_0i`, `Lightlike.Canonical.coordMetric_adapted_ij`, `Lightlike.Canonical.admSliceMetric`,
    `Lightlike.Canonical.admSliceMetric_eq_spatialMetric`, `Lightlike.Canonical.admSliceMomentum`,
    `Lightlike.Canonical.admSliceMomentum_symm`
21. Lightlike/Canonical/TestsFoliationChart.lean - `Lightlike.Canonical.admSliceMetric_minkowski`,
    `Lightlike.Canonical.admSliceMomentum_minkowski`
22. Lightlike/Canonical/FoliationLie.lean - `Lightlike.Canonical.extrinsicCurvature_eq_neg_half_lieDeriv`
23. Lightlike/Canonical/FoliationSpacelike.lean - `Lightlike.Canonical.spatialMetric_pos`
24. Lightlike/Canonical/Triad.lean - `Lightlike.Canonical.IsCoTriad`, `Lightlike.Canonical.densTriad`, `Lightlike.Canonical.triadK`,
    `Lightlike.Canonical.gaussK_eq_zero_iff`
25. Lightlike/Canonical/SpinConnection.lean - `Lightlike.Canonical.spinConn`, `Lightlike.Canonical.spin_compat`,
    `Lightlike.Canonical.abConn`, `Lightlike.Canonical.gaussConstraint`, `Lightlike.Canonical.gauss_spinConn`,
    `Lightlike.Canonical.gauss_abConn`, `Lightlike.Canonical.gauss_abConn_antisymm_violates`
26. Lightlike/Canonical/Tetrad.lean - `Lightlike.Canonical.tetradConn`, `Lightlike.Canonical.gaugeCurv`,
    `Lightlike.Canonical.gaugeCurv_tetradConn`
27. Lightlike/Canonical/Holst.lean - `Lightlike.Canonical.holstDensity`, `Lightlike.Canonical.holstStar_tetradConn`,
    `Lightlike.Canonical.palatini_tetradConn`, `Lightlike.Canonical.holstDensity_tetradConn`,
    `Lightlike.Canonical.holstStar_rotation`
28. Lightlike/Canonical/AshtekarCanonical.lean - `Lightlike.Canonical.E_dSpin_eq_div`, `Lightlike.Canonical.integral_E_dSpin_eq_zero`
29. Lightlike/Canonical/SpinVariation.lean - `Lightlike.Canonical.linCompat_dSpin`,
    `Lightlike.Canonical.integral_E_deriv_spinConn_eq_zero`
30. Lightlike/Canonical/AshtekarSymplectic.lean - `Lightlike.Canonical.triad_potential`,
    `Lightlike.Canonical.integral_E_dAbConn_eq_triadK`, `Lightlike.Canonical.integral_E_dAbConn`,
    `Lightlike.Canonical.triad_potential_needs_symm`
31. Lightlike/Canonical/Holonomy.lean - `Lightlike.Canonical.transport`, `Lightlike.Canonical.holonomy`,
    `Lightlike.Canonical.transport_trans`, `Lightlike.Canonical.holonomy_mem_specialUnitaryGroup`,
    `Lightlike.Canonical.holonomy_u1Conn`
32. Lightlike/Canonical/HolonomyPaths.lean - `Lightlike.Canonical.holonomy_comp_reparam`,
    `Lightlike.Canonical.holonomy_revPath`, `Lightlike.Canonical.PwPath.hol_trans`, `Lightlike.Canonical.PwPath.hol_rev`
33. Lightlike/Canonical/HolonomyGauge.lean - `Lightlike.Canonical.gaugeConn`, `Lightlike.Canonical.holonomy_gaugeConn`,
    `Lightlike.Canonical.holonomy_pureGauge`

## References

1. T. Thiemann, *Modern Canonical Quantum General Relativity*, Cambridge University Press, 2007, chapter 1;
   R. Arnowitt, S. Deser and C. W. Misner, *The dynamics of general relativity*, equations (3.14a), (3.14b).
2. E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, equations (2.43),
   (2.68)-(2.70), (3.1)-(3.10), (3.27), (4.27)-(4.32), (4.43)-(4.47), (4.108).
3. E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, equations (4.19), (4.22),
   (4.104), (4.108), (7.16), (7.17).
4. J. C. Aurrekoetxea, K. Clough and E. A. Lim, *Cosmology using numerical relativity*, arXiv:2409.01939, equations (3),
   (23), (25), (26).
5. A. Ashtekar and J. Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018,
   equations (2.6), (2.16)-(2.21), (2.23), (4.35)-(4.37).
6. S. Holst, *Barbero's Hamiltonian derived from a generalized Hilbert-Palatini action*, arXiv:gr-qc/9511026,
   equations (1), (3)-(6).
