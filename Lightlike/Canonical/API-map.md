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
and these hold without a smoothness hypothesis [18] {2}. In Minkowski space the time coordinate gives lapse one and the Euclidean induced metric [17].

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

## References

1. T. Thiemann, *Modern Canonical Quantum General Relativity*, Cambridge University Press, 2007, chapter 1;
   R. Arnowitt, S. Deser and C. W. Misner, *The dynamics of general relativity*, equations (3.14a), (3.14b).
2. E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, equations (2.43),
   (2.68)-(2.70), (3.1)-(3.10), (4.27)-(4.32).
