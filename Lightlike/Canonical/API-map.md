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
supported variation [4]. The bracket of two smeared Hamiltonian constraints, with the inverse metric as structure
function, is not yet formalized. [TODO]

A grid computation in dimension two (`scripts/adm_algebra_check.py`) supports the three brackets; with the kinetic
coefficient `1/2` of dimension three, used in dimension two, the bracket of two Hamiltonian constraints differs from
the momentum constraint of the structure function.

## Lean References

1. Lightlike/Canonical/ADM.lean - `hamiltonianDensity`, `momentumDensity`, `hamiltonianConstraint`,
   `momentumConstraint`, `admBracket`
2. Lightlike/Tests/ADM.lean - `flat_hamiltonian`, `flat_momentum`, `wrong_momentum_violates`,
   `wrong_hamiltonian_violates`
3. Lightlike/Canonical/MomentumBracket.lean - `isPiGradient_momentumConstraint`, `bracket_momentum_momentum`
4. Lightlike/Canonical/HamiltonianBracket.lean - `admBracket_momentum_hamiltonian`
5. Lightlike/Canonical/CurvatureJet.lean - `scalarCurvature_eq_Rjet`, `differentiableAt_Rjet`
6. Lightlike/Canonical/CurvatureCovariance.lean - `hasDerivAt_scalar_lie`
7. Lightlike/Canonical/KineticCovariance.lean - `dkinJ_lie`

## References

1. T. Thiemann, *Modern Canonical Quantum General Relativity*, Cambridge University Press, 2007, chapter 1;
   R. Arnowitt, S. Deser and C. W. Misner, *The dynamics of general relativity*, equations (3.14a), (3.14b).
