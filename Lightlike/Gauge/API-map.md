# Constrained Hamiltonian systems

## Abstract (Alpha)

This API treats constrained Hamiltonian systems on a flat phase space `X × X`: first- and second-class constraints, the
Dirac bracket, the Dirac consistency algorithm with its termination, chart independence and chart gluing, the linear
coisotropic reduction, and the infinitesimal and local gauge structure (Faddeev–Popov, gauge directions, gauge orbits).
The Marsden–Weinstein reduction of a manifold by a free proper action at a regular value is not treated: there is no moment
map or quotient manifold in the library, and only the linear case is proved.

## Content (Alpha)

For constraint functions `φ_a` on `X × X`, with the Poisson bracket of Physlib, the bracket matrix is `C_ab = {φ_a, φ_b}`:
the constraints are first class when `C = 0` on the constraint surface and second class when `det C ≠ 0` there, and the Dirac
bracket is `{f, g} - Σ {f, φ_a} (C⁻¹)_ab {φ_b, g}` [1] {1}. `C` is antisymmetric, the Dirac bracket is antisymmetric and
vanishes against a constraint, a second-class set has an even number of constraints, and the reduced tangent space
has dimension `dim E - 2 dim(orbit)` for a linear action at a zero of the moment map [2]. For the particle on a circle the
constraints `|q|² - 1` and `⟨p, q⟩` are second class with reduced dimension `2`, and treating them as first class gives the
wrong count `0` [10].

The Dirac algorithm builds a chain of constraint surfaces by adding the consistency conditions. Under linear
independence of the gradients a regular stage has at most `dim E` constraint functions, and nested regular stages with
nonempty zero sets are constant from some stage on [3]; without regularity it need not terminate (`{x ≤ 1/(k+1)}` in `ℝ`).
The secondary constraints do not depend on the choice of the invertible block, for a first-order bracket and regular stages
[4] {2}. Constant rank of the consistency matrix gives local admissibility only, and the local charts are glued into a
finite atlas, so that the surfaces are constant from stage `dim E + 1` and the consistency system is solvable on the
final surface [5].

The form `σ` induced on `D^⊥/D` for an isotropic `D` is alternating and nondegenerate [6] {3}; this is the linear case of
Marsden–Weinstein. If the matrix `{G_a, φ_b}` of gauge-fixing functions with the constraints is invertible, the gauge
directions `X_{φ_b}` are independent and meet the slice tangent only in `0` [7]; the Hamiltonian fields of first-class
constraints are tangent to the constraint surface and `Ω`-orthogonal to its tangent directions [8]; and through every point of
the surface near `x₀` there is a gauge orbit, by Frobenius for a family involutive only on an invariant set [9] {2}.

## Lean References

1. Lightlike/Gauge/Constraints.lean - `Gauge.phaseGrad`, `Gauge.gradForm`, `Gauge.poissonBracket_eq_gradForm`,
   `Gauge.isSymplecticForm_gradForm`, `Gauge.IsRegularConstraints`, `Gauge.IsFirstClass`, `Gauge.IsSecondClass`,
   `Gauge.reducedDim`, `Gauge.reducedDimAllFirstClass`, `Gauge.diracBracket`
2. Lightlike/Gauge/ConstraintsAPI.lean - `Gauge.bracketMatrix_transpose`, `Gauge.diracBracket_antisymm`,
   `Gauge.diracBracket_constraint`, `Gauge.even_of_isSecondClass`, `Gauge.finrank_orbit_add_momentTangent`,
   `Gauge.finrank_reducedTangent`
3. Lightlike/Gauge/DiracRegular.lean - `Gauge.card_le_finrank_of_regular`, `Gauge.exists_stable_of_regular`
4. Lightlike/Gauge/DiracChart.lean - `Gauge.Stage.chiFun_zero_iff_of_admissible`, `Gauge.Stage.consistent_iff_leftNull`,
   `Gauge.zeroSet_stages_eq`
5. Lightlike/Gauge/DiracGlue.lean - `Gauge.DiracAtlas`, `Gauge.DiracAtlas.final_consistent`,
   `Gauge.final_consistent_of_constantRank`
6. Lightlike/Gauge/ReducedForm.lean - `Gauge.reducedForm`, `Gauge.reducedForm_isAlt`, `Gauge.reducedForm_nondegenerate`
7. Lightlike/Gauge/FaddeevPopov.lean - `Gauge.fpMatrix`, `Gauge.linearIndependent_hamField_of_det_ne_zero`,
   `Gauge.eq_zero_of_mem_ker_of_det_ne_zero`
8. Lightlike/Gauge/GaugeFlow.lean - `Gauge.hamField`, `Gauge.pairing_hamField_eq_zero_of_firstClass`,
   `Gauge.gradForm_hamField_eq_zero`
9. Lightlike/Gauge/Orbits/GaugeOrbits.lean - `Gauge.exists_gauge_orbit`
10. Lightlike/Tests/Constraints.lean - `Gauge.circle_isSecondClass`, `Gauge.circle_wrong_count`

## References

1. M. Henneaux, C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1.
2. A. Wipf, *Hamilton's formalism for systems with constraints*, arXiv:hep-th/9312078, Sections 3.1, 3.3 and 5.2.
3. A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764, Springer (2001), Lemma 23.3.
