# Spacetime geometry in coordinates

## Abstract (Alpha)

This API describes spacetime geometry the way general relativity textbooks compute it: a metric is
given by its components in a chart, and the Christoffel symbols, the Riemann and Ricci tensors and
the scalar curvature are the standard coordinate formulas. It also defines Lorentzian metrics on
smooth manifolds and connects them to their coordinate components, so that curvature statements
proven in coordinates apply to the components of a manifold-level metric.

## Content (Alpha)

A coordinate metric on an open set is a smooth, symmetric, invertible matrix-valued function of
the coordinates [1]. From it one computes the Christoffel symbols, the Riemann tensor, the Ricci
tensor and the scalar curvature by the standard formulas {1} [1]. Minkowski space is flat [1].

The lowered Riemann tensor is symmetric under exchange of its index pairs and satisfies the first
Bianchi identity [2]. The second Bianchi identity in coordinates is not yet formalized. [TODO]

Under a smooth change of coordinates the Riemann tensor, the Ricci tensor and the scalar curvature
transform as tensors, and solutions of the vacuum Einstein equations pull back to solutions [3].

A Lorentzian metric on a smooth manifold modelled on `ℝⁿ` is a smooth symmetric bilinear form on
each tangent space with signature (−,+,…,+), in the mostly-plus convention {2} [4]. In every chart
of the atlas its components form a coordinate metric of Lorentzian signature [5].

On a manifold modelled on a normed space the Lie bracket of vector fields is the commutator of derivations of smooth functions, `[X, Y] g = X (Y g) - Y (X g)` [9]; Mathlib has this for a vector space only, and the identity is the step for the tensoriality of the curvature below.

A Lorentzian metric has a Levi-Civita connection, the torsion-free connection compatible with it, given by the Koszul formula, and any two agree on vector fields differentiable at a point [10].

In a chart of a manifold modelled on `ℝⁿ` the coordinate vector fields commute and the Levi-Civita connection is given by the Christoffel symbols of the coordinate components, `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ` [11].

For a smooth connection on a Hausdorff manifold modelled on a finite-dimensional space without boundary, the curvature defined with extensions of tangent vectors does not depend on the extensions: in a chart it is an expression in the Christoffel tensor of the connection and its derivative, a function of the values of the three vectors only [12], [13].

For a Levi-Civita connection of a smooth Lorentzian metric (same hypotheses) the first Bianchi identity holds, the lowered curvature is antisymmetric in each pair of slots and symmetric under exchange of the pairs, and the Ricci tensor is symmetric [14].

In a chart of a manifold modelled on `ℝⁿ` (Hausdorff), the components of the curvature of a Levi-Civita connection are the coordinate Riemann tensor, its Ricci tensor and scalar curvature are the coordinate ones, and the Einstein equations hold on the manifold iff the coordinate vacuum equations hold in every chart [15].

For a smooth torsion-free connection the second Bianchi identity holds: the cyclic sum of the covariant derivative of the curvature vanishes [16].

In a chart, the covariant derivative of a bilinear form field, in particular of the Einstein tensor, is given by the components formula, so it is tensorial in the three arguments [17].

For a coordinate metric the contracted Bianchi identity holds, `g^{στ} ∇_σ G_{τν} = 0` for the coordinate Einstein tensor [18], and for the Levi-Civita connection of a Lorentzian metric on a manifold the divergence of the Einstein tensor vanishes [19].

The curvature of a manifold-level metric as a tensor field is defined in `Connection.lean` [7]: a connection is Mathlib's
covariant derivative on the tangent bundle; the Riemann curvature is `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`
(the sign convention of a Mathlib proposal, <https://github.com/leanprover-community/mathlib4/pull/45069>), the Ricci tensor is its trace over the first slot, the scalar
curvature its trace with the metric, the Levi-Civita connection is the torsion-free connection compatible with `g`, and the Einstein
equations with cosmological constant are `Ric - (S/2) g + Λ g = 0` [7]; the covariant derivative of the curvature and of a field of bilinear forms, the divergence and the Einstein tensor `Ric - (S/2) g` are defined there too [7]. These are definitions only: the existence and
uniqueness of the Levi-Civita connection, the independence of the curvature from the extensions, its symmetries, and the
agreement with the coordinate curvature of [1] in every chart are stated as proof tasks `T-GE1-P2` to `T-GE1-P8` (including the second and contracted Bianchi identities and Minkowski space as a solution)
(`Tasks/GE/`), with open proofs, except the last: on `ℝⁿ` the flat connection `∇_v Y = DY(v)` is a torsion-free connection compatible with the Minkowski metric with zero curvature, so Minkowski space satisfies the Einstein equations with `Λ = 0` [8]. [TODO]

In Minkowski space, an observer who travels out and back along two straight segments ages less
than one who stays at rest [6].

## Lean References

1. Lightlike/Spacetime/Curvature.lean - `IsCoordMetric`, `christoffel`, `riemann`, `ricci`,
   `scalarCurvature`, `minkowski_flat`
2. Lightlike/Spacetime/RiemannSymmetry.lean - `IsCoordMetric.riemannLower_pair_symm`,
   `IsCoordMetric.bianchi_first`
3. Lightlike/Spacetime/ChartChange.lean - `riemann_pullback`, `ricci_pullback`,
   `scalarCurvature_pullback`, `isVacuumSolution_pullback`
4. Lightlike/Spacetime/Lorentzian.lean - `LorentzianMetric`
5. Lightlike/Spacetime/Coordinates.lean - `LorentzianMetric.isLorentzianCoordMetric_coordMetric`
6. Lightlike/Spacetime/Minkowski.lean - `twin_paradox`
7. Lightlike/Spacetime/Connection.lean - `Connection`, `Connection.curvatureAt`, `Connection.riemannLowerAt`,
   `Connection.ricciAt`, `Connection.scalarCurvatureAt`, `Connection.IsMetricCompatible`,
   `Connection.IsLeviCivita`, `Connection.covDerivCurvatureAt`, `Connection.covDerivBilinAt`,
   `Connection.divBilinAt`, `Connection.einsteinField`, `LorentzianMetric.SatisfiesEinstein`
8. Lightlike/Spacetime/FlatConnection.lean - `flatConnection`, `flat_torsion`, `flat_curvatureAt`,
   `flat_isMetricCompatible`, `minkowski_satisfiesEinstein_proved`
9. Lightlike/Spacetime/LieDerivation.lean - `mfderiv_mlieBracket`, `mfderiv_eq_chart`, `mpullback_chart`,
   `dirDeriv`, `chartField`
10. Lightlike/Spacetime/LeviCivita.lean - `koszul`, `leviCivita`, `leviCivita_torsion`,
   `leviCivita_compat`, `leviCivita_unique`, `leviCivita_exists_unique_proved`
11. Lightlike/Spacetime/ChartConnection.lean - `coordField`, `mlieBracket_coordField`,
   `leviCivita_coordField`
12. Lightlike/Spacetime/ChartCovariant.lean - `contMDiffAt_cov`, `hat`, `cov0`, `cov0_isCov`
13. Lightlike/Spacetime/ChartCurvature.lean - `gamHat`, `mdiffAt_gamHat`, `hat_cov`, `hv_bracket`,
   `Rhat`, `curvature_hat`, `curvatureAt_apply_proved`
14. Lightlike/Spacetime/CurvatureSymmetries.lean - `bianchi_first_proved`, `riemannLowerAt_antisymm_last`,
   `riemannLowerAt_pair_symm`, `ricciAt_symm_proved`
15. Lightlike/Spacetime/ChartAgreement.lean - `riemann_coord_comp`, `ricciAt_coord`, `scalarCurvatureAt_coord`,
   `satisfiesEinstein_iff_chart_proved`
16. Lightlike/Spacetime/BianchiSecond.lean - `bianchi_second_proved`
17. Lightlike/Spacetime/ChartTensor.lean - `covDerivBilinAt_bilOf`, `covDerivBilinAt_einstein`: the covariant derivative of a bilinear field in chart components (tensorial); smoothness of the coordinate Riemann, Ricci, scalar and Einstein tensors. Step 1 for the task T-GE1-P8.
18. Lightlike/Spacetime/ContractedBianchi.lean - `covR_cyc`, `einstein_div_coord`: the second Bianchi identity in coordinates and its double contraction.
19. Lightlike/Spacetime/DivergenceFree.lean - `einstein_divergence_free_proved`: the divergence of the Einstein tensor of a Levi-Civita connection vanishes.

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 3.
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
