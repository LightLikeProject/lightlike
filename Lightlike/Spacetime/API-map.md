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

For a coordinate metric the contracted Bianchi identity holds, `g^{στ} ∇_σ G_{τν} = 0` for the coordinate Einstein tensor [18], and for the Levi-Civita connection of a Lorentzian metric on a manifold the divergence of the Einstein tensor vanishes [19]; the Einstein equations with a cosmological constant and a source, and in dimension other than two the vacuum equations are `Ric = 0` [23].

A Lorentzian coordinate metric on an open subset of `ℝⁿ` is a Lorentzian metric on that open subset as a manifold, with the same components in every chart [20]; exterior Schwarzschild on the manifold layer satisfies the vacuum Einstein equations and has vanishing Ricci tensor [21]; the Levi-Civita connection of a Lorentzian metric is a smooth covariant derivative [22].
The volume measure of a Lorentzian metric on a manifold is the pushforward of `√|det g| dx` in each chart, and for a set in a chart domain it is given by the integral over its chart image in any chart [24].

The coordinate components and the volume measure are defined for a smooth symmetric nondegenerate bilinear field on the tangent bundle, a metric of any signature, of which a Lorentzian metric and a smooth Riemannian metric of Mathlib are the two cases; the coordinate matrix of a Riemannian metric is positive definite [25]. On an open subset of Euclidean space, a coordinate metric of any signature is a metric of the open subset with the same components in every chart, and the volume of a measurable set is the integral of the square root of the absolute value of the determinant over its image [26].

A Lorentzian metric extends this structure, and the Levi-Civita connection, the curvature symmetries, the second Bianchi identity, the divergence of the Einstein tensor and the Einstein equations are stated and proved for it, so they hold for every metric of every signature [7].

The curvature of a manifold-level metric as a tensor field is defined in `Connection.lean` [7]: a connection is Mathlib's
covariant derivative on the tangent bundle; the Riemann curvature is `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`
(the sign convention of a Mathlib proposal, <https://github.com/leanprover-community/mathlib4/pull/45069>), the Ricci tensor is its trace over the first slot, the scalar
curvature its trace with the metric, the Levi-Civita connection is the torsion-free connection compatible with `g`, and the Einstein
equations with cosmological constant are `Ric - (S/2) g + Λ g = 0` [7]; the covariant derivative of the curvature and of a field of bilinear forms, the divergence and the Einstein tensor `Ric - (S/2) g` are defined there too [7]. These are definitions only: the existence and
uniqueness of the Levi-Civita connection, the independence of the curvature from the extensions, its symmetries, and the
agreement with the coordinate curvature of [1] in every chart are stated as proof tasks `T-GE1-P2` to `T-GE1-P8` (including the second and contracted Bianchi identities and Minkowski space as a solution)
(`Tasks/GE/`), with open proofs, except the last: on `ℝⁿ` the flat connection `∇_v Y = DY(v)` is a torsion-free connection compatible with the Minkowski metric with zero curvature, so Minkowski space satisfies the Einstein equations with `Λ = 0` [8]. [TODO]

The Lie derivative of the metric along a vector field, `(L_X g)(V, W) = X(g(V, W)) - g([X, V], W) - g(V, [X, W])`, equals `g(∇_V X, W) + g(V, ∇_W X)` for the Levi-Civita connection (metric compatibility and vanishing torsion), so a field is a Killing field, `g(∇_v X, w) + g(v, ∇_w X) = 0`, exactly when `L_X g = 0` [27]. The bracket of two Killing fields is Killing, so the Killing fields form a Lie algebra [28]. In Minkowski space the affine fields `y -> A y + c` with `A` skew for the metric are Killing, the dilation is not, and their brackets are again of this form with the Poincare relations [29]. Every `C²` Killing field of Minkowski space is of this form, so the Killing fields form a vector space of dimension `n (n + 1) / 2` [61]. Conversely, the generator `X = ∂_sΦ(0, ·)` of a `C²` one-parameter family `Φ(s, ·)` of maps preserving the metric satisfies Killing's equation `DG(X)(u, w) + G(DX u, w) + G(u, DX w) = 0` in coordinates [44].

For a non-null hypersurface given as a level set of a function, with unit normal `n`, the extrinsic curvature `K(v, w) = g(∇_v n, w)` is symmetric on tangent vectors, the Levi-Civita connection splits on tangent fields as `∇_Y Z = D_Y Z - ε K(Y, Z) n`, and the tangential and normal components of the curvature are the Gauss relation `g(R(X, Y) Z, W) = g(R^D(X, Y) Z, W) - ε (K(Y, Z) K(X, W) - K(X, Z) K(Y, W))` and the Codazzi relation `g(R(X, Y) Z, n) = -((D_X K)(Y, Z) - (D_Y K)(X, Z))` [30]. Contracted in an orthonormal basis `(n, E_a)` of the tangent space, `g(E_a, E_b) = η_a δ_ab`, they give the constraints: `2 G(n, n) = -ε R^D + K² - K_ab K^ab` (Hamiltonian) and `G(n, E_c) = Σ_a η_a ((D_{E_a} K)(E_c, E_a) - (D_{E_c} K)(E_a, E_a))` (momentum), with `G` the Einstein tensor [47].

The first variation of the Einstein-Hilbert density in coordinates: for a smooth metric `g` and a smooth symmetric perturbation `h` on `R^n`, the metric `g + t h` has volume density with derivative `1/2 sqrt(|g|) g^{ab} h_{ab}` [31], Christoffel symbols with the derivative `delta Gamma` [32], and curvature with first variation given by the linearised Riemann tensor [35] [36]; the contraction `g^{sigma nu} delta R_{sigma nu}` times the volume density is the divergence of `sqrt(|g|) W^rho` with `W^rho = g^{sigma nu} delta Gamma^rho_{sigma nu} - g^{rho sigma} delta Gamma^kappa_{kappa sigma}` (the Palatini identity [33] [34] [37]), so that the density `sqrt(|g|) (R - 2 Lambda)` has the first variation `-sqrt(|g|) (R^{ab} - R g^{ab}/2 + Lambda g^{ab}) h_{ab}` plus a divergence [37]. The divergence of a compactly supported field integrates to zero and the density is differentiable under the integral over a compact region, so the first variation of the integral over a compact region containing the support of the perturbation is `-∫ sqrt(|g|) (R^{ab} - R g^{ab}/2 + Lambda g^{ab}) h_{ab}`, with no boundary term [38]. That the critical points are the vacuum Einstein equations and the statement on a manifold are not yet proved. [TODO]

A metric is a critical point of the Einstein-Hilbert action with a cosmological term, for every smooth symmetric perturbation of compact support, exactly when it satisfies the vacuum Einstein equations with that cosmological constant, by the first variation and the fundamental lemma of the calculus of variations [39]. In two dimensions the Einstein tensor vanishes identically, so every metric is critical for the action without cosmological term [40].

A smooth metric of any signature on the product of the time line and three-dimensional space for which the three spatial translations and the three spatial rotations are Killing fields has `g_{0k} = 0` and `g_{ij}` a function of the time times `delta_{ij}`, the flat FLRW form [62]. For every spatial curvature `k`, the three rotations and the three curved translations `Pₘ = (1 - k|x|²/4)∂ₘ + (k/2)xₘ(x · ∂)` as Killing fields on the set `1 + k|x|²/4 > 0` give there the FLRW form `b(t) dt² + a(t) δ/(1 + k|x|²/4)²`, with the slices in isotropic coordinates [63]. The local flow of a Killing field preserves the metric [64]. Along the orbits of finitely many Killing fields whose brackets close with constant structure constants, the metric pulled back by the flow solves a linear equation in the structure constants alone, so two such families with the same structure constants and proportional Gram matrices at a point have proportional metrics along their orbits [65]: the first part of the step from abstract homogeneous and isotropic slices to these coordinates. On `ℝ³` the curved translations and the rotations are Killing for the space form `δ/(1 + k|x|²/4)²` and close with explicit structure constants [66]; so a metric with Killing fields of these structure constants whose rotations vanish at a point is, in the orbit chart `η ↦ exp(∑ ηₘ Pₘ)(p)`, a constant multiple of the space form in its own orbit chart [67]. If the rotations vanish along a worldline `c`, then in the chart `Φ(t, ξ) = exp(∑ ξₑ Yₑ)(c t)` the metric is `b(t) dt² + a(t) δ/(1 + k|x|²/4)²` with `b(t) = g(c', c')`: the cross terms vanish because the rotations fix the velocity of `c`, and the time-time component is constant along the orbits [68]. The passage from an isometry group to such a Killing algebra is not yet proved. [TODO]

In Minkowski space, an observer who travels out and back along two straight segments ages less
than one who stays at rest [6].

The focusing lemma for the Riccati inequality: a function on `0 ≤ s < L` with `Θ' ≤ -Θ²/m` (`m > 0`) and `Θ(0) < 0` has `L ≤ m/|Θ(0)|`, the analytic step of geodesic focusing from Raychaudhuri's equation [49].

Raychaudhuri's equation in coordinates: for a smooth field `v` geodesic on an open set of a coordinate metric, with `∇_b vᵃ = ∂_b vᵃ + Γᵃ_{bc} vᶜ` and the expansion `Θ = ∇ₐ vᵃ`, `v(Θ) = -(∇_b vᵃ)(∇ₐ vᵇ) - R_{σν} vᵠ vᵛ`; where `g(v, v) = -1`, splitting `∇v` into expansion, shear `σ` and rotation `ω` gives `v(Θ) = -Θ²/(n-1) - σ² + ω² - R(v, v)` [50] [51] [52]. For a unit geodesic field (`g(v, v) = -1` on the open set), along an integral curve for parameters `0 ≤ s < L` that starts converging, `R(v, v) + σ² - ω² ≥ 0` gives `L ≤ (n-1)/|Θ(0)|`; for a Lorentzian metric the shear term is nonnegative, so a rotation-free congruence with `R(v, v) ≥ 0` focuses [53] [54]. On a manifold, for the Levi-Civita connection and a smooth vector field `V` geodesic near `x`, `V(Θ) = -tr((∇V)²) - Ric(V, V)` with `Θ = tr(∇V)`, proved in the chart at `x` from the coordinate identity [55]. For a Lorentzian metric and a unit geodesic `V`, rotation-free (`g(∇_u V, w) = g(∇_w V, u)`) with `Ric(V, V) ≥ 0`, `V(Θ) ≤ -Θ²/(n-1)`, and along an integral curve of `V` for `0 ≤ s < L` with `Θ(γ(0)) < 0`, `L ≤ (n-1)/|Θ(γ(0))|` [55]. For a null geodesic field `k` with an auxiliary null `N` (`g(k, N) = -1`) and the screen metric `h = g + k♭ N♭ + N♭ k♭`, projecting `∇k` onto the screen gives `k(Θ) = -Θ²/(n-2) - σ̂² + ω̂² - R(k, k)` [58] [59]; for a Lorentzian metric `σ̂² ≥ 0`, so a null field with `ω̂ = 0` (true for a rotation-free one) and `R(k, k) ≥ 0` focuses within `(n-2)/|Θ(0)|`, in coordinates and on a manifold [59] [60].

The null, weak, strong and dominant energy conditions are stated pointwise for a symmetric bilinear form on a Lorentzian vector space; dust with non-negative density satisfies all four, a positive cosmological constant violates the strong one, and a scalar field with negative potential at a point of vanishing gradient violates the weak one [43]. On a Lorentzian 4-manifold the four conditions hold for a stress-energy field at every point; for a perfect fluid they take the effective forms, and under the Einstein equations they are equivalent to the geometric forms on the Ricci and Einstein tensors [45]. For a perfect fluid the tensor conditions are Physlib's effective conditions on a cosmic fluid at c = 1 [46]. The electromagnetic field satisfies the weak, dominant and strong conditions, through a Lorentz frame started by any unit timelike vector [48].

The divergence theorem on a manifold: for a metric of any signature, its Levi-Civita connection, a smooth vector field `X` vanishing outside a compact set and a measurable domain `D` given near every point of its closure by a defining function (`D = {u ≥ 0}`, `du ≠ 0` where `u = 0`), `∫_D div X d vol_g` is the flux of `X` through the boundary of `D`, written with a partition of unity subordinate to charts and graph charts of the boundary in each chart; a density `f · dV_g` is the case of the field `f X` [57]. In a chart, `√|g| ∇ₐXᵃ = ∂ⱼ(√|g| Xʲ)`, and the theorem in `ℝⁿ⁺¹` needs its hypothesis only on the support of the field [56] [57].

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
20. Lightlike/Spacetime/OpenCoordMetric.lean - `openMetric`, `openMetric_coordMetric`: a Lorentzian coordinate metric on an open set as a Lorentzian metric on the manifold, and the bridge.
21. Lightlike/Spacetime/SchwarzschildManifold.lean - `schwarzschildMetric`, `schwarzschild_coordMetric`, `schwarzschild_satisfiesEinstein`, `schwarzschild_ricci_eq_zero`: exterior Schwarzschild on the manifold layer.
22. Lightlike/Spacetime/LeviCivitaSmooth.lean - `contMDiffCovariantDerivative_leviCivita`: the Levi-Civita connection of a Lorentzian metric is smooth.
23. Lightlike/Spacetime/EinsteinEquations.lean - `satisfiesEinstein_iff_ricci`, `satisfiesEinstein_zero_iff_ricci_eq_zero`: the vacuum Einstein equations with a cosmological constant are Ricci proportional to the metric, and Ricci-flat for no cosmological constant.
24. Lightlike/Spacetime/VolumeMeasure.lean - `volumeMeasure`, `volumeMeasure_chart`, `volumeMeasure_minkowski`: the volume measure of a Lorentzian metric, its chart formula and the Minkowski trust check.
25. Lightlike/Spacetime/NondegMetric.lean - `NondegMetric`, `NondegMetric.coordMetric`, `NondegMetric.ofRiemannian_coordMetric_posDef`: smooth symmetric nondegenerate bilinear fields on a manifold, the Lorentzian and the Riemannian metrics as cases, and the coordinate components with their tensor properties.
26. Lightlike/Spacetime/NondegOpen.lean - `openNondeg`, `openNondeg_coordMetric`, `openNondeg_volumeMeasure`: a coordinate metric of any signature on an open subset of Euclidean space as a metric of the open subset, the coordinate components in every chart, and its volume measure.
27. Lightlike/Spacetime/LieMetric.lean - `lieDerivMetric`, `IsKillingAt`, `lieDerivMetric_symm`, `lieDerivMetric_zero`, `lieDerivMetric_eq_of_isLeviCivita`, `isKillingAt_iff_lieDerivMetric_eq_zero`: the Lie derivative of a metric of any signature along a vector field, and for the Levi-Civita connection its equality with the symmetrised covariant derivative of the field, so that the Killing equation says the Lie derivative of the metric vanishes.
28. Lightlike/Spacetime/KillingAlgebra.lean - `IsKillingNear`, `mlieBracket_jacobi`, `lieDerivMetric_lieBracket`, `IsKillingNear.lieBracket`: the bracket of two Killing fields of a metric of any signature is Killing (the Jacobi identity and the bracket formula for derivatives of functions).
29. Lightlike/Spacetime/PoincareKilling.lean - `affField`, `affField_killing_iff`, `not_isKillingAt_dilation`, `mlieBracket_affField`, `skew_comm_skew`: in Minkowski space the affine fields with skew linear part are Killing, the dilation is not, and the affine fields close under the bracket with the Poincare relations.
30. Lightlike/Spacetime/Hypersurface.lean - `Hypersurface.IsUnitNormal`, `Hypersurface.IsTangentNear`, `Hypersurface.secondFF`, `Hypersurface.lieBracket_isTangentNear`, `Hypersurface.secondFF_symm_fields`, `Hypersurface.exists_tangent_extension`, `Hypersurface.Dfield`, `Hypersurface.gaussCurv`, `Hypersurface.covK`, `Hypersurface.gauss_relation`, `Hypersurface.codazzi_relation`: the unit normal and second fundamental form of the level sets of a function, its symmetry, and the Gauss and Codazzi relations.
31. Lightlike/Spacetime/VariationDet.lean - `hasDerivAt_det_add_smul`, `hasDerivAt_sqrt_abs_det_add_smul`, `hasDerivAt_inv_add_smul`, `fderiv_inv_entry`: Jacobi's formula for the determinant, the variation of the volume density and the derivative of the matrix inverse.
32. Lightlike/Spacetime/VariationChristoffel.lean - `hasDerivAt_christoffel_add_smul`: the variation of the Christoffel symbols of the perturbed metric.
33. Lightlike/Spacetime/PalatiniAlgebra.lean - `palatini_alg_nd`, `palatini_dd`: the algebra of the Palatini identity, finite sums only.
34. Lightlike/Spacetime/VariationInverse.lean - `pd_inv_eq`, `pd_sqrt_abs_det`, `hasDerivAt_det_path`, `hasDerivAt_sqrt_abs`: the derivatives of the inverse metric and of the volume density in coordinates.
35. Lightlike/Spacetime/VariationExchange.lean - `hasDerivAt_fderiv_exchange`, `contDiffAt_christoffel_family`, `dChristoffel`, `hasDerivAt_pd_christoffel`: exchange of the variation and a partial derivative.
36. Lightlike/Spacetime/VariationRiemann.lean - `hasDerivAt_riemann`, `dRicci`, `hasDerivAt_ricci`, `hasDerivAt_scalarCurvature`: the first variation of the Riemann, Ricci and scalar curvature in coordinates.
37. Lightlike/Spacetime/PalatiniCoord.lean - `Wvec`, `palatini_coord`, `ricciUp`, `hasDerivAt_lagrangian`: the Palatini identity in coordinates and the first variation of the Einstein-Hilbert density at a point.
38. Lightlike/Spacetime/VariationIntegral.lean - `lagDensity`, `contDiffAt_lagDensity`, `hasDerivAt_integral_family`, `integral_pd_eq_zero`, `contDiff_flux`, `eh_first_variation`: the Einstein-Hilbert density is smooth in the perturbation parameter and the point, and the first variation of its integral over a compact region containing the support of the perturbation is the Einstein tensor plus cosmological term contracted with the perturbation.
39. Lightlike/Spacetime/VariationCritical.lean - `einsteinUp`, `IsEHCritical`, `contDiff_ricci`, `contDiff_scalarCurvature`, `isEHCritical_iff`: a smooth nondegenerate metric is a critical point of the Einstein-Hilbert action, for perturbations of compact support, if and only if it satisfies the vacuum Einstein equations with a cosmological constant.
40. Lightlike/Spacetime/EinsteinTwoDim.lean - `ricci_two_dim`, `einsteinUp_two_dim`, `isEHCritical_two_dim`: in two dimensions the Ricci tensor is half the scalar curvature times the metric, the Einstein tensor vanishes, and every smooth nondegenerate metric is a critical point of the Einstein-Hilbert action without cosmological term.
41. Lightlike/Spacetime/CoordKilling.lean - `coordField_killing`: a coordinate field along which the metric components are constant is a Killing field (`IsKillingAt`) of the Levi-Civita connection.
42. Lightlike/Spacetime/SchwarzschildKilling.lean - `schwarzschild_killing`: the time translation `∂_t` is a Killing field of exterior Schwarzschild.
43. Lightlike/Spacetime/EnergyConditions.lean - `NullEC`, `WeakEC`, `StrongEC`, `DominantEC`, `dust_energyConditions`, `cosmo_energyConditions`, `scalar_negative_potential_violates_weak`: the pointwise energy conditions of a stress-energy tensor on a Lorentzian vector space and their trust checks.
44. Lightlike/Spacetime/IsometryKilling.lean - `fderiv_apply_inr_of_id`, `killing_of_isometry_family`, `killing_of_isometry_family_on`: the generator of a one-parameter family of isometries is a Killing field, in coordinates.
45. Lightlike/Spacetime/EnergyConditionsField.lean - `LorentzianMetric.NullECField`, `LorentzianMetric.fluidField_dominantEC_iff`, `LorentzianMetric.nullECField_iff_ricci`, `LorentzianMetric.strongECField_iff_ricci`, `LorentzianMetric.dominantECField_iff_einstein`: the energy conditions of a stress-energy field on a Lorentzian 4-manifold, the perfect-fluid forms, and the equivalence of the physical and geometric forms under the Einstein equations.
46. Lightlike/Spacetime/EnergyConditionsPhyslib.lean - `fluid_nullEC_iff_physlib`, `fluid_weakEC_iff_physlib`, `fluid_strongEC_iff_physlib`, `fluid_dominantEC_iff_physlib`: for a perfect fluid the tensor energy conditions are Physlib's effective energy conditions on a cosmic fluid at c = 1.
47. Lightlike/Spacetime/HypersurfaceConstraints.lean - `curvatureAt_linear`, `ricciAt_frame`, `scalarCurvatureAt_frame`, `exists_frame`, `hamiltonian_constraint`, `momentum_constraint`: the Hamiltonian and momentum constraints from the contracted Gauss and Codazzi relations.
48. Lightlike/Spacetime/EnergyConditionsEM.lean - `exists_frame_of_timelike`, `em_weakEC`, `em_dominantEC`, `em_strongEC_of_eq`, `emT_traceless`: every unit timelike vector starts a Lorentz frame; the electromagnetic field satisfies the weak, dominant and strong energy conditions.
49. Lightlike/Spacetime/RiccatiFocusing.lean - `focusing`: the focusing lemma for the Riccati inequality.
50. Lightlike/Spacetime/RaychaudhuriAlgebra.lean - `Raychaudhuri.raychaudhuri_algebra`: the index computation of the Raychaudhuri identity (fable1).
51. Lightlike/Spacetime/RaychaudhuriCoord.lean - `covD`, `expansion`, `covDMat`, `shear`, `rotation`, `pd_covD`, `raychaudhuri_coord`, `raychaudhuri_equation`: Raychaudhuri's identity and equation for a geodesic field in coordinates.
52. Lightlike/Spacetime/RaychaudhuriSplit.lean - `Raychaudhuri.normSqG`, `Raychaudhuri.trace_sq_split`: the trace of the square of the derivative of a geodesic field splits into expansion, shear and rotation.
53. Lightlike/Spacetime/RaychaudhuriFocusing.lean - `covD_orthogonal`, `IsLorentzianCoordMetric.orthogonal_nonneg`, `focusing_along`, `raychaudhuri_convergence`, `shear_normSq_nonneg`, `raychaudhuri_focusing_at`, `raychaudhuri_focusing`: convergence and focusing of a unit timelike geodesic field along its integral curves.
54. Lightlike/Spacetime/RaychaudhuriShear.lean - `Raychaudhuri.trace_mul_nonneg`, `Raychaudhuri.normSqG_nonneg`, `Raychaudhuri.spacelike_complement`, `Raychaudhuri.orthogonal_nonneg_of_lorentzian`: the square of a spatial symmetric tensor is nonnegative.
55. Lightlike/Spacetime/RaychaudhuriManifold.lean - `chartComp`, `hv_cov_eq`, `trace_eq_of_hv`, `ricciAt_hv`, `g_hv`, `rotation_chart_eq_zero`, `expansionM`, `expansionDeriv`, `mfderiv_expansionM`, `raychaudhuri_manifold`, `raychaudhuri_leviCivita`, `raychaudhuri_focusing_manifold_at`, `raychaudhuri_focusing_manifold`: the Raychaudhuri identity and geodesic focusing for a vector field on a manifold.
56. Lightlike/Spacetime/EHManifold/LocalDivergence.lean - `exists_graph_atlas_integral_divergence_loc`, `exists_graph_atlas_integral_divergence_of_defining_function_loc`: the divergence theorem in ℝⁿ⁺¹ with the hypothesis on the support of the field.
57. Lightlike/Spacetime/EHManifold/ManifoldDivergence.lean - `sqrt_det_mul_expansion`, `divField`, `contDiff_divField`, `integral_expansionM_chart`, `chart_defining_function`, `exists_chart_flux`, `expansionM_sum`, `divergence_theorem_manifold`, `divergence_theorem_manifold_density`: the divergence theorem on a manifold.
58. Lightlike/Spacetime/RaychaudhuriNullAlg.lean - `Raychaudhuri.trace_sq_split_proj`, `Raychaudhuri.nullScreen`, `Raychaudhuri.nullScreen_proj_sq`, `Raychaudhuri.trace_proj_conj`, `Raychaudhuri.trace_proj_conj_sq`, `Raychaudhuri.nullShear_mulVec`: the split over a screen projector and the null screen.
59. Lightlike/Spacetime/RaychaudhuriNull.lean - `covD_orthogonal_of_const`, `nullProj`, `nullB`, `nullShear`, `nullRotation`, `raychaudhuri_null_equation`, `nullShear_normSq_nonneg`, `nullRotation_eq_zero`, `raychaudhuri_null_focusing_at`, `raychaudhuri_null_focusing`: Raychaudhuri's equation and focusing for a null geodesic field in coordinates.
60. Lightlike/Spacetime/RaychaudhuriNullManifold.lean - `screenProj`, `nullRotation_chart_eq_zero`, `raychaudhuri_null_focusing_manifold_at`, `raychaudhuri_null_focusing_manifold`: null geodesic focusing on a manifold.
61. Lightlike/Spacetime/KillingMinkowski.lean - `eq_affine_of_skew_deriv`, `killing_eq_affField`, `finrank_skewEta`, `finrank_killingFields`: every `C²` Killing field of Minkowski space is affine with an η-skew linear part, and the Killing fields form a space of dimension `n (n + 1) / 2`.
62. Lightlike/Spacetime/HomogeneousIsotropic.lean - `lieDerivMetric_affField_basis`, `spatial_const`, `rotCLM`, `flat_flrw_of_killing`: the Lie derivative of the metric on the coordinate basis fields, and the flat FLRW form of a metric of any signature on four-dimensional space with the spatial translations and rotations as Killing fields.
63. Lightlike/Spacetime/HomogeneousIsotropicCurved.lean - `lieDerivMetric_basis`, `curvTrans`, `ray_relation`, `curved_flrw_of_killing`: for every curvature k, the rotations and the curved translations as Killing fields give the FLRW form `b(t) dt² + a(t) δ/(1 + k|x|²/4)²`.
64. Lightlike/Spacetime/KillingFlow.lean - `killing_flow_isometry`, `flow_transport`: the local flow of a Killing field preserves the metric, and transports fields whose brackets with it close.
65. Lightlike/Spacetime/KillingOrbit.lean - `suspField`, `fderiv_susp_flow`, `hasDerivWithinAt_gram`, `orbitData`, `hasDerivWithinAt_orbitData`, `orbit_comparison`: along the orbits of Killing fields with constant structure constants the metric solves a linear equation in the structure constants.
66. Lightlike/Spacetime/SpaceFormKilling.lean - `SpaceForm.metric`, `SpaceForm.P`, `SpaceForm.R`, `SpaceForm.X`, `SpaceForm.S`, `SpaceForm.lieBracket_X`, `SpaceForm.killing_P`, `SpaceForm.killing_R`: the Killing algebra of the space form of curvature k in isotropic coordinates and its structure constants.
67. Lightlike/Spacetime/KillingOrbitChart.lean - `gram_of_isotropy`, `fderiv_susp_flow_zero`, `isometric_spaceForm`: a homogeneous and isotropic 3-metric is, in orbit charts, a constant multiple of the space form of curvature k.
68. Lightlike/Spacetime/KillingOrbitFLRW.lean - `pairing_zero_of_isotropy`, `orbit_time_data`, `flrw_of_killing_algebra`: a metric with a Killing algebra of the space-form type whose rotations vanish along a worldline has the FLRW form in the orbit chart.

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 3.
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
