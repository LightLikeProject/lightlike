# Connections, curvature and holonomy on a trivial bundle

## Abstract (Alpha)

This API treats a connection on a trivial bundle over a normed space with values in a normed algebra (a gauge
potential of a matrix group), its curvature 2-form and its parallel transport, following Svetlichny's
*Preparation for Gauge Theory*. The curvature is normalised as in the source: `F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]`, and all statements are on the
open set of a trivialisation, where the source states them.

## Content (Alpha)

A connection is a one-form `A` on an open set `U` of a normed space `E` with values in a normed algebra `𝔄`, `C²` on
`U` (the local principal gauge potential of a trivialisation over `U`, Svetlichny p. 30 {1}), and its curvature is
`F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]` with `dA(η, ξ) = ∂_η A(ξ) - ∂_ξ A(η)`, the normalisation of eq. (62) {1}. The
curvature is antisymmetric, local, and for commuting values (the abelian case, `U(1)`) it is `dA` [1]. Parallel
transport along a segment solves `U' = -A(x + tξ)(ξ) U`, `U(0) = 1`; it exists for short legs and is unique [2]. A
pure gauge has trivial holonomy around the parallelogram [3], and for `U(1)` the holonomy of a uniform field is the
exponential of `-i` times the flux [4]. The transport around the parallelogram `x, x + εξ, x + εξ + εη, x + εη` is
`1 + ε² F(η, ξ) + O(ε³)` (eq. (62)) for `A` `C²` on all of `E` [5] and for `A` `C²` on an open `U ∋ x` in a space
with smooth bump functions [6]. Under the gauge transformation `A ↦ g A g⁻¹ - dg g⁻¹` (eq. (38)) the curvature
transforms as `F ↦ g F g⁻¹` (eqs. (63), (64)), on `U` and on overlaps `U ∩ V` [7]. On the trivial principal bundle the
connection 1-form `ω_{(x,h)}(ξ, L) = h⁻¹ (A(ξ) + L) h` (eq. (36)) satisfies (34) and the invariance (35), and its
pullbacks by sections are the gauge transforms of `A` [8]. The gauge group is the group of units of `𝔄`; gauge
transformations for a general Lie group are in the Lie connection API. On a `C¹` vector bundle over a manifold
(structure group `GL(F)`), `d + A_U` in each trivialization is a covariant derivative, (38) on the overlaps makes them
agree, and local potentials satisfying (38) are the representatives of a covariant derivative, unique on
differentiable sections [9]. For a Lie group `G` (Mathlib's `LieGroup`, modelled on a real Banach space without
boundary), a principal `G`-bundle `P` over a manifold `M` is glued from the pieces `U_i × G` along `(x, h) ↦ (x,
g_ij(x) h)` for transition maps with `g_ii = 1` and `g_jk g_ij = g_ik`; it is a `C^n` manifold modelled on `M × G`
when the `g_ij` are `C^n`, its local trivializations are `C^n`, and `G` acts on the right [10]. Local potentials `A_i`
satisfying (38) define, through the local forms (36), a connection form on the tangent spaces of `P` whose
representative in every trivialization is the given one; it is invariant (35), reproduces the Lie algebra on vertical
vectors (34), and is the only form with these representatives (Theorem 10, p. 31) [11]. When `G` and the transition
maps are `C^n` (`n ≥ 3`) and the potentials are `C^m` one-forms with `m + 1 ≤ n`, the form is a `C^m` section of
`Hom(TP, g)`, so smooth data give a smooth form [12].

## Lean References

1. Lightlike/Gauge/Connection/Basic.lean - `Gauge.Connection`, `Gauge.curvature`, `Gauge.curvature_antisymm`,
   `Gauge.curvature_congr`, `Gauge.curvature_of_commute`
2. Lightlike/Gauge/Connection/Transport.lean - `Gauge.IsSegmentTransport`, `Gauge.exists_segmentTransport`,
   `Gauge.segmentTransport_unique`, `Gauge.IsSegmentTransport.eq_one_sub_integral`
3. Lightlike/Gauge/Connection/PureGauge.lean - `Gauge.pureGauge`, `Gauge.isSegmentTransport_pureGauge`,
   `Gauge.squareHolonomy_pureGauge`
4. Lightlike/Gauge/Connection/Abelian.lean - `Gauge.lineIntegral`, `Gauge.isSegmentTransport_abelian`,
   `Gauge.squareHolonomy_abelian`, `Gauge.uniformField`, `Gauge.squareHolonomy_uniformField`
5. Lightlike/Gauge/Connection/SmallLoop.lean - `Gauge.squareHolonomy_eq`
6. Lightlike/Gauge/Connection/Local.lean - `Gauge.IsSegmentTransport.congr`, `Gauge.exists_contDiff_eqOn_ball`,
   `Gauge.squareHolonomy_eq_of_contDiffOn`
7. Lightlike/Gauge/Connection/GaugeCovariance.lean - `Gauge.gaugeTransform`, `Gauge.curvature_gaugeTransform`,
   `Gauge.curvature_transition`
8. Lightlike/Gauge/Connection/Principal.lean - `Gauge.connectionForm`, `Gauge.connectionForm_vertical`,
   `Gauge.connectionForm_mul_right`, `Gauge.connectionForm_unitSection`,
   `Gauge.connectionForm_section_eq_gaugeTransform`
9. Lightlike/Gauge/Connection/BundleConnection.lean - `Gauge.localCov`, `Gauge.localCov_isCovariantDerivativeOn`,
   `Gauge.localCov_eq_of_mem`, `Gauge.exists_covariantDerivative_of_local`, `Gauge.covariantDerivative_eq_of_local`
10. Lightlike/Gauge/Connection/PrincipalGlue.lean - `Gauge.PrincipalCocycle`, `Gauge.PrincipalCocycle.mkCore`,
   `Gauge.PrincipalCocycle.total`, `Gauge.PrincipalCocycle.isOpenEmbedding_incl`, `Gauge.PrincipalCocycle.incl_eq_iff`,
   `Gauge.PrincipalCocycle.localTriv`, `Gauge.PrincipalCocycle.transition_eq`, `Gauge.PrincipalCocycle.isManifold`,
   `Gauge.PrincipalCocycle.isManifold_of_contMDiffOn`, `Gauge.PrincipalCocycle.contMDiffOn_localTriv`,
   `Gauge.PrincipalCocycle.contMDiffOn_localTriv_symm`, `Gauge.PrincipalCocycle.act`, `Gauge.PrincipalCocycle.act_incl`,
   `Gauge.PrincipalCocycle.localTriv_act`
11. Lightlike/Gauge/Connection/PrincipalConnection.lean - `Gauge.PrincipalCocycle.localForm`,
   `Gauge.PrincipalCocycle.IsCompatible`, `Gauge.PrincipalCocycle.localForm_transition`,
   `Gauge.PrincipalCocycle.connForm`, `Gauge.PrincipalCocycle.connForm_localTriv_symm`,
   `Gauge.PrincipalCocycle.connForm_unique`, `Gauge.PrincipalCocycle.connForm_act`,
   `Gauge.PrincipalCocycle.connForm_vertical`
12. Lightlike/Gauge/Connection/PrincipalSmooth.lean - `Gauge.tangentCoordChange_prod`,
   `Gauge.PrincipalCocycle.contMDiffAt_rightTrivial_coord`, `Gauge.PrincipalCocycle.contMDiffAt_adjointE_inv`,
   `Gauge.PrincipalCocycle.contMDiffAt_localForm_coord`, `Gauge.PrincipalCocycle.connForm_eq_of_mem`,
   `Gauge.PrincipalCocycle.connForm_contMDiffAt`, `Gauge.PrincipalCocycle.contMDiff_connForm`

## References

1. G. Svetlichny, Preparation for Gauge Theory, arXiv:math-ph/9902027 (1999), §4.6 pp. 29-31 (eqs. (34)-(38), Theorem 10)
   and pp. 40-43 (eqs. (60), (62)-(64)).
