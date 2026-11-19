# GC1: connections on a trivial bundle, curvature, holonomy

Status of 19 November 2026 (work in progress). Claim tags: MEASURED = checked in Lean or
by reading the cited location; PROXY / ASSUMPTION = stated as such.

## Source

G. Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1 (1999), read with pdftotext on 19 November 2026
(printed page numbers):

* p. 40: parallel transport solves `df^a/dt = -Σ_i Γ^a_i(x(t), f(t)) dx^i/dt`; the parallelogram `C` through
  `x_0 = x, x_1 = x + ξ, x_2 = x + ξ + η, x_3 = x + η` and back; transport along `C` is computed to second order in
  `ξ, η` as `T^{(3)}_{-η} T^{(2)}_{-ξ} T^{(1)}_η T^{(0)}_ξ`.
* p. 41: the result is `exp(R(η, ξ))` with `R(η, ξ) = dΓ(η, ξ) + [Γ(η), Γ(ξ)]` (eq. (60)), the curvature 2-form.
* p. 42: for a principal `G`-bundle the transport is `P exp(-∫ A)` and transport around `C` is, to second order,
  multiplication by `exp(F(η, ξ))`, `F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]` (eq. (62)), "defining thus a `g`-valued
  2-form in `U`"; the transition formula `F_V = g_{VU} F_U g_{VU}⁻¹` (eq. (63)).
* p. 43: under a gauge transformation `φ`, represented in a trivialisation by `φ_U(x)`, `F ↦ φ_U F φ_U⁻¹` (eq. (64)).
* pp. 29-31 (§4.6): the connection 1-form `ω` on `P G` with `ω_p(L_p) = L` (eq. (34)) and
  `ω_{p·g}(v · g) = Ad_{g⁻¹} ω_p(v)` (eq. (35)); in a trivialisation over an open `U`, with `T_h G ≃ g` by right
  translation, `ω_{(x,h)}(ξ, L) = h⁻¹ (A_U(ξ) + L) h` (eq. (36)), `A_U` "a `g`-valued 1-form on `U`", the local
  principal gauge potential; on `U ∩ V`, `A_V = g_{VU} A_U g_{VU}⁻¹ - dg_{VU} g_{VU}⁻¹` (eq. (38), p. 30); Theorem 10
  (p. 31): local potentials satisfying (38) on all overlaps define a unique invariant connection.

Where the source states its formulas: (36), (38), (62), (63) and (64) are stated in a local trivialisation over an
open set `U` of the base (MEASURED, read at the locations above); only (34), (35) and Theorem 10 are stated on the
bundle.

The source registered for GC1 earlier (Hamilton 2017, Chapter 5) was not opened; it is replaced by this one
(maintainers' decision, 19 November 2026).

## Formal statements and how they compare

* `curvature` (Connection/Basic.lean): `F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]` with `dA(η, ξ) = ∂_η A(ξ) - ∂_ξ A(η)` and
  `[a, b] = a b - b a`, the normalisation of (62) (no factor `1/2`). Setting: the trivialisation over an open set
  `U` of a normed space `E` (`Connection`: a one-form `C²` on an open `domain`), the connection an `𝔄`-valued
  one-form for a normed algebra `𝔄`; `curvature_congr`: `F` at `x` depends only on `A` near `x`. The trivial bundle
  over `U` is the source's own local form (the formulas are stated there, see above), so this part is
  representation. Difference, kind weaker: the gauge group is the group of units of a normed algebra `𝔄` with
  values of `A` in `𝔄`. For (62) alone this covers every Lie group the source allows, since a finite-dimensional
  Lie algebra embeds in some `gl(n)` (Ado), but group elements enter (38), (63) and (64), and a Lie group that is
  not a matrix group (the universal cover of `SL(2, ℝ)`) is not a group of units of a normed algebra (general Lie
  groups: next section). The bundle-level statements (34), (35) and Theorem 10 on a principal bundle over a manifold
  are in `PrincipalGlue.lean` and `PrincipalConnection.lean` (last section).
* `IsSegmentTransport` (Connection/Transport.lean): `U(0) = 1`, `U' = -A(x + tξ)(ξ) U`, the transport equation of
  p. 40 with `Γ(x, f) = A(x) f`. Existence for a short leg (Picard–Lindelöf) and uniqueness (Mathlib's
  `IsPicardLindelof`, `ODE_solution_unique_of_mem_Icc_right`); the integral equation `U = 1 - ∫ A U`.
* `squareHolonomy_pureGauge` (Connection/PureGauge.lean): the transport around the parallelogram of a pure gauge
  `A = g⁻¹ dg` is `1` (trust check: a flat connection has trivial holonomy on this contractible loop).
* `squareHolonomy_uniformField` (Connection/Abelian.lean): for `U(1)` (`𝔄 = ℂ`) the transport is `exp(-∫ A)`, and for
  the uniform field the circulation around the parallelogram is `i b det(a, b')`, so the holonomy is `exp(-i Φ)`
  with the flux `Φ = b det(a, b')` (trust check "U(1) holonomy is exp(i·flux)", with this orientation).
* `squareHolonomy_eq` (Connection/SmallLoop.lean): for a `C²` connection, any transports along the legs
  `x → x + εξ → x + εξ + εη → x + εη → x` satisfy `‖U₄U₃U₂U₁ - (1 + ε² F(η, ξ))‖ ≤ C ε³` for small `ε`: the
  milestone's "done when". Compared with Svetlichny p. 42, eq. (62) (and p. 41, eq. (60)): (62) states the transport
  around the parallelogram to second order as `exp(F(η, ξ))`, i.e. `1 + F(η, ξ) + O(3)`; the formal statement has
  the same `F(η, ξ)`, the same order of legs (`ξ` first, then `η`) and an explicit `O(ε³)` remainder. The `ε²`
  coefficient `DA(η)ξ - DA(ξ)η + A(η)A(ξ) - A(ξ)A(η)` was computed by hand from the four legs (19 November) and is
  `sum_legG_add_pairs` in Lean. Difference, kind representation: legs are straight segments in a normed space and
  the remainder is `C ε³` instead of "to second order".

* `squareHolonomy_eq_of_contDiffOn` (Connection/Local.lean): the same statement for `A` that is `C²` only on an open
  `U ∋ x`, in a space with smooth bump functions (every finite-dimensional space; the source's base is an
  `n`-dimensional manifold, p. 29): `A` agrees near `x` with a globally `C²` cutoff `χ A`, which has the same
  transports along the four legs (`IsSegmentTransport.congr`) and the same curvature at `x` (`curvature_congr`).
  This is (62) as stated, for the local potential on `U`.
* `curvature_gaugeTransform` (Connection/GaugeCovariance.lean): with `A' = g A g⁻¹ - dg g⁻¹` (eq. (38), p. 30,
  `gaugeTransform`) and `g` `C²`, `A`, `g⁻¹` differentiable on an open `U`, `F_{A'} = g F_A g⁻¹` on `U` (eq. (64),
  p. 43); `curvature_transition`: (38) on an overlap `U ∩ V` gives `F_V = g_{VU} F_U g_{VU}⁻¹` there (eq. (63),
  p. 42). The `dg` terms cancel by the symmetry of the second derivative of `g` (`isSymmSndFDerivAt`).
* `connectionForm` (Connection/Principal.lean): `ω_{(x,h)}(ξ, L) = h⁻¹ (A(x)(ξ) + L) h` on the trivial principal
  bundle (eq. (36), p. 30), in the source's right-translation coordinates `(ξ, L)`;
  `connectionForm_vertical`: `ω` is `L` on the fundamental vector of `L` (eq. (34), p. 29);
  `connectionForm_mul_right`: `ω_{(x, hg)} = g⁻¹ ω_{(x,h)} g` (eq. (35), p. 29); `connectionForm_unitSection`:
  the pullback by the unit section is `A`; `connectionForm_section_eq_gaugeTransform`: the pullback by a section
  `x ↦ (x, k(x))` over an open `U` is the gauge transform of `A` by `k⁻¹` (eq. (38)).

## General Lie groups (difference (b)): attempts

The files of this section are in `Lightlike/Gauge/LieConnection/`.

* Attempt 1 (`LieGroup.lean`, Mathlib's `LieGroup` and `GroupLieAlgebra`): `Ad_g = d(conj_g)_1`, `Ad_g` preserves the
  bracket (`mpullback_mlieBracket`), the curvature (62) with the bracket of `GroupLieAlgebra`, and (64) for a constant
  `g`. It stops at an `x`-dependent `g`, which needs `d(Ad) = ad ∘ Ad` and the Maurer–Cartan equation; neither is in
  Mathlib (Mathlib has no `Ad`), and principal `G`-bundles are in neither Mathlib nor Physlib.
* Attempt 2 (19 November 2026; `G` modelled on `𝓘(ℝ, E)` without corners, kind representation). Steps (1)-(3)
  compile: the multiplication `M(y, z) = φ(φ⁻¹y φ⁻¹z)` in the chart `φ` at `1` is `C³` (`contDiffAt_chartMul`); the
  pullback of `X_v` by `φ⁻¹` is `∂_z M(y, y₀) v`, so `⁅v, w⁆ = ∂_y(∂_z M(y, y₀) w) v - ∂_y(∂_z M(y, y₀) v) w`
  (`bracket_eq_chart`); and `D(Ad · w)_1 v = ⁅v, w⁆` (`fderiv_adjoint_chart`, from `fderiv_conj_chart`: `Dι = -id`
  and the symmetry of `D²M`). Step (4) compiles in the chart (`ChartGauge.lean`): for a `C²` path `γ` with
  `γ x₀ = y₀`, `∂_η (Ad_{g(x)} a(x)) = Da(η) + ⁅Dγ η, a x₀⁆` (`fderiv_conjApply_chart`) and the Maurer–Cartan
  equation `∂_η θ(ξ) - ∂_ξ θ(η) = ⁅Dγ η, Dγ ξ⁆` for `θ(x)(ξ) = ∂M(γ x, ι(γ x))(Dγ(x) ξ, 0)` (`maurerCartan_chart`: the
  second derivative of `γ` cancels by symmetry, `∂₁∂₁M(·, y₀) = 0`, `Dι = -id`, and the mixed partials of `M` give
  the bracket). Step (5) (`LieGroupGauge.lean`): `rightMCForm` (`dg g⁻¹ = d(R_{g⁻¹}) ∘ dg`) and `lieGaugeTransform`
  (eq. (38)), their chart forms (`rightMCForm_eq_chart`, `eventually_adjointE_eq`), the covariance (64) at a point
  where `g = 1` (`lieCurvature_lieGaugeTransform_of_chart`), and under a left translation `g ↦ g₀ g`
  (`rightMCForm_mul_left`, `lieGaugeTransform_mul_left`), so **(64) holds for every `C²` gauge transformation of a
  general Lie group** (`lieCurvature_lieGaugeTransform`). Attempt 2 succeeds for the point-dependent `g`. The
  bundle-level statements (principal bundles, Theorem 10) are recorded separately below.

## Principal bundles and Theorem 10 (p. 31): attempts

Theorem 10: for a principal `G`-bundle `π : P → X` with trivializations `h_U` over an open cover and `g`-valued
1-forms `A_U` satisfying (38) on the overlaps, there is a unique invariant connection on `P` whose representatives are
the `A_U`.

* Attempt 1 (19 November 2026; `P` through Mathlib's fiber bundles, `FiberBundle G P` with the coordinate changes
  `(x, h) ↦ (x, g_VU(x) h)`). It stops before the connection can be stated: an invariant connection is a `g`-valued
  1-form `ω` on `TP` (eqs. (34)-(36)), so `P` must be a manifold, and Mathlib has no smooth structure on such a total
  space. Its charted space on a fiber bundle (`FiberBundle.chartedSpace'`, `Geometry/Manifold/VectorBundle/Basic.lean`,
  line 82) takes the model fiber itself as the chart target `B × F`, so the fiber must be a model space; a Lie group
  `G` is a manifold, not a model space, and the composition with the charts of `G` is not provided. The only
  manifold structure on a total space (`Bundle.TotalSpace.isManifold`, same file, line 467) is built on the groupoid
  `contMDiffFiberwiseLinear`, i.e. for fiberwise linear coordinate changes, which left multiplication on `G` is not.
  Mathlib has no principal bundles (no file mentions them), and Physlib's gauge-theory API map lists the principal
  bundle and its connection as `[TODO]` (`ClassicalFieldTheory/GaugeTheory/API-map.md`, line 15). Missing piece, by
  name: a charted space and `IsManifold` instance on the total space of a fiber bundle whose fiber is a manifold and
  whose coordinate changes are smooth in the product charts.
* Attempt 2 (19 November 2026; genuinely different: `P` glued from the pieces `U_i × G` with its own charted space,
  without `FiberBundle`; `PrincipalGlue.lean`, `PrincipalConnection.lean`). A `PrincipalCocycle` is an open cover
  `U_i` of `M` with transition maps `g_ij` satisfying `g_ii = 1` and `g_jk g_ij = g_ik`. Mathlib's
  `TopCat.GlueData.MkCore` glues the spaces `U_i × G` along `(x, h) ↦ (x, g_ij(x) h)` (the source's `ψ_VU`, p. 30)
  into `P` (`total`); the pieces are open (`isOpenEmbedding_incl`), and two points of the pieces agree in `P` exactly
  when their base points agree and `h' = g_ij(x) h` (`incl_eq_iff`). The chart of `P` at a point is a local
  trivialization `h_i` followed by a chart of `M × G`; the chart changes are the transition maps (`transition_eq`), so
  `P` is a `C^n` manifold modelled on `M × G` when the `g_ij` are `C^n` (`isManifold`, `isManifold_of_contMDiffOn`),
  with `C^n` trivializations (`contMDiffOn_localTriv`, `contMDiffOn_localTriv_symm`) and the right action
  `h_i⁻¹(x, h) · k = h_i⁻¹(x, h k)` (`act`, `act_incl`, `localTriv_act`). This is the missing piece named in attempt
  1, built for the principal bundle. On this `P`, with `G` a `C³` Lie group modelled on a real Banach space without
  boundary: `localForm` is (36), `ω_(x,h)(ξ, w) = Ad_{h⁻¹}(A(x) ξ + dR_{h⁻¹} w)`; under (38) (`IsCompatible`,
  `A_j = Ad_{g_ij} A_i - dg_ij g_ij⁻¹`) the local forms agree through the derivative of the transition maps
  (`localForm_transition`, eq. (37)); the glued form `connForm` on the tangent spaces of `P` has the representative
  `ω^{U_i}` in every trivialization (`connForm_localTriv_symm`), is invariant, `ω_{p·k}(dR_k v) = Ad_{k⁻¹} ω_p(v)`
  (`connForm_act`, eq. (35)), gives `ω(d(p ·)_1 L) = L` on the fundamental vectors (`connForm_vertical`, eq. (34)),
  and is the only form with these representatives (`connForm_unique`). Attempt 2 succeeds: Theorem 10 holds for the
  glued principal bundle. Differences, kind representation: `P` is given by the transition data of its
  trivializations (`g_VU = h_V ∘ h_U⁻¹`, the data the source uses in (37) and (38)) rather than as an abstract bundle
  with trivializations, which Mathlib does not have; the identification `T_h G ≃ g` by `dR_{h⁻¹}` (p. 30) is written
  out inside `localForm`; the fundamental vector of `L` is `d(p ·)_1 L` and (34) is stated at `p · 1`, which is `p`
  (`act_one`). Smoothness (`PrincipalSmooth.lean`): if `G` and the `g_ij` are `C^n` with `n ≥ 3` and each `A_i` is a
  `C^m` one-form on `U_i` with `m + 1 ≤ n`, then `ω` is a `C^m` section of Mathlib's hom bundle `Hom(TP, g)`
  (`contMDiff_connForm`, from the chart form `connForm_contMDiffAt`: near a point `ω` is written through one
  trivialization, `connForm_eq_of_mem`; the tangent coordinates of `M × G` split, `tangentCoordChange_prod`; and the
  derivatives of the group operations are `C^m` in coordinates, `contMDiffAt_rightTrivial_coord`,
  `contMDiffAt_adjointE_inv`, from Mathlib's `ContMDiffAt.mfderiv`); for smooth data the form is smooth. Differences,
  kind representation: a `C^m` one-form `A_i` is given by its expression in the charts of `M`
  (`x ↦ A_i(x) ∘ tangentCoordChange` is `C^m` near each point of `U_i`, which is Mathlib's criterion
  `contMDiffAt_hom_bundle` for sections of the hom bundle); `G` also carries the `C³` Lie group structure of the
  adjoint action (`minSmoothness ℝ 3 ≤ n`), and the `C¹` structures of the tangent bundles are passed as instances.

The vector-bundle form of Theorem 10 is a separate result (`BundleConnection.lean`), not an attempt at `P`: a `C¹`
vector bundle `V` with model fiber `F` over a manifold (structure group `GL(F)`); a local potential in a
trivialization `e` of the atlas is an `End(F)`-valued one-form `A`, and `∇σ = e⁻¹(dσ_e + A σ_e)` (`localCov`) is a
covariant derivative on the base set (`localCov_isCovariantDerivativeOn`). With the coordinate change `g = e' ∘ e⁻¹`
(`coordChangeL`), (38) makes the two local covariant derivatives agree on the overlap (`localCov_eq_of_mem`), so local
potentials on trivializations covering `M` that satisfy (38) on every overlap are the representatives of a covariant
derivative (`exists_covariantDerivative_of_local`), unique on the sections differentiable at the point
(`covariantDerivative_eq_of_local`).

## Reuse

Mathlib: `IsPicardLindelof`, `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, `ContDiffBump`,
`ContDiffAt.isSymmSndFDerivAt`, `Filter.EventuallyEq.fderiv_eq`, `ODE_solution_unique_of_mem_Icc_right`,
`integral_eq_sub_of_hasDeriv_right_of_le`, `integral_hasDerivAt_right`, `fderiv_mul'`, `TopCat.GlueData.MkCore`,
`TopCat.GlueData.ι_eq_iff_rel`, `symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn`, `contMDiffOn_of_mem_maximalAtlas`,
`mfderiv_prodMk`, `mfderiv_prod_eq_add_apply`, `Filter.EventuallyEq.mfderiv_eq`, `ContMDiffAt.mfderiv`,
`contMDiffAt_hom_bundle`, `inTangentCoordinates_eq`, `tangentCoordChange_comp`; no connections on principal bundles
in Mathlib. Physlib: `ElectromagneticPotential`, `toFieldStrength` (U(1) on Minkowski space) and
`LocalGaugeData`; its holonomy and parallel transport are TODO there. Tau Ceti: not checked.
