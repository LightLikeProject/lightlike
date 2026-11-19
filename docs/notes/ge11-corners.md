# GE11 on manifolds with corners: what is proved, and how it compares with the task text and the source

State (18 November 2026): the chain of T-GE1 P2-P8 (chart curvature, symmetries, second Bianchi identity, chart agreement, the divergence-free
Einstein tensor, smoothness of the Levi-Civita connection, the Einstein equations as Ricci proportional to the metric) is stated for any
`ModelWithCorners`, with derivatives of the coordinate expressions taken within `range I`. No Mathlib gap was found. Pieces used:
`ContDiffWithinAt.isSymmSndFDerivWithinAt` (mixed partial derivatives commute at points of the closure of the interior; `range I` is the closure
of its interior), `ContDiffWithinAt.fderivWithin_right`, `fderivWithin_inter`, `extChartAt_target_mem_nhdsWithin_of_mem`, and the new
`mvfderiv_eq_chart_at` (chain rule in the chart at `x₀` at any point of its domain, within `range I`).

## Weaker than the task text, not than the source (the maintainers, 20:02)
* The coordinate layer is for the model `Fin n → ℝ`; the manifold layer (`ChartCovariant` to `CurvatureSymmetries`, `EinsteinEquations`) is for any
  finite-dimensional `E`. Follow-up task: transport the coordinate layer along a continuous linear equivalence `E ≃L Fin n → ℝ`.
* `VolumeMeasure` keeps `[T2Space M]` and is boundaryless. Follow-up task: the measure of a metric on a manifold with corners.
* Both are not weaker than the source (Carroll, *Lecture Notes on General Relativity*, ch. 2-3; Wald, *General Relativity*, ch. 2-3: manifolds
  locally `ℝⁿ`, boundaryless, Hausdorff). Comparison pending: those sections have not been read at page and equation level, so no row that rests on
  them is closed.

## Comparison with the source: pending
Locations to read before any GE11 row is closed: Carroll ch. 3 (curvature, Bianchi identities, the Einstein tensor and `∇^μ G_{μν} = 0`),
Wald ch. 3 (Riemann tensor, Bianchi identities) and ch. 4 (Einstein equation). Nothing is claimed as matching until the equation numbers are recorded here.

## Follow-up tasks (not partials: weaker than the task text only, the maintainers, 20:02)
1. **Generic model space `E` for the coordinate layer.** The coordinate files (`Curvature`, `RiemannSymmetryWithin`, `ContractedBianchiWithin`, `ChartConnection`, `ChartAgreement`, `ChartTensor`, `DivergenceFree`,
   `LeviCivitaSmooth`) are for `I : ModelWithCorners ℝ (Fin n → ℝ) H`; the manifold layer is for any finite-dimensional `E`. Plan: Mathlib's `ModelWithCorners.transContinuousLinearEquiv` turns a model on `E` into one on
   `Fin n → ℝ` (used in `FLRWModel.lean` for `J × S³`); what is missing is the transport of a `NondegMetric`, a connection and its curvature along the change of model (derivatives transport by
   `hasMFDerivAt_transContinuousLinearEquiv` and `…_right` in `ModelTransport.lean`; the smoothness of the transported bilinear field needs the bundle trivialisation API used in `PullbackForm.lean`).
2. **The volume measure on manifolds with corners.** `VolumeMeasure.lean` keeps `[T2Space M]` and the boundaryless model; the measure of a Lorentzian metric on a manifold with boundary is not attempted.

## The Corners layer (rebuild on main 40b14699, 19 November 2026)

The generalisation to any model with corners no longer edits the boundaryless chart layer: the fifteen files of
`Lightlike/Spacetime/` it had changed (`BianchiSecond`, `ChartAgreement`, `ChartConnection`, `ChartCovariant`,
`ChartCurvature`, `ChartTensor`, `Coordinates`, `Curvature`, `CurvatureSymmetries`, `DivergenceFree`, `EinsteinEquations`,
`LeviCivitaSmooth`, `LieDerivation`, `SchwarzschildManifold`, `VolumeMeasure`) are main's, unchanged, and the general
versions that the CO30 and GE11 files use are in `Lightlike/Spacetime/Corners/`, one file per source file, in namespace
`Lightlike` with a `W` suffix on every name the boundaryless layer owns (a sub-namespace would break dot notation such
as `g.coordMetric`). Only what those files use was moved: the transitive closure of the constants of the CO30 and GE11
files, computed in Lean from the environment. `Corners/EinsteinChart.lean` (`einsteinEq_iff_chartW`) replaces the
branch's `Spacetime/EinsteinChart.lean`, whose name and path the FLRW-slice entry uses for the boundaryless statement.
`Corners/Bridge.lean` proves that for the model `𝓘(ℝ, Fin n → ℝ)` the two layers agree: the chart and tangent
trivializations, the coordinate fields and the components of a vector field by definition, the coordinate metric
(`NondegMetric.coordMetricW_eq_coordMetric`) through `mfderivWithin_univ`, and the chart-derivative lemma.

What moved (source file: declarations, with the new name where it changed):

* `ChartAgreement.lean` (29): `gramB` → `gramBW`, `gramB_isUnit` → `gramB_isUnitW`, `coord_eq_sum_basis` → `coord_eq_sum_basisW`, `raise` → `raiseW`, `g_raise` → `g_raiseW`, `trace_raise` → `trace_raiseW`, `hv_curvatureAt` → `hv_curvatureAtW`, `gamHat_coord` → `gamHat_coordW`, `mvfderiv_gamHat_apply` → `mvfderiv_gamHat_applyW`, `mvfderiv_gamHat_coord` → `mvfderiv_gamHat_coordW`, `hv_coordField` → `hv_coordFieldW`, `symmL_eq_coordField` → `symmL_eq_coordFieldW`, `riemann_coord_comp` → `riemann_coord_compW`, `Rhat_add_left` → `Rhat_add_leftW`, `Rhat_smul_left` → `Rhat_smul_leftW`, `Rhat_add_mid` → `Rhat_add_midW`, `Rhat_smul_mid` → `Rhat_smul_midW`, `Rhat_add_right` → `Rhat_add_rightW`, `Rhat_smul_right` → `Rhat_smul_rightW`, `RhatFst` → `RhatFstW`, `ricciAt_eq_trace` → `ricciAt_eq_traceW`, `ricciAt_coord` → `ricciAt_coordW`, `hv_smul'` → `hv_smul'W`, `RhatFst_add_mid` → `RhatFst_add_midW`, `RhatFst_smul_mid` → `RhatFst_smul_midW`, `RhatFst_add_right` → `RhatFst_add_rightW`, `RhatFst_smul_right` → `RhatFst_smul_rightW`, `RicB` → `RicBW`, `scalarCurvatureAt_coord` → `scalarCurvatureAt_coordW`.
* `ChartConnection.lean` (12): `coordField` → `coordFieldW`, `coordField_apply` → `coordField_applyW`, `mdiffAt_coordField` → `mdiffAt_coordFieldW`, `chartField_coordField` → `chartField_coordFieldW`, `mfderiv_chart_coordField` → `mfderiv_chart_coordFieldW`, `contMDiffAt_chartCoord` (new), `mfderiv_chartCoord` (new), `mlieBracket_coordField` → `mlieBracket_coordFieldW`, `g_coordField` → `g_coordFieldW`, `mvfderiv_gpair_coordField` → `mvfderiv_gpair_coordFieldW`, `eq_of_g_coordField` → `eq_of_g_coordFieldW`, `leviCivita_coordField` → `leviCivita_coordFieldW`.
* `ChartCovariant.lean` (11): `LocallySmoothConnection` → `LocallySmoothConnectionW`, `contMDiffAt_cov` → `contMDiffAt_covW`, `tTriv` → `tTrivW`, `hat` → `hatW`, `mdiffAt_hat_iff` → `mdiffAt_hat_iffW`, `hat_add` → `hat_addW`, `hat_smul` → `hat_smulW`, `cov0` → `cov0W`, `symmL_hat` → `symmL_hatW`, `mvfderiv_congr` → `mvfderiv_congrW`, `cov0_isCov` → `cov0_isCovW`.
* `ChartCurvature.lean` (32): `cfield` → `cfieldW`, `hat_cfield` → `hat_cfieldW`, `contMDiffAt_cfield` → `contMDiffAt_cfieldW`, `contMDiffAt_clm_of_apply` → `contMDiffAt_clm_of_applyW`, `contMDiffAt_clm_of_apply_infty` → `contMDiffAt_clm_of_apply_inftyW`, `gam` → `gamW`, `gam_apply` → `gam_applyW`, `gamHat` → `gamHatW`, `gamHat_apply` → `gamHat_applyW`, `cov0_cfield` → `cov0_cfieldW`, `gamHat_eq` → `gamHat_eqW`, `contMDiffAt_gamHat_apply` → `contMDiffAt_gamHat_applyW`, `mdiffAt_gamHat` → `mdiffAt_gamHatW`, `mvfderiv_eq_chart` → `mvfderiv_eq_chartW`, `mvfderiv_eq_chart_at` (new), `mdiffAt_comp_symm` → `mdiffAt_comp_symmW`, `mvfderiv_clm_apply` → `mvfderiv_clm_applyW`, `hv` → `hvW`, `hv_symmL` → `hv_symmLW`, `symmL_hv` → `symmL_hvW`, `hv_add` → `hv_addW`, `hat_cov` → `hat_covW`, `mvfderiv_clm_comp` → `mvfderiv_clm_compW`, `hv_bracket` → `hv_bracketW`, `deriv_comm_E` → `deriv_comm_EW`, `hv_sub` → `hv_subW`, `Rhat` → `RhatW`, `contMDiffAt_covApply` → `contMDiffAt_covApplyW`, `hat_covApply` → `hat_covApplyW`, `mdiffAt_DY` → `mdiffAt_DYW`, `curvature_hat` → `curvature_hatW`, `eventually_extend` → `eventually_extendW`.
* `ChartTensor.lean` (3): `IsCoordMetricW.contDiffOn_riemannW` (new), `IsCoordMetricW.contDiffOn_ricciW` (new), `IsCoordMetricW.contDiffOn_scalarCurvatureW` (new).
* `Coordinates.lean` (10): `chartTriv` → `chartTrivW`, `symm_mem_chartTriv_baseSet` → `symm_mem_chartTriv_baseSetW`, `mfderiv_extChartAt_symm_eq` → `mfderiv_extChartAt_symm_eqW`, `coordBasis` → `coordBasisW`, `coordBasis_apply` → `coordBasis_applyW`, `NondegMetric.coordMetric_eq` → `NondegMetric.coordMetric_eqW`, `NondegMetric.coordMetric_transpose` → `NondegMetric.coordMetric_transposeW`, `NondegMetric.coordMetric_isUnit_det` → `NondegMetric.coordMetric_isUnit_detW`, `NondegMetric.coordMetric_smooth` → `NondegMetric.coordMetric_smoothW`, `NondegMetric.isCoordMetricW_coordMetric` (new).
* `Curvature.lean` (1): `NondegMetric.coordMetric` → `NondegMetric.coordMetricW`.
* `CurvatureSymmetries.lean` (21): `SmoothNear` → `SmoothNearW`, `curvatureAt_apply_eventually` → `curvatureAt_apply_eventuallyW`, `smoothNear_mlieBracket` → `smoothNear_mlieBracketW`, `cov_torsion` → `cov_torsionW`, `bianchi_first_aux` → `bianchi_first_auxW`, `jacobi_cyc` → `jacobi_cycW`, `bianchi_first_proved` → `bianchi_first_provedW`, `compat_mv` → `compat_mvW`, `compat_mv'` → `compat_mv'W`, `contMDiffAt_gpair` → `contMDiffAt_gpairW`, `riemann_antisymm_aux` → `riemann_antisymm_auxW`, `riemannLowerAt_antisymm_last` → `riemannLowerAt_antisymm_lastW`, `curvatureAt_antisymm_left` → `curvatureAt_antisymm_leftW`, `riemannLowerAt_pair_symm` → `riemannLowerAt_pair_symmW`, `metricGram` → `metricGramW`, `tb` → `tbW`, `metricGram_isUnit` → `metricGram_isUnitW`, `coord_eq_sum` → `coord_eq_sumW`, `riemannLowerAt_antisymm_first` → `riemannLowerAt_antisymm_firstW`, `ricciAt_eq_sum` → `ricciAt_eq_sumW`, `ricciAt_symm_proved` → `ricciAt_symm_provedW`.
* `EinsteinEquations.lean` (1): `NondegMetric.EinsteinEq` → `NondegMetric.EinsteinEqW`.
* `LeviCivitaSmooth.lean` (5, and the `LocallySmoothConnectionW` instance for `leviCivita`): `mfderiv_chart_symmL` → `mfderiv_chart_symmLW`, `mvfderiv_chart_fixed` → `mvfderiv_chart_fixedW`, `contMDiffAt_mvfderiv_cfield` → `contMDiffAt_mvfderiv_cfieldW`, `contMDiffAt_gamHat_leviCivita` → `contMDiffAt_gamHat_leviCivitaW`, `contMDiffAt_leviCivita` → `contMDiffAt_leviCivitaW`.
* `LieDerivation.lean` (6): `dirDeriv` → `dirDerivW`, `chartField` → `chartFieldW`, `mfderiv_of_eventuallyEq_chart` (new), `mfderiv_eq_chart` → `mfderiv_eq_chartW`, `mpullback_chart` → `mpullback_chartW`, `mfderiv_mlieBracket` → `mfderiv_mlieBracketW`.
