# Stationary phase for the Lorentzian EPRL vertex

## Abstract (Alpha)

This API sets up the stationary phase analysis of the Lorentzian EPRL vertex amplitude in
coherent boundary states. For one triangle it gives the action at the level of spinors, shows
that its real part is at most zero with the maximum exactly at proportional spinors, and derives
the first critical relation. At a vertex, stationarity in the group variables is closure of the
normals, and the critical relation for SU(2) group elements holds exactly when two normals agree.
The second variation of the triangle factor is computed along a line and along the group
variation. With SU(2) group elements the critical points are the gluing points of the Euclidean
theory, and under the nondegeneracy hypotheses of the Euclidean classification they form two
classes. For group elements in SL(2, C), the critical equations (20) and (21) of the source with the spinor z
eliminated are a predicate on the group elements; parity `X -> (X^dagger)^-1` is an involution that
exchanges the two equations and so preserves the critical set, it is the identity on SU(2), and
for SU(2) the predicate is the Euclidean gluing condition. A stationary phase theorem for integrals of `e^{τ S}` with `Re S ≤ 0` is derived from the oscillatory
form. The existence and classification of critical points outside SU(2) and the asymptotic formula
of the vertex are not covered.

## Content (Alpha)

The setting is that of Barrett, Dowdall, Fairbairn, Hellmann and Pereira {1}, Section 4. For one
triangle, with spinors `Z = X_a† z` and `Z' = X_b† z`, the antilinear structure `jMap`, the
weight `triWeight` (the modulus of `e^S`) and the complex action `triAction` are defined [1].
The weight is at most one, so `Re S ≤ 0`, and it equals one exactly at proportional spinors [1].
Eliminating `z` gives the first critical relation, eq. (20) of {1} [1]. A maximal and a
non-maximal example check the definitions [1].

Stationarity in the group variables uses the triangle factor `triFactor` for a doubled spin
`n = 2k` and its derivative along `X ↦ X exp(tL)` with `L` in `sl₂(ℂ)`, at the source and at the
target end of a triangle [2]. The vertex condition is `Σ n_e n̂_e = 0` and `Σ p_e n̂_e = 0`, and
for `p = γk` it is closure of the normals, with `γ` dropping out [2]. A configuration of two
opposite triangles is stationary, and a single triangle is not [2].

For unit spinors, `2|⟨x,y⟩|² = ‖x‖²‖y‖² + n(x)·n(y)`, so unit spinors with equal normals differ
by a phase [3]. For SU(2) group elements the relation `A⁻¹ξ = c B⁻¹Jξ'` with a unit `c` holds
exactly when the normals of `A⁻¹ξ` and `B⁻¹Jξ'` agree [3]. The spin vector of the first column of
a matrix is its Bloch vector, so on an edge this relation is exactly the gluing condition of the
Euclidean theory, equal Bloch vectors of the two frames [5]. The critical points with SU(2) group
elements are therefore the Euclidean gluing points, and given the two reference solutions and the
independence hypotheses of the Euclidean classification they are exactly the two classes
`X_a = ±X₄` and `X_a = ±X₄ Q₄† Q_a` [5]. A twisted data set has the critical point `X = 1`, and
parallel instead of antiparallel normals do not [5].

For group elements in SL(2, C), the critical equations (20) and (21) of {1} with `z` eliminated
are the predicate `IsLorCritical`. Parity `X -> (X^dagger)^-1` is an involution, the identity on
SU(2) exactly, and it exchanges the two equations, so it preserves the critical set; `J` carries
`X` to `(X^dagger)^-1`, eq. (33) of {1} [6]. For SU(2) group elements the predicate is the
Euclidean gluing condition and then the two equations agree with `r = 1` [6]. Parity is not the
identity on a boost, the twisted data have the critical point `X = 1`, and parallel normals do
not [6]. Critical points outside SU(2) are not covered.

The second derivative of the triangle factor along `Z + tW` is `triFactor · (ℓ² + H)`, with `ℓ`
the log derivative and `H = -n (⟨W,ξ⟩/⟨Z,ξ⟩)² - (n + 2ip)(‖W‖²/‖Z‖² - 2 (Re⟨Z,W⟩)²/‖Z‖⁴)` [4]. Under
the group variation `X ↦ X exp(tL)` at `Z ∥ ξ`, with `c = β + iα`, this becomes
`-n (½ c·n̂)² - (n + 2ip)(¼(|β|² + |α|² + 2 (β×α)·n̂) - 2 (½ β·n̂)²)`, using
`4‖L†ξ‖² = Σ|c_i|² + 2 (β×α)·n̂` [4]. A rotation and a boost about the axis of a spinor give
`-ip/2` and `+ip/2` [4].

The stationary phase theorem for `a e^{τ S}` with `Re S ≤ 0` on the support of `a`, a finite set of
critical points where `-∂²S` is invertible, in any dimension, has the sum of `e^{τ S(x₀)}
(2π/τ)^{n/2} (det(-∂²S(x₀)))^{-1/2} a(x₀)` as leading term with error `O(τ^{-n/2-1})` [7]. A
Gaussian is the example, and the opposite sign violates `Re S ≤ 0` [7].

With a weight `w(λ) = O(λ^m)` and an amplitude split into a compactly supported part and a remainder
whose integral is assumed to be `O(λ^{-n/2-1})`, the integral `w(λ) ∫ A e^{λ S}` is the weight
times the sum over the critical points, with error `O(λ^{m-n/2-1})` [8]. The remainder bound is a
hypothesis, not proved, and it holds trivially for a zero remainder [8]. The global smoothness of the
action in these statements cannot hold for the Lorentzian action (logarithms of the overlaps and
norms): the local version needs smoothness only on an open set containing the support of the
localised amplitude, by a smooth cutoff of the action [32]. The action of a smooth chart is smooth on every open set where,
on each edge, the product of the overlaps is off the cut of the logarithm [33]. A chart of `SL(2,ℂ)` near the identity with the tangent map
`X ↦ X exp(M)` of BDFHP Appendix A is the Cayley transform `((1 + s) 1 + M)/(1 - s)`, `s = c·c/16`, of
`M = ½ Σ c_i σ_i`: determinant one, value `1` and derivative `M` at `0`, smooth entries where `s ≠ 1`
[34]; Mathlib has no `det exp = exp tr`. The 44-variable chart (`X_a = X₀_a · cayley (φ_a + iθ_a)` for
`a < 4`, `z_e = (w₀_e + u_e + i v_e, 1)`) is smooth where the four Cayley denominators are nonzero, and
the vertex asymptotics hold in it with the smoothness hypothesis replaced by that open set and the
overlap condition; the Haar density and the identification of the vertex integral with the chart
integral stay named hypotheses (`aLoc`, `aFar`) [35]. Along `t ↦ t v` the chart has the tangent map
`X_a ↦ X₀_a · chartGen (φ_a + iθ_a)`, `z_e ↦ (u_e + i v_e, 0)` [35]. The two-point formula with the
constants of eq. (57) holds for an action smooth only on an open set [36]. The Haar measure of
`SL(2,ℂ)` is Lebesgue measure in the chart `g_z` of `FixedChart.lean` (density `1`), so, if the
integrand is jointly integrable, the vertex is `(∏ c_e) s⁻⁴` times the Lebesgue integral of the
integrand over `(ℂ³)⁴ × ℂ¹⁰` [37]; through a measure-preserving identification with `ℝ⁴⁴` the vertex of the
scaled data is `(∏ c_e) s⁻⁴ ∫ a(x) e^{λ S(x)} dx` with the `λ`-independent amplitude `a = ∏ Ω_e` [37]. The chart `fixVertexChart` is smooth where the
`λ`-coordinates are nonzero, and the asymptotic formula for the scaled vertex holds in it with the
cutoff split `a = χ a + (1 - χ) a`; the named hypotheses (joint integrability, `hK`, `hdet`, `hint`,
`hfar`, the weight bound) are those of the statement [38]; `hint` is assumed only along `λ ∈ ℕ` (the form `∀ τ : ℝ` fails for `τ < 0`
where an overlap vanishes). The numerical factor of BDFHP eq. (57) and its second line for `p = γ k`
are in [39]. For boundary data whose normals do not close at a node `a < 4`, the weighted vertex integral in the fixed charts
is `O(λ^{m-N})` for every `N`: the differential of the chart `g_0` is onto the tangent space, so at a point with
`Re S = 0` (an aligned point) the derivative of the pulled-back action along a suitable chart direction is the sum of
the logarithmic derivatives of the ends at the node, which does not vanish; `Re S ≤ 0`, the smoothness of the action
and the absence of critical points are proved, and the far remainder stays under `hint` and `hfar` [40].

The vertex action `lorAction` is the sum of the triangle actions over the ten edges at the spinors
`X†z` [9]. Its real part is at most zero where the spinors and overlaps are nonzero [9]. In a chart
of any dimension, with the pulled-back action smooth, the formula of the previous paragraph holds
with the Hessian of the pulled-back action; the chart, the Haar density of the amplitude, the
finiteness of the critical set and the remainder bound are hypotheses, and the explicit constants
of the source are not computed [9].

When no point of the support has a critical point (`Re S < 0` or `dS ≠ 0` at each point), the
integral `∫ a e^{τ S}` decays faster than every power of `τ`, and with the remainder bound for
every order the weighted integral is `O(λ^{m-N})` for every `N` [10]. This is the suppression of
the source without critical points, in a chart; the remainder bound is a hypothesis.

For two critical points with opposite phases `±iθ` and a weight `c λ^m` the integral is
`λ^{m-n/2}` times `A₁ e^{iλθ} + A₂ e^{-iλθ}` up to `O(λ^{m-n/2-1})`, with `A_i` built from the
Hessian determinant, the amplitude and `c`; that these are the constants of the source is a
hypothesis [8]. A Gaussian on the line is the example: all hypotheses hold and the leading term is
`(2π/τ)^{1/2}`. The statement with the Hessian sign reversed, or with any other leading constant,
is false [11]. With the two constants interchanged, the formula cannot hold as well when
`sin θ ≠ 0` and the constants differ, by a lemma that `sin(nθ) → 0` forces `sin θ = 0` [11]. Dropping `Re S ≤ 0` also breaks
the conclusion: for `S = +x²/2` with the bump amplitude the integral stays above `∫ a > 0`, so no
constant gives the order `τ^{-3/2}` [11].

The shape of the constant of eq. (57), `sign · (2π)^{n/2} · multiplicity · (det(-∂²S))^{-1/2} ·
Π 2 k c Ω`, is the definition `eq57Constant`. The two-point formula holds with these constants when
the amplitude at each critical point, times the weight constant, equals `sign · multiplicity ·
Π f_e`; this identification, the reading of `det H` of the source as `det(-∂²S)`, the Haar density
and the closed Hessian are hypotheses or open [12]. The source writes `√(det H)` with `H` the
Hessian of `S` and no branch; `det H = det(-H)` for even `n` but the branch of the root still differs
between the two readings, which a control on `ℂ²` shows, and for odd `n` the determinants differ [11].

When the normals at a vertex do not close, the first variation of the action in the group directions
is nonzero at every point with `Re S = 0`, so the pointwise condition of the suppression holds and
the weighted integral is `O(λ^{m-N})` for every `N` (the suppression of eq. (56)). This uses two
named hypotheses, that the chart's tangent space contains the group variations and that the
remainder bound holds for every order, and it excludes the single vector geometry of eq. (55),
where the normals close. Two opposite triangles close, and one triangle does not [13].

The vertex amplitude itself is written with the fifth `SL(2, ℂ)` element fixed to `1` and the chart
`z = (w, 1)` of each `ℂP¹`; its integrand is measurable, bounded by the product of the densities of
`Ω` wherever no overlap vanishes, and each density is integrable on `ℂ` [14]. The finiteness of the
whole integral is not proved here; the action is in the power form, so its exponential is the
EPRL integrand for every doubled spin; at an odd doubled spin and a point where the logarithm of
the earlier form changes branch, the two forms differ by `-1`, and the bound `|e^S| ≤ 1` fails
for a negative spin [15].
Towards the identification with the finite principal-series vertex, the lowest SU(2) level of the
principal series on a coherent state is the `n`-th power of a linear form, and for `2k = n` the
exponential of the action is the product of the overlap power, the real power of the norms and
the imaginary power of their ratio, and one link of the principal-series vertex, with the boundary
spinors `ξ = first column of ḡ₁` and `ξ' = first column of w g₂`, is `e^S` times the density of `Ω` [16].
The sum over the links and the Fubini step, hence the identity of the two amplitudes, are not proved yet.
One link as an integral over the chart is proved: the contraction of the EPRL matrix coefficients
`D_{m m'}(a⁻¹ b)` with coherent coefficients equals `(‖A e₀‖²)⁻¹ ∫_ℂ e^S / (‖Z‖² ‖Z'‖²) dw` [17], with
`‖A e₀‖² = π/(n+1)` for the lowest level, from the Beta integral `∫₀^∞ u^n (1+u)^{-n-2} du = 1/(n+1)`
[18] and the polar integral over `ℂ` [19]; a numerical check of the identity and of the constant
is `scripts/asymptotics/link_integral_check.py`.
Assembling the ten links, the coherent principal-series vertex equals the Lorentzian vertex up to the
explicit factor `(haarScalarFactor haarC SL2C.haar)^4`, which comes from the chart measure of the
finite vertex; the outer integral of the Lorentzian vertex is therefore finite, and the value of one
link at spin zero is `π` [20].
The inner integral over `ℂ^10` also converges at every point of `SL(2, ℂ)^5`, as a product over the ten
edges of functions bounded by the density of `Ω`, so the Lorentzian vertex of the coherent data is a
genuine integral [21].
The asymptotic formula with two critical points is proved as a reduction: the amplitude of the scaled
data minus `λ^{m - n/2} (A₁ e^{iλθ} + A₂ e^{-iλθ})` is `O(λ^{m - n/2 - 1})` under named hypotheses (a
chart representation of the amplitude, the two critical points, the Hessians, the far-field decay and
the constants of eq. (57)), none of which is proved here [22]; these hypotheses are consistent, as a
model phase with two nondegenerate critical points shows [23]. The Hessian at the SU(2) critical
point of the regular simplex is numerically nondegenerate, with margin about 0.15 in the Fubini–Study
frame (`scripts/asymptotics/lorentzian_hessian_check.py`).
The oscillation frequency of eq. (53), `γ Σ k Θ` with the dihedral boost angles of a symmetric Lorentzian
4-simplex (four spins on one tetrahedron, six others; the type 4-1 signs), reproduces to the published
digits the four frequencies fitted to the numerical amplitude of Donà–Fanizza–Sarno–Speziale
(`scripts/asymptotics/lorentzian_regge_frequency_check.py`); this is a numerical check of the
statement, not a proof.
For a configuration satisfying the z-eliminated critical equations (20), (21), the spinors
`z_e = (X_a†)⁻¹ ξ_ab` give `Z_ab = ξ_ab` and `Z_ba = r c J ξ_ba`, and the real part of the action
attains its maximum `0` there [24]. On such an edge the derivative of the triangle factor along a
variation `δz` (which moves both spinors at once) vanishes by (21) alone, and the group variations
sum to zero by closure at each node [25]; the passage from these line derivatives to the gradient of
the chart action is not made. The derivative of `triAction` itself along a curve is the same
expression where the product of the overlaps is off the cut of the logarithm [26]. Along any curve through a critical configuration with
the critical spinors, the derivative of `lorAction` is zero when closure holds at every node [27];
the curves are given by their entrywise derivative `X₀ · genMat c`, and the Fréchet derivative of
`lorChartAction` is not identified here. The second derivative along a one-parameter subgroup of one
node, with the other elements and the spinors fixed, is the sum over the ends at the node of the end
formula `endForm` [29] [28]: the block `H^{X_a X_a}` of BDFHP Appendix A, equal to a quarter of eq. (61)
at source ends (the printed blocks correspond to the generators `iσ`, `σ`) and different from (61) at
target ends, where the sign of the parameter `p` and a term `m·(α×β)` appear; checked against the
independent `44 × 44` numerics to `2·10⁻¹⁹` (`scripts/asymptotics/lorentzian_hessian_node_check.py`). The blocks `H^{zz}` (in the
Wirtinger entries `zzWirtinger`) and `H^{Xz}` (`xzSource`, `xzTarget`) are proved without criticality [29]
and checked at non-critical configurations (`scripts/asymptotics/lorentzian_hessian_noncritical_check.py`).
The mixed second derivatives along two different nodes or two different spinors vanish, and the
`44 × 44` matrix `hessBlockMatrix` assembled from the blocks is symmetric [30]; its identification with the
matrix of second derivatives in a chart is not proved. Conversely, at a configuration with `Re S = 0` every edge is aligned
(`Z_ab = λ ξ_ab`, `Z_ba = μ J ξ_ba`), the first derivative along a curve `X_a Y(t)` is the sum of the logarithmic
derivatives of the ends at `a`, and stationarity along every such curve gives the closure `Σ n_e n̂_e = 0` at each node:
there is no critical configuration for boundary data without closure [31]. The suppression of the integral for such
data (BDFHP eq. (56)) needs this in a chart and is not proved.

## Lean References

1. Lightlike/Asymptotics/Lorentzian/Action.lean - `Asymptotics.Lorentzian.triWeight_le_one`,
   `Asymptotics.Lorentzian.triWeight_eq_one_iff`, `Asymptotics.Lorentzian.norm_exp_triAction`,
   `Asymptotics.Lorentzian.exists_critical_relation`, `Asymptotics.Lorentzian.jMap_jMap`,
   `Asymptotics.Lorentzian.inner_jMap_self`, `Asymptotics.Lorentzian.triWeight_eq_one_example`,
   `Asymptotics.Lorentzian.triWeight_lt_one_example`
2. Lightlike/Asymptotics/Lorentzian/Stationary.lean -
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_gen`,
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_gen_target`,
   `Asymptotics.Lorentzian.stationary_iff`, `Asymptotics.Lorentzian.stationary_iff_closure`,
   `Asymptotics.Lorentzian.spinVec_jMap`
3. Lightlike/Asymptotics/Lorentzian/Critical.lean - `Asymptotics.Lorentzian.two_norm_inner_sq`,
   `Asymptotics.Lorentzian.phase_iff_spinVec_eq`, `Asymptotics.Lorentzian.su2_relation_iff`
4. Lightlike/Asymptotics/Lorentzian/Hessian.lean - `Asymptotics.Lorentzian.hasDerivAt_lineLogDeriv`,
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_line`,
   `Asymptotics.Lorentzian.hasDerivAt_deriv_triFactor_line`,
   `Asymptotics.Lorentzian.norm_adjoint_gen_sq`, `Asymptotics.Lorentzian.hessLine_group`
5. Lightlike/Asymptotics/Lorentzian/Classification.lean -
   `Asymptotics.Lorentzian.spinVec_firstCol`, `Asymptotics.Lorentzian.glued_iff_phase`,
   `Asymptotics.Lorentzian.isSU2Critical_iff_glued`,
   `Asymptotics.Lorentzian.isSU2Critical_iff_two_classes`
6. Lightlike/Asymptotics/Lorentzian/Parity.lean - `Asymptotics.Lorentzian.parityMap`,
   `Asymptotics.Lorentzian.coe_parityMap`, `Asymptotics.Lorentzian.parityMap_parityMap`,
   `Asymptotics.Lorentzian.parityMap_ofSU2`, `Asymptotics.Lorentzian.parityMap_eq_self_iff`,
   `Asymptotics.Lorentzian.jMap_spinAct`, `Asymptotics.Lorentzian.IsLorCritical`,
   `Asymptotics.Lorentzian.isLorCritical_parity`,
   `Asymptotics.Lorentzian.isLorCritical_ofSU2_iff`
7. Lightlike/Asymptotics/Lorentzian/ExpPhase.lean - `Asymptotics.Lorentzian.hessMat_const_mul`,
   `Asymptotics.Lorentzian.expPhase_asymptotics`, `Asymptotics.Lorentzian.gaussAction_re_nonpos`,
   `Asymptotics.Lorentzian.wrongSign_re_pos`
8. Lightlike/Asymptotics/Lorentzian/VertexFormula.lean - `Asymptotics.Lorentzian.weighted_asymptotics`,
   `Asymptotics.Lorentzian.hfar_zero`, `Asymptotics.Lorentzian.weighted_two_points`
9. Lightlike/Asymptotics/Lorentzian/Vertex.lean - `Asymptotics.Lorentzian.lorAction`,
   `Asymptotics.Lorentzian.re_triAction_le_zero`, `Asymptotics.Lorentzian.re_lorAction_le_zero`,
   `Asymptotics.Lorentzian.lorChartAction`, `Asymptotics.Lorentzian.lorHessian`,
   `Asymptotics.Lorentzian.lorVertex_asymptotics`, `Asymptotics.Lorentzian.lorAction_zero`
10. Lightlike/Asymptotics/Lorentzian/Suppression.lean - `Asymptotics.Lorentzian.expPhase_suppressed`,
    `Asymptotics.Lorentzian.weighted_suppressed`
11. Lightlike/Asymptotics/Lorentzian/ExpPhaseTests.lean - `Asymptotics.Lorentzian.hessMat_gaussAction`,
    `Asymptotics.Lorentzian.expPhase_gauss`, `Asymptotics.Lorentzian.expPhase_gauss_wrong_constant`,
    `Asymptotics.Lorentzian.invSqrtDet_neg_one_ne_one`,
    `Asymptotics.Lorentzian.expPhase_gauss_wrong_sign`, `Asymptotics.Lorentzian.sin_eq_zero_of_tendsto`,
    `Asymptotics.Lorentzian.swap_constants_fails`,
    `Asymptotics.Lorentzian.re_grow_integrand`, `Asymptotics.Lorentzian.expPhase_grow_fails`,
    `Asymptotics.Lorentzian.det_gauss_hessian`, `Asymptotics.Lorentzian.det_neg_of_even`,
    `Asymptotics.Lorentzian.invSqrtDet_neg_one_two`
12. Lightlike/Asymptotics/Lorentzian/Eq57.lean - `Asymptotics.Lorentzian.eq57Constant`,
    `Asymptotics.Lorentzian.weighted_two_points_eq57`, `Asymptotics.Lorentzian.eq57Constant_mult_zero`,
    `Asymptotics.Lorentzian.eq57Constant_neg_sgn`
13. Lightlike/Asymptotics/Lorentzian/NonClosing.lean - `Asymptotics.Lorentzian.lorVertex_suppressed`,
    `Asymptotics.Lorentzian.closing_violates_hnoclose`, `Asymptotics.Lorentzian.single_satisfies_hnoclose`
14. Lightlike/Asymptotics/Lorentzian/Amplitude.lean - `Asymptotics.Lorentzian.lorIntegrand`,
    `Asymptotics.Lorentzian.lorVertex`, `Asymptotics.Lorentzian.measurable_lorIntegrand`,
    `Asymptotics.Lorentzian.norm_lorIntegrand_le`, `Asymptotics.Lorentzian.integrable_lorEdgeDensity`,
    `Asymptotics.Lorentzian.lorEdgeDensity_one`
15. Lightlike/Asymptotics/Lorentzian/ActionTests.lean - `Asymptotics.Lorentzian.exp_triAction_odd_sign`,
    `Asymptotics.Lorentzian.exp_triAction_even_agree`,
    `Asymptotics.Lorentzian.triWeight_neg_spin_gt_one`
16. Lightlike/Asymptotics/Lorentzian/Bridge.lean - `Asymptotics.Lorentzian.lam_emb_cohState`,
    `Asymptotics.Lorentzian.suV_ae`, `Asymptotics.Lorentzian.hvec_cohState`,
    `Asymptotics.Lorentzian.inner_principalSeries_eq_integral`,
    `Asymptotics.Lorentzian.exp_triAction_nat`, `Asymptotics.Lorentzian.weight_pair`,
    `Asymptotics.Lorentzian.link_pointwise`, `Asymptotics.Lorentzian.link_eq_lor`
17. Lightlike/Asymptotics/Lorentzian/LinkIntegral.lean - `Asymptotics.Lorentzian.inner_pi_inv_mul`,
    `Asymptotics.Lorentzian.eprlVec_sum`, `Asymptotics.Lorentzian.eprlCoeff_pair`,
    `Asymptotics.Lorentzian.suV_cohVec_eq`, `Asymptotics.Lorentzian.ae_pairing_ne_zero`,
    `Asymptotics.Lorentzian.link_integral`
18. Lightlike/Asymptotics/Lorentzian/RadialBeta.lean - `Asymptotics.Lorentzian.radial_integral`
19. Lightlike/Asymptotics/Lorentzian/NormLowest.lean - `Asymptotics.Lorentzian.norm_sq_wgt`,
    `Asymptotics.Lorentzian.nrmA_sq_lowest`, `Asymptotics.Lorentzian.link_integral_explicit`
20. Lightlike/Asymptotics/Lorentzian/CoherentVertex.lean - `Asymptotics.Lorentzian.map_conjSL_haar`,
    `Asymptotics.Lorentzian.sum_magBox_linkProd`, `Asymptotics.Lorentzian.eprlIntegrand_iotaProd`,
    `Asymptotics.Lorentzian.eprlIntegrand_coh`, `Asymptotics.Lorentzian.eprlVertex_eq_lorVertex`,
    `Asymptotics.Lorentzian.integrable_lorOuter`, `Asymptotics.Lorentzian.link_value_spin_zero`
21. Lightlike/Asymptotics/Lorentzian/InnerIntegrable.lean - `Asymptotics.Lorentzian.ae_overlap_src`,
    `Asymptotics.Lorentzian.ae_overlap_tgt`, `Asymptotics.Lorentzian.integrable_edge`,
    `Asymptotics.Lorentzian.integrable_lorInner`, `Asymptotics.Lorentzian.integrable_lorInner_coh`
22. Lightlike/Asymptotics/Lorentzian/AsymptoticFormula.lean - `Asymptotics.Lorentzian.triAction_smul`,
    `Asymptotics.Lorentzian.lorAction_smul`, `Asymptotics.Lorentzian.lorVertex_asymptotic_formula`
23. Lightlike/Asymptotics/Lorentzian/ExpPhaseTwoPoints.lean - `Asymptotics.Lorentzian.toyAction`,
    `Asymptotics.Lorentzian.toy_two_points`
24. Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean - `Asymptotics.Lorentzian.critZ`,
    `Asymptotics.Lorentzian.critZ_src`, `Asymptotics.Lorentzian.critZ_tgt`,
    `Asymptotics.Lorentzian.re_lorAction_critZ`
25. Lightlike/Asymptotics/Lorentzian/ZStationary.lean - `Asymptotics.Lorentzian.hasDerivAt_triFactor_joint`,
    `Asymptotics.Lorentzian.hasDerivAt_triFactor_curve`, `Asymptotics.Lorentzian.zedge_cancel`,
    `Asymptotics.Lorentzian.edge_variation`,
    `Asymptotics.Lorentzian.sum_logDeriv_nodes`
26. Lightlike/Asymptotics/Lorentzian/TriActionDeriv.lean - `Asymptotics.Lorentzian.exp_triAction_eq_triFactor`,
    `Asymptotics.Lorentzian.differentiableAt_triAction`,
    `Asymptotics.Lorentzian.hasDerivAt_triAction_curve`
27. Lightlike/Asymptotics/Lorentzian/CriticalGradient.lean - `Asymptotics.Lorentzian.genMat`,
    `Asymptotics.Lorentzian.hasDerivAt_spinAct`,
    `Asymptotics.Lorentzian.hasDerivAt_lorAction_critical`, `Asymptotics.Lorentzian.hcl_of_closure`
28. Lightlike/Asymptotics/Lorentzian/SpinorPauli.lean - `Asymptotics.Lorentzian.inner_genMat`,
    `Asymptotics.Lorentzian.inner_genMat_genMat`, `Asymptotics.Lorentzian.srcValue_eval`,
    `Asymptotics.Lorentzian.projForm`, `Asymptotics.Lorentzian.tripleForm`
29. Lightlike/Asymptotics/Lorentzian/HessianNode.lean - `Asymptotics.Lorentzian.srcCoeff`,
    `Asymptotics.Lorentzian.tgtCoeff`, `Asymptotics.Lorentzian.endForm`,
    `Asymptotics.Lorentzian.hasDerivAt_srcCoeff`, `Asymptotics.Lorentzian.hasDerivAt_tgtCoeff`,
    `Asymptotics.Lorentzian.hessXX_block`, `Asymptotics.Lorentzian.sum_projForm_pos_iff`,
    `Asymptotics.Lorentzian.re_hessRR_neg`, `Asymptotics.Lorentzian.hessZZ_line`,
    `Asymptotics.Lorentzian.deriv_deriv_triAction_line`, `Asymptotics.Lorentzian.zzWirtinger`,
    `Asymptotics.Lorentzian.hessZZ_block`, `Asymptotics.Lorentzian.hessXZ_block`,
    `Asymptotics.Lorentzian.xzSource`, `Asymptotics.Lorentzian.xzTarget`,
    `Asymptotics.Lorentzian.hasDerivAt_srcCoeff_gen`, `Asymptotics.Lorentzian.hessXX_curve`,
    `Asymptotics.Lorentzian.srcCoeff_adj_gen`, `Asymptotics.Lorentzian.tgtCoeff_adj_gen`
30. Lightlike/Asymptotics/Lorentzian/HessianAssembly.lean - `Asymptotics.Lorentzian.hessZZ_cross`,
    `Asymptotics.Lorentzian.hessXX_cross`, `Asymptotics.Lorentzian.nodeQuad`,
    `Asymptotics.Lorentzian.nodeBilin`, `Asymptotics.Lorentzian.hessBlockMatrix`,
    `Asymptotics.Lorentzian.hessBlockMatrix_symm`

31. Lightlike/Asymptotics/Lorentzian/ClosureFromCritical.lean -
    `Asymptotics.Lorentzian.hasDerivAt_lorAction_aligned`, `Asymptotics.Lorentzian.exists_sl2_curve`,
    `Asymptotics.Lorentzian.aligned_of_re_lorAction_eq_zero`,
    `Asymptotics.Lorentzian.critical_configuration_closure`,
    `Asymptotics.Lorentzian.no_critical_without_closure`
32. Lightlike/Asymptotics/Lorentzian/VertexLocal.lean - `Asymptotics.Lorentzian.exists_smooth_extension`,
    `Asymptotics.Lorentzian.weighted_asymptotics_local`,
    `Asymptotics.Lorentzian.lorVertex_asymptotics_local`
33. Lightlike/Asymptotics/Lorentzian/ActionSmooth.lean - `Asymptotics.Lorentzian.contDiffAt_triAction`,
    `Asymptotics.Lorentzian.contDiffAt_spinAct`, `Asymptotics.Lorentzian.lorChartAction_contDiffOn`
34. Lightlike/Asymptotics/Lorentzian/CayleyChart.lean - `Asymptotics.Lorentzian.chartGen`,
    `Asymptotics.Lorentzian.cayleyMat`, `Asymptotics.Lorentzian.cayley`,
    `Asymptotics.Lorentzian.cayley_zero`, `Asymptotics.Lorentzian.contDiffOn_cayleyMat`,
    `Asymptotics.Lorentzian.hasDerivAt_cayleyMat_zero`
35. Lightlike/Asymptotics/Lorentzian/VertexChart.lean - `Asymptotics.Lorentzian.vertexChart`,
    `Asymptotics.Lorentzian.vertexChart_zero`, `Asymptotics.Lorentzian.cayleyDomain`,
    `Asymptotics.Lorentzian.lorChartAction_vertexChart_contDiffOn`,
    `Asymptotics.Lorentzian.lorVertex_asymptotics_vertexChart`,
    `Asymptotics.Lorentzian.vertexChart_group_hasDerivAt`, `Asymptotics.Lorentzian.vertexChart_spinor_hasDerivAt`
36. Lightlike/Asymptotics/Lorentzian/AsymptoticFormulaLocal.lean - `Asymptotics.Lorentzian.weighted_two_points_local`,
    `Asymptotics.Lorentzian.weighted_two_points_eq57_local`,
    `Asymptotics.Lorentzian.lorVertex_asymptotic_formula_local`
37. Lightlike/Asymptotics/Lorentzian/VertexHaarChart.lean - `Asymptotics.Lorentzian.integral_haar4_fixChart`,
    `Asymptotics.Lorentzian.integral_pi_haar_eq`, `Asymptotics.Lorentzian.lorVertex_eq_fixChart_integral`,
    `Asymptotics.Lorentzian.exists_measurePreserving_vertex_space`, `Asymptotics.Lorentzian.fixVertexChart`,
    `Asymptotics.Lorentzian.chartAmplitude`, `Asymptotics.Lorentzian.lorVertex_scaled_eq_chart_integral`
38. Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean - `Asymptotics.Lorentzian.fixDomain`,
    `Asymptotics.Lorentzian.fixVertexChart_group_contDiffOn`,
    `Asymptotics.Lorentzian.lorChartAction_fixVertexChart_contDiffOn`,
    `Asymptotics.Lorentzian.lorVertex_asymptotics_fixChart`
39. Lightlike/Asymptotics/Lorentzian/Eq57Constants.lean - `Asymptotics.Lorentzian.bdfhpC`,
    `Asymptotics.Lorentzian.bdfhpN`, `Asymptotics.Lorentzian.bdfhpN_eq`,
    `Asymptotics.Lorentzian.lorEdgeDensity_smul`

40. Lightlike/Asymptotics/Lorentzian/VertexSuppressed.lean -
    `Asymptotics.Lorentzian.fixPre`, `Asymptotics.Lorentzian.hasDerivAt_fixMat_line`,
    `Asymptotics.Lorentzian.fixVertexChart_curve`, `Asymptotics.Lorentzian.hasDerivAt_chartAction_aligned`,
    `Asymptotics.Lorentzian.weighted_suppressed_local`,
    `Asymptotics.Lorentzian.lorVertex_suppressed_fixChart`

## References

1. J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann, R. Pereira, Lorentzian spin foam
   amplitudes: graphical calculus and asymptotics, *Class. Quantum Grav.* 27 (2010) 165009.
