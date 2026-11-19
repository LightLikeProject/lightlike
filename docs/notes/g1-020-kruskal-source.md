# G1-020: the Kruskal-Szekeres metric, source comparison

Lean: `Lightlike/GR/KruskalFunction.lean`, `Lightlike/GR/KruskalMetric.lean`.

## Source read (pdftotext of the arXiv PDF)

S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7 "The Schwarzschild solution and black holes",
eqs. (7.75)-(7.85), printed pages 186-188 (units `G` kept, `G = 1` in Lean). Wording and equations:

* (7.77) in the null coordinates `(u', v')`: `ds² = -(16 G³M³/r) e^{-r/2GM} (du' dv' + dv' du') + r² dΩ²`.
* (7.78)-(7.79): `u = (u' - v')/2`, `v = (u' + v')/2`, "in terms of which the metric becomes"
  (7.80) `ds² = (32 G³M³/r) e^{-r/2GM} (-dv² + du²) + r² dΩ²`,
  (7.81) "where r is defined implicitly from `(u² - v²) = (r/2GM - 1) e^{r/2GM}`". "The coordinates (v, u, θ, φ) are known as
  Kruskal coordinates ... Note that v is the timelike coordinate."
* (7.82)-(7.83): radial null curves `v = ±u + constant`; "the event horizon r = 2GM ... is defined by `v = ±u`".
* "our coordinates (v, u) should be allowed to range over every value ... the allowed region is therefore `-∞ ≤ u ≤ ∞` and `v² < u² + 1`".

## How each Lean statement matches (Carroll's `(v, u)` = our `(T, X)`)

* `kruskalMetric`: `h(r) = (32 M³/r) e^{-r/2M}`, `diag(-h, h, r², r² sin²θ)` with `r = kG(X² - T²)`: MATCH with (7.80)-(7.81), `G = 1`.
* `kruskalU = {X² - T² > -1, 0 < θ < π}`: MATCH with the allowed region `v² < u² + 1` (source states the whole region, we add `0 < θ < π` for the chart).
* `kF M r = (r/2M - 1) e^{r/2M}`, `kG` its inverse on `(-1, ∞)`: the implicit definition (7.81); the source does not prove that the implicit equation
  defines a smooth `r` (we prove it: `contDiffAt_kG`).
* `kruskal_isVacuumSolution`: the source derives the metric from Schwarzschild by coordinate changes (so it solves the vacuum equations on the image);
  our statement covers the whole region including the horizons `T = ±X` (continuity of Ricci) and the region `T + X < 0` (reflection symmetry), and the
  Lorentzian signature (`kruskal_isLorentzian`). The source does not state either explicitly.
* Source statement not proved in Lean: null curves `v = ±u + const` (7.82); regions I-IV and the Kruskal diagram; the exterior coordinate map
  `(t, r) ↦ (v, u)` (7.78)-(7.79) is replaced by the chart change from ingoing Eddington-Finkelstein coordinates (`kruskalChange`).

Not read: Kruskal (1960), Szekeres (1960), MTW section 31.5, Wald section 6.4.

## Open parts of G1-020 (row text: Kruskal-Szekeres MAXIMAL extension of Schwarzschild, Eddington-Finkelstein, event horizon, interior region, Penrose diagram)

Proved in Lean: Eddington-Finkelstein chart across the horizon (vacuum, `ef_isVacuumSolution`), the Kruskal-Szekeres metric on `X² - T² > -1` (vacuum, Lorentzian,
`kruskal_isVacuumSolution`, `kruskal_isLorentzian`), the chart change from EF, the reflection symmetry.

NOT proved (open, no attempt completed):
* **Maximality (inextendibility)** of the Kruskal extension: needs the notion of an extension of a Lorentzian manifold and a curvature-blow-up or geodesic-completeness argument
  (the Kretschmann scalar `48 M²/r⁶` diverges at `r = 0`); none of this is in the library. The same missing infrastructure blocks the non-extension routes of G1-058
  (Riemannian length/distance, holonomy, Killing fields on manifolds).
* **Null curves `v = ±u + const`** (Carroll (7.82)) and the statement of the event horizon as `v = ±u` (7.83): the horizon as a null hypersurface and the event horizon as the
  boundary of the past of future null infinity need the causal structure of the Kruskal manifold (GE2 relations on a manifold with this chart): not formalized here.
* **The four regions I-IV and the exterior map `(t, r) ↦ (v, u)`** (7.78)-(7.79) (we use the chart change from ingoing EF instead).
* **The Penrose diagram** (conformal compactification of the Kruskal manifold: Penrose-Carter): this is GE7, only done for Minkowski space and AdS.

## Parts closed after the metric

Source read for these: Carroll, arXiv:gr-qc/9712019, chapter 7, printed pages 186-190 (eqs. (7.75)-(7.85), the Kruskal
diagram, the four regions and the text on regions II-IV) and pages 197-198 (eqs. (7.103)-(7.105), the Penrose diagram
of the maximally extended solution). Kruskal (1960), Szekeres (1960), MTW, Wald, Hawking-Ellis: not read.

* Lightlike/GR/KruskalRegions.lean: (7.83) horizon `r = 2M` iff `X² = T²`; (7.84) `r` constant iff `X² - T²` constant;
  `T` timelike, `X` spacelike; (7.82) a radial vector `(a, b, 0, 0)` is null iff `a² = b²`; the regions
  `I: X > |T|`, `II: T > |X|`, `III: T < -|X|`, `IV: X < -|T|` cover the domain with the horizon, `r > 2M` exactly in
  `I ∪ IV`, `r < 2M` exactly in `II ∪ III`; a curve with future-directed causal velocity that is in region II stays in
  it, and `r` strictly decreases along it (the source: "it can never return", "you cannot even stop yourself from
  moving in the direction of decreasing r").
* Lightlike/GR/KruskalExterior.lean: (7.78), (7.79) as the closed form of `kruskalChange` at `v = t + r*`; (7.85)
  `T/X = tanh (t/4M)`; the image of the exterior `r > 2M` is exactly region I.
* Lightlike/GR/KruskalPenrose.lean: (7.105) with `p = arctan (T + X)`, `q = arctan (T - X)`: a bijection of the
  Kruskal domain onto `|p|, |q| < π/2`, `|p + q| < π/2`; the singularity lines `p + q = ±π/2` are straight; the horizon
  is `p = 0` or `q = 0`; the metric in `(p, q, θ, φ)` is `-(h(r)/(2 cos²p cos²q))(dp dq + dq dp) + r² dΩ²`.

Differences from the source in these files:
* representation: causal curves are differentiable curves in the chart with `g(v, v) ≤ 0`, `0 < v⁰`; the manifold
  notion `IsFutureCausalCurve` is not used; the regions are given by inequalities read off the source's figure.
* convention: no factor `√(2GM)` inside the arctangent of (7.105) (our `T`, `X` are dimensionless).
* representation: the source's ranges for `(u'', v'')` are `-π/2 < u'', v'' < π/2` and `-π < u'' + v'' < π`; the exact
  image proved here is cut by `|p + q| < π/2` (our `q` belongs to `U = T - X`).

Still open: maximality (inextendibility) of the extension; the event horizon as the boundary of the past of future
null infinity on the manifold; conformal infinity as added points.

## The curvature singularity

Source read: Carroll, arXiv:gr-qc/9712019, chapter 7, printed pages 171-172 (curvature scalars as the test for a
singularity; eq. (7.30)).

* Lightlike/Spacetime/Kretschmann.lean: `K = R_{abcd} R^{abcd}` for a coordinate metric, chart independence
  (`kretschmann_pullback`), continuity.
* Lightlike/GR/SchwarzschildKretschmann.lean: all components of the Riemann tensor of Schwarzschild (`riemann_sch`),
  and `K = 48 M²/r⁶` (`kretschmann_sch`).
* Lightlike/GR/KruskalKretschmann.lean: `K = 48 M²/r⁶` in Eddington-Finkelstein coordinates across the horizon and
  on the whole Kruskal domain; `K` is unbounded near `X² - T² = -1`; for every coordinate metric and every chart
  change of the Kruskal domain into its domain that is an isometry, a sequence with `r → 0` has no limit in the
  target (`not_tendsto_of_isometric_chart`).

Difference from the source (kind: the source is in error): (7.30) prints `12 G²M²/r⁶`; the computation gives
`48 M²/r⁶`. The conclusion of the source (the invariant diverges at `r = 0`) is unaffected.

Maximality, state of the attempts:
* Attempt 1 (this section): curvature blow-up excludes every extension through `r = 0`. It does not give
  maximality: an extension could add points elsewhere (at the ends `r → ∞` of the two exteriors, or along the
  horizons at infinite `T`, `X`). Concrete missing step: every inextendible geodesic of the Kruskal manifold that
  does not run into `r = 0` is complete; with that, the standard argument (a boundary point of an extension is
  reached by a geodesic of finite affine length) closes maximality. Not in the library: geodesics of the Kruskal
  metric beyond the radial null ones, affine completeness, and the notion of an extension of a Lorentzian manifold.
* Attempt 2: maximality stated for the chart, "no coordinate metric on a larger connected open
  set restricts to the Kruskal metric under an isometric chart embedding". This statement is FALSE, so the attempt
  fails for a concrete reason: the chart domain `kruskalU` has `0 < θ < π`, it omits the rotation axis `θ = 0, π` of
  every two-sphere. The Kruskal manifold is `{X² - T² > -1} × S²`, and `kruskalU` is a proper open subset of it;
  a second chart with a rotated polar axis extends it. Every geodesic that crosses the axis leaves the chart at a
  finite affine parameter without any singularity. So maximality cannot be stated or proved at the level of one
  coordinate chart; it needs the Kruskal manifold with its `S²` factor (two charts at least, or the product
  structure), which the library does not have: the manifold of the exterior in
  Lightlike/Spacetime/SchwarzschildManifold.lean is also an open subset of `ℝ⁴` in one chart.
  What attempt 2 produced and is true: the ingoing radial null rays as geodesics with
  affine parameter `-r` in Eddington-Finkelstein coordinates, and the divergence of the Kretschmann scalar at the
  finite affine parameter `r₀` along them (Lightlike/GR/EFNullGeodesic.lean): the extension is geodesically
  incomplete at `r = 0`, the "finite distance" condition of the source (page 171).
* What a full proof needs, in order: (1) the Kruskal manifold `{X² - T² > -1} × S²` as a Lorentzian manifold;
  (2) the notion of an extension (an isometric open embedding into a connected Lorentzian manifold that is not
  onto); (3) existence of geodesics in the extension through a boundary point (Picard-Lindelöf for the geodesic
  equation); (4) the classification of the geodesics of the Kruskal manifold by the constants of motion `E`, `L`:
  each inextendible one is complete or has `r → 0` at a finite affine parameter; (5) the curvature argument of
  attempt 1. Steps (1)-(4) are new infrastructure.

## The Kruskal manifold in one chart

Step (1) of the plan for maximality, done without a sphere bundle: `ℝ × S²` is `ℝ³ ∖ {0}` by `(X, n) ↦ e^X n`, so
the Kruskal manifold `{X² - T² > -1} × S²` is the open subset `{x ≠ 0, (log |x|)² - T² > -1}` of `ℝ⁴`.

* Lightlike/GR/KruskalManifold.lean: the metric `-h dT² + ((h - r²)/|x|⁴)(x·dx)² + (r²/|x|²)|dx|²` is a smooth
  Lorentzian coordinate metric there (explicit frame); `kruskalManifoldMetric` is the Lorentzian metric on the
  manifold.
* Lightlike/GR/KruskalSpherical.lean: the chart `(T, X, θ, φ)` maps into it by a chart change, and the metric pulls
  back to the Kruskal metric of the source's form (7.80).
* Lightlike/GR/KruskalManifoldCurvature.lean: vacuum equations and the Kretschmann scalar `48 M²/r⁶` on the whole
  manifold (the rotation axis by continuity).

This global chart is the library's own; no source is cited for it. Remaining for maximality: (2) the notion of an
extension, (3) geodesics through a boundary point of an extension, (4) the classification of the geodesics.

## The notion of extension

Source read (pdftotext of the arXiv PDF): J. Sbierski, *The C⁰-inextendibility of the Schwarzschild spacetime and
the spacelike diameter in Lorentzian geometry*, arXiv:1507.00601v2 (25 April 2016): page 1 (the definition of
`Cᵏ`-inextendible in the introduction), Section 2.3, Definition 2.15 and Remark 2.16 (page 11), Lemma 2.17
(page 12), Section 1.1 (page 3) and item iv) of Section 1.3 ("timelike geodesic completeness implies, in a
straightforward way, the `C²`-inextendibility of the Lorentzian manifold").
The abstract states: "The maximal analytic Schwarzschild spacetime is manifestly inextendible as a Lorentzian
manifold with a twice continuously differentiable metric."

Lightlike/Spacetime/SpacetimeExtension.lean: `IsLorentzianExtension`, `IsInextendible` (Definition 2.15, for smooth
metrics; differences recorded in the file header: smooth instead of `Cᵏ` (weaker), open embedding and an explicit
Hausdorff hypothesis (representation)). Remark 2.16 (3) of the source: a local notion of extension is not adequate
(Minkowski space would be locally extendible), so the target statement is the global one,
`IsInextendible (kruskalManifoldMetric M hM)`.

Not yet proved. The bridge still missing between `IsLorentzianExtension` and the chart statements: in a chart of
the extension around a boundary point, the embedding is a chart change on an open subset of the Kruskal manifold,
so `not_tendsto_of_isometric_chart` applies to sequences with `r → 0`; the other sequences need the geodesics.

## The curvature half of maximality at the level of manifolds

* Lightlike/Spacetime/ExtensionChart.lean: for a smooth isometric map `ι` of an open subset `U` of `ℝⁿ` (with a
  Lorentzian coordinate metric) into a Lorentzian manifold, and a chart of the target at a point `p`, the map
  `ψ = chart ∘ ι` is a chart change on its open domain and the coordinate metric of the target pulls back to the
  metric of `U` (`pullback_coordMetric_extChartMap`, `isChartChange_extChartMap`).
* Lightlike/GR/KruskalExtension.lean: `IsLorentzianExtension.not_tendsto_kruskal`: in every extension of the Kruskal
  manifold (Sbierski's Definition 2.15, smooth metrics), a sequence of points with `X² - T² → -1` has no limit.

What is still missing for `IsInextendible (kruskalManifoldMetric M hM)`: a boundary point `p` of the image in an
extension is the limit of a sequence `ι z_k`; by the theorem above `X² - T²` stays away from `-1` along it, so
`z_k` leaves every compact subset of the Kruskal manifold with `r` bounded below. To exclude this one needs that
such a sequence cannot converge in a Lorentzian manifold; the standard proof takes a geodesic of the extension
through `p` and uses that every geodesic of the Kruskal manifold is complete or runs into `r = 0`
(Sbierski, Section 1.3 iv)). Missing in the library: existence of geodesics through a point (Picard-Lindelöf for
the geodesic equation in a chart) and the analysis of the Kruskal geodesics with the constants of motion.

## Toward the geodesics

Proved so far, for the second half of maximality:
* Lightlike/Spacetime/GeodesicChartChange.lean: geodesics are chart-independent (`IsGeodesicOn.map_chartChange`).
* Lightlike/Spacetime/GeodesicMomentum.lean: the momentum of a cyclic coordinate is conserved
  (`IsGeodesicOn.hasDerivAt_momentum`).
* Lightlike/GR/EFConstants.lean: in Eddington-Finkelstein coordinates the energy `p = -(1 - 2M/r) v' + r'` and the
  axial angular momentum are constant, and `r'² = p² + (1 - 2M/r)(κ - r² (θ'² + sin²θ φ'²))` with `κ = g(w, w)`
  (constant by `IsGeodesicOn.hasDerivAt_speed`).

Plan for "a geodesic of the Kruskal manifold defined on `[0, b)`, `b < ∞`, with `r` bounded below has a limit in
the manifold as `t → b`" (with it and the existence of geodesics through a point (the exponential map of a coordinate
metric), inextendibility follows as in Sbierski, Section 1.3 iv)):
1. the total angular momentum `L² = r⁴ (θ'² + sin²θ φ'²)` is constant (the angular Christoffel symbols of the
   Eddington-Finkelstein metric, or the rotations as chart changes of the global chart);
2. then `|r'|` is bounded on the interval by the radial equation, so `r` is bounded above and below;
3. the null Kruskal coordinates satisfy `|V U'|, |U V'| ≤ C` (from `κ` and the energy), which bounds `U'`, `V'` away
   from the bifurcation sphere `U = V = 0`; at the bifurcation sphere a separate argument is needed (the geodesic
   equation in the Kruskal chart, whose Christoffel symbols are not yet computed);
4. bounded velocity gives a Cauchy curve, hence a limit, which lies in the manifold because `r` is bounded below.
Steps 1-4 are not done.
