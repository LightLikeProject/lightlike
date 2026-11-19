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
