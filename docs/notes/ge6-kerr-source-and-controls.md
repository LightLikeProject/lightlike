# GE6: Kerr, source comparison and negative controls

Lean files: `Lightlike/GR/Kerr.lean`, `KerrJet.lean`, `KerrJetEntries.lean`, `KerrRicci.lean`, `KerrHorizon.lean`, `KerrControl.lean`.

## Source read (pdftotext of the arXiv PDF)

M. Visser, *The Kerr spacetime: A brief introduction*, arXiv:0706.0622v3 (mass written `m`). Locations:
* Boyer–Lindquist line element: section 5 "Boyer–Lindquist coordinates", eq. (57), p. 14. Same entries as `kerrMetric`
  (`g_tt = -(1 - 2mr/Σ)`, `2 g_tφ = -4mra sin²θ/Σ`, `g_rr = Σ/Δ`, `g_θθ = Σ`, `g_φφ = (r² + a² + 2ma² r sin²θ/Σ) sin²θ`).
  Also: "If a → 0 the Boyer–Lindquist line element reproduces the Schwarzschild line element" (p. 15), matching `kerrMetric_zero`.
* Determinant: "det(g_ab) = − sin²θ (r² + a² cos²θ)²", eq. (106). Matches `det_kerrMetric`.
* Horizons: `r± = m ± √(m² − a²)` (the table of surfaces, section on horizons). Matches `kerrRplus`.
* Angular velocity and the null generator: `Ω± = a/(2 m r±) = a/(r±² + a²)` (112), `L^a = (1, 0, 0, Ω±)` (113),
  `g_ab(r±) L^a L^b = 0` (114), p. 26. Matches `kerrOmega`, `kerr_chi_null` (null for every θ at `r = r₊`).

NOT found in this source: the surface gravity `κ` (no occurrence of surface gravity or κ in the text). `kerrKappa = Δ'(r₊)/(2(r₊² + a²))`
and `kerrKappa_eq : κ = √(M² − a²)/(2 M r₊)` are therefore compared with the plan row GE6 only (and my memory of the standard value
(r₊ − r₋)/(2(r₊² + a²)), which is not a source); no location is cited for `κ`. Boyer–Lindquist (1967) and Carroll ch. 6 were not read.

The Ricci-flatness of Kerr: Visser does not prove it in the section read; `kerr_isVacuumSolution` is proved in Lean from `riemann_jet`.

## Negative controls

* The plan row asks for "a sign flipped in g_tφ shown not to be Ricci-flat". That statement is false: `g_tφ` is the only entry odd in `a`
  (`Σ`, `Δ`, `g_tt`, `g_rr`, `g_θθ`, `g_φφ` depend on `a²`), so flipping its sign is `a ↦ −a` (`kerrMetric_neg`), which is Kerr with spin `−a`
  and Ricci-flat (`ricci_kerr` holds for every `a`). Confirmed by `sympy` (Ricci of the `k = ±1` metrics vanishes).
* The real control: `ctrlMetric M a k` = Kerr with `g_tφ` multiplied by `k`; for `k = 1/2`, `M = 1`, `a = 1/2` at `(r, θ) = (3, π/2)`
  `sympy` gives `R_{22} = −25/456 ≠ 0` (also `R_{00} = −13/24624`, `R_{03} = 1/2052`, `R_{11} = 2443/84474`, `R_{33} = 1321/98496`).
  The Lean proof of `R_{22} ≠ 0` (`ctrl_not_ricci_flat`) is in `KerrControl.lean` (status: see the file).
