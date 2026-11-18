# GE6: Kerr is Ricci-flat — plan

State (4e3e69e): `Lightlike/GR/Kerr.lean` has `kerrMetric` (Boyer–Lindquist), `det_kerrMetric = -Σ² sin²θ`,
`isCoordMetric_kerr`, `kerrMetric_zero` (a = 0 is Schwarzschild). Nothing about curvature yet.

Open: `IsVacuumSolution 0 (kerrMetric M a) (kerrU M a)`; Killing horizon `r₊ = M + √(M²-a²)`, `κ = √(M²-a²)/(2 M r₊)`,
`Ω_H = a/(2 M r₊)`; negative control: flipping the sign of `g_tφ` is not Ricci-flat (a ≠ 0).

Method (MEASURED difficulty: the diagonal route used for Schwarzschild/AdS does not apply, g has a (t,φ) block):
1. Inverse metric in closed form (block `[[g_tt, g_tφ],[g_tφ, g_φφ]]` has determinant `-Δ sin²θ`),
   `g^{tt} = -((r²+a²)² - Δ a² sin²θ)/(ΣΔ)`, `g^{tφ} = -2Mar/(ΣΔ)`, `g^{φφ} = (Δ - a² sin²θ)/(ΣΔ sin²θ)`,
   `g^{rr} = Δ/Σ`, `g^{θθ} = 1/Σ`. Prove `kerrMetric * kerrInv = 1`.
2. Christoffels `Γ^i_{jk}` with the library's `christoffel` replaced via `inv`; expect ~30 independent symbols, each a
   rational function of `r, cosθ, sinθ`. Alternative with far smaller expressions: Kerr–Schild form
   `g = η + (2Mr³/(r⁴+a²z²)) l⊗l` in Cartesian-like coordinates, then a chart change to Boyer–Lindquist
   (the `IsChartChange`/`ricci_pullback` machinery of `ChartChange.lean` transports Ricci-flatness).
3. Prefer route Kerr–Schild if `ricci` of `η + H l l` with `l` null and geodesic reduces to a linear equation in `H`
   (the Kerr–Schild linearity), else brute force with `field_simp; ring` in pieces per `(σ,ν)`.
