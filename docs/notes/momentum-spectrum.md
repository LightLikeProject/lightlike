# The spectrum of the momentum extensions `P_θ` on `L²(0, 1)`

Source read: G. Bonneau, J. Faraut, G. Valent, arXiv:quant-ph/0103153, Section 5.3, p. 8: after eq. (14), "Moreover, the spectra are purely
discrete. Using the boundary condition (14), the eigenvalues and eigenfunctions are easily shown to be" eq. (15):
`P_θ φ_n(x, θ) = (2πħ/L) ν φ_n(x, θ)`, `ν = n + θ/2π`, `n = 0, ±1, ±2, …`, `φ_n(x, θ) = L^{-1/2} exp(2iπν x/L)`, `(φ_m, φ_n) = δ_mn`.

Conventions: `ħ = 1`, `L = 1`; the eigenvalue `2πν = θ + 2πn` is written `θ + 2πn` and the eigenfunction `e^{i(θ + 2πn)x}`
(`planeWave (θ + 2πn)`); `θ` is real.

| Source (p. 8) | Library (`MomentumSpectrum`) | Check |
|---|---|---|
| `φ_n ∈ D_θ`, `P_θ φ_n = 2πν φ_n` | `momentumTheta_planeWave` | matches |
| `(φ_m, φ_n) = δ_mn` | `inner_planeWave`, `orthonormal_planeWave` | matches |
| "the eigenvalues are" the `2πν`, `n ∈ ℤ` (no others) | `eigenvalue_momentumTheta`: an eigenvalue `μ ∈ ℂ` of `P_θ` is `θ + 2πn` | matches |
| the eigenfunctions are the `φ_n` | `eigenvector_momentumTheta`: an eigenvector for `θ + 2πn` is a multiple of `φ_n` | matches |
| "the spectra are purely discrete" | `spectrum_momentumTheta`: `σ(P_θ) = θ + 2πℤ` (Physlib's `LinearPMap.spectrum`); `pointSpectrum_momentumTheta`: `σ = σ_p`; with the one-dimensional eigenspaces and `2πℤ` discrete | matches, in the sense: every point of the spectrum is an isolated eigenvalue of multiplicity one |

Method. An eigenvector `y` of `A†` with `A† y = μ y` has the continuous representative `f = f(0) + ∫₀ˣ i μ f`, so `e^{-iμx} f(x)` is absolutely
continuous with derivative zero almost everywhere and `f = f(0) e^{iμx}` (`bvRep_eigen`); the boundary condition gives `e^{iμ} = e^{iθ}`. Off
`θ + 2πℤ` the resolvent equation `-i y' - z y = f`, `y(1) = e^{iθ} y(0)`, has the solution `y(x) = e^{izx} (C + i ∫₀ˣ e^{-izt} f(t) dt)`
(`exists_momentumTheta_sub_eq`), so `P_θ - z` is onto; it is one-to-one since `z` is not an eigenvalue, and `P_θ` is closed, so `z` is in the
resolvent set (Physlib's `IsClosed.resolventSet_eq`). No compact-resolvent theorem is used.

Differences from the source, kind convention: `ħ = 1`, `L = 1` (the general `L` is the unitary rescaling, not stated), `θ ∈ ℝ`. Not stated: the
expansion (16)-(17) of the state (4).
