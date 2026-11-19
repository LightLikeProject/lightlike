# G2-002: Schwarzschild and FLRW initial data satisfy the ADM constraints (source check)

Lean file: `Lightlike/Canonical/InitialData.lean`.

## Sources read

1. E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035 (lecture notes, 2007).
   Read at the locations below in the arXiv PDF; page numbers are the printed ones (they agree with the PDF pages).
2. J. C. Aurrekoetxea, K. Clough and E. A. Lim, *Cosmology using numerical relativity*, arXiv:2409.01939v2 (2025).
   Read at the locations below in the arXiv PDF (version 2).

## Statements and the locations they rest on

| Lean statement | Source, location | Match |
|---|---|---|
| `schSlice M` is the spatial block of `schMetric M` at `t = 0`, equal to `diag((1 − 2M/r)⁻¹, r², r² sin²θ)` (`schSlice_eq`) | Gourgoulhon, eq. (7.16) (the Schwarzschild metric in Schwarzschild coordinates) and eq. (7.17) (`γ_ij = diag((1 − 2m/r)⁻¹, r², r² sin²θ)` on `t = const`), p. 107 | Same metric and same induced metric, with `m = M`, coordinates `(r, θ, φ) = (y 0, y 1, y 2)`. |
| Zero shift and `∂_t γ_ij = 0` (`schMetric_shift`, `schSlice_static`), hence `K_ij = 0` and `π = 0` | Gourgoulhon, eq. (4.104), p. 67 (`K_ij = (1/2N)(γ_ik D_j β^k + γ_jk D_i β^k − ∂_t γ_ij)`) and eq. (4.108), p. 67 (`π^{ij} = √γ (K γ^{ij} − K^{ij})`); the example after eq. (7.56), p. 112: for the foliations of the Schwarzschild coordinates "the extrinsic curvature vanishes identically: K = 0" | Same: the Lean proves the two inputs of (4.104) (shift and time derivative) and uses `π = 0`. |
| `schSlice_hamiltonianConstraint`, `schSlice_momentumConstraint` | Gourgoulhon, eq. (4.19), p. 54 (`R + K² − K_ij K^ij = 16πE`) and eq. (4.22), p. 54 (`D_j K^j_i − D_i K = 8π p_i`), with `E = 0`, `p = 0` (vacuum) | With `K = 0` the Hamiltonian constraint is `R = 0` (`scalarCurvature_schSlice`) and the momentum constraint is trivial. The library's `ℋ = −√γ (R + K² − K_ij K^ij)` (for `d = 3`) and `∇_k π^{ik}` are `−√γ` and `√γ` times the source's left-hand sides. |
| `flrwSlice_eq`: `γ_ij = a(t)² δ_ij`; lapse `1`, shift `0` (`flrwMetric_lapse`, `flrwMetric_shift`) | Aurrekoetxea–Clough–Lim, eq. (23), p. 10 (`γ_ij = a² δ_ij`, `K_ij ∼ −H γ_ij`, `K = −3H`) | Same slice metric. `flrwMetric a 0` is the `k = 0` case of `Lightlike/Cosmology/FLRW.lean`. |
| `flrwMomentum_eq`: `π^{ij} = −2 a'(t) δ^{ij}` is `√γ (K γ^{ij} − K^{ij})` with `K_ij = −½ ∂_t γ_ij` | Gourgoulhon, eqs. (4.104) and (4.108), p. 67, with `N = 1`, `β = 0`; Aurrekoetxea–Clough–Lim, eq. (22) (the same formula for `K_ij`) and eq. (23), p. 10 | Same: `K_ij = −a a' δ_ij = −H γ_ij`, and the source's sign convention (negative `K` for expansion) is the one used. |
| `flrw_hamiltonian_iff`: for `a(t) > 0`, `ℋ + 16πG √γ ρ = 0` iff `(a'/a)² = 8πGρ/3` | Aurrekoetxea–Clough–Lim, eq. (3), p. 4 (flat Friedmann equations), eq. (25), p. 10 (Hamiltonian constraint), and pp. 10-11 ("the Hamiltonian constraint is simply the first of the Friedmann equations in Eqn. (3)"); Gourgoulhon, eq. (4.19), p. 54 | Same equation. Representation: the constraint is written as `−√γ` times (4.19) / (25) with Newton's constant `G` kept; both sources write it with `G = 1` (eq. (3) of Aurrekoetxea–Clough–Lim keeps `G`). Eq. (25) of Aurrekoetxea–Clough–Lim prints `(3)R_ij`; the scalar `(3)R` is meant (it is contracted with nothing and compared with scalars), and Gourgoulhon's (4.19) has the scalar. |
| `flrwK_hamiltonian_iff` (any `k`): `ℋ + 16πG √γ ρ = 0` iff `(a'/a)² = 8πGρ/3 − k/a²`, with `γ_ij = (a S)² δ_ij`, `S = 1/(1 + k|x|²/4)` (the spatial block of `flrwMetric a k`), `R = 6k/a²` (`scalarCurvature_flrwSliceK`) | Gourgoulhon, eq. (4.19), p. 54, for the constraint; the curved Friedmann equation is `Lightlike.Cosmology.FirstFriedmann` (`Lightlike/Cosmology/FLRW.lean`, which cites Carroll's lecture notes) | The constraint is the source's (4.19); Aurrekoetxea–Clough–Lim state the reduction to Friedmann only for `k = 0`, so the comparison of the curved case with a source that states it is pending. |
| `flrwK_hamiltonian_iff_Lambda`: `ℋ + √γ (16πGρ + 2Λ) = 0` iff `(a'/a)² = 8πGρ/3 − k/a² + Λ/3` | Aurrekoetxea–Clough–Lim, p. 5, the text after eq. (6) (`w = −1` for the cosmological constant, densities added to give the sources of eq. (3)) | Representation: `Λ` is entered as the density `Λ/(8πG)` of a fluid with `w = −1` in `E = ρ` of (4.19). |
| `flrw_momentumConstraint` (zero matter momentum) | Aurrekoetxea–Clough–Lim, eq. (26), p. 10, and p. 11 ("the momentum constraints are trivially satisfied via isotropy"); Gourgoulhon, eq. (4.22), p. 54 | Same, with `S_i = p_i = 0` for the comoving fluid. |

## Scope

* Schwarzschild: the slice `t = 0` in Schwarzschild coordinates on the chart region `r > 0`, `r ≠ 2M`,
  `sin θ ≠ 0`; positive definiteness of the slice metric on `r > 2M` (`schSlice_posDef`). The isotropic form of
  the same slice (Gourgoulhon, Sec. 8.2) is not formalised here.
* FLRW: any `k` and `Λ`, on the chart domain `1 + k|x|²/4 > 0` of `Lightlike.Cosmology.flrwDomain` (all of `ℝ³` for
  `k ≥ 0`, the ball `|x| < 2/√|k|` for `k < 0`).
* Schwarzschild: every slice `t = const` carries the same data (`schMetric_block_eq_schSlice`); the chart region is the
  domain of the Schwarzschild coordinates themselves, as in Gourgoulhon's (7.16)–(7.17).

## Trust checks

* `ricci_schSlice_ne_zero`: for `M ≠ 0` the Schwarzschild slice is curved (`R_θθ = M/r`), so the vanishing of `R`
  is not flatness; `ricci_schSlice` gives all components, checked independently with a sympy computation of the
  library's formulas (`R_rr = −2M/(r²(r − 2M))`, `R_θθ = M/r`, `R_φφ = M sin²θ/r`, `R = 0`).
* `schSliceRegion_nonempty`: the exterior region is not empty for every `M`.
* `deSitter_hamiltonianConstraint`: de Sitter (`a = e^{Ht}`, `H² = 8πGρ_Λ/3`) satisfies the constraint at every time.
* `expanding_vacuum_violates`: an expanding slice without matter (`H ≠ 0`, `ρ = 0`) violates it.
* `ricci_cf`: the Ricci tensor `2kS²δ_ij` of the curved slice agrees with the spatial part of the four-dimensional
  `Lightlike.Cosmology.ricci_flrw` at `a' = a'' = 0`, computed independently.
