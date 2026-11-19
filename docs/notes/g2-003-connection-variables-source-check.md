# G2-003: connection and triad variables (source check)

Lean files: `Lightlike/Canonical/Triad.lean`, `Lightlike/Canonical/SpinConnection.lean`, `Lightlike/Canonical/Tetrad.lean`,
`Lightlike/Canonical/Holst.lean`.

## Sources read

1. A. Ashtekar and J. Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018
   (Class. Quant. Grav. 21 (2004) R53), Sec. II, read at the locations below in the arXiv PDF.
2. S. Holst, *Barbero's Hamiltonian derived from a generalized Hilbert-Palatini action*, arXiv:gr-qc/9511026
   (Phys. Rev. D 53 (1996) 5966), read in full (6 pages).

## Statements and the locations they rest on

| Lean | Source, location | Match |
|---|---|---|
| `IsCoTriad e h`: `h = eᵀ e` (`h_ab = Σ_i e^i_a e^i_b`), `e` invertible | Ashtekar–Lewandowski, text before eq. (2.16), p. 16: `q_ab = e^i_a e^j_b η_ij` | Same with `η = δ` (Lorentzian signature, `σ = −1`). |
| `densTriad`: `E^a_i = |det e| e^a_i`; `densTriad_eq_poly`: `E^a_i = ½ ε_ijk ε_abc e^j_b e^k_c` for `det e > 0` | eqs. (2.20)–(2.21), p. 17: `kγ P^a_i = √|det q| e^a_i = Ẽ^a_i` and `P^a_i = (1/2kγ) e^j_b e^k_c η^{abc} ε_ijk` | Same (`E = kγ P`); the polynomial form needs the orientation `det e > 0`, as the equality of the two expressions in (2.20)–(2.21) does. |
| `triadK`: `K^i_a = K_ab e^b_i` | eq. (2.18), p. 16: `K^i_a = (q^α_a q^b_β ∇_α n^β) e^i_b`, with `n` the future directed unit normal (p. 16) | Same form, with `K_ab` AL's `q q ∇n`. **Convention:** this `K_ab` is minus the `extrinsicCurvature` of `Lightlike/Canonical/Foliation.lean` (Gourgoulhon (2.43): `K(u, v) = −u · ∇_v n`), so the chart data of a foliation enter `triadK` and `abConn` as `−K` (corrected 19 November 2026; earlier this row read "Same"). |
| `spinConn`: `Γ^i_a = −½ ε_ijk e^b_j ∇_a e^k_b`, with `∇` built from `Lightlike.christoffel h` | Holst, eq. (6), p. 2: `Γ^i_a = −½ ε^{ijk} e^b_j ∇_a e_{bk}` | Same (internal indices moved with `δ`). |
| `spin_compat`: `∂_a e^k_b − ∂_b e^k_a + ε_kij (Γ^i_a e^j_b − Γ^i_b e^j_a) = 0` | Ashtekar–Lewandowski eq. (2.17), p. 16: `de^i + ε^i_jk Γ^j ∧ e^k = 0` | Same; `covTriad_add_spin` is the stronger `∇_a e^k_b + ε_ijk Γ^i_a e^j_b = 0`. |
| `abConn`: `A^i_a = Γ^i_a + γ K^i_a` | eq. (2.20), p. 17: `A^i_a = Γ^i_a − σγ K^i_a` | Same with `σ = −1` (Lorentzian). |
| `gaussConstraint`: `G_i = ∂_a E^a_i + ε_ijk A^j_a E^a_k` | eq. (2.23), p. 17: `G_i = D_a P^a_i = ∂_a P^a_i + ε_ij^k A^j_a P^a_k` | Same up to the constant factor `kγ` (`E = kγ P`). |
| `gauss_spinConn`: `∂_a E^a_i + ε_ijk Γ^j_a E^a_k = 0` | the compatibility of `Γ` with the triad (2.17), p. 16 | The statement is a consequence the source uses but does not number. |
| `gaussK_eq_zero_iff`: the `K` part `ε_ijk K^j_a E^a_k` vanishes iff `K_ab = K_ba` | — | Supporting lemma; not stated in the sources read. |
| `tetradConn`: `ω_μ = e (∂_μ e⁻¹ + Γ_μ e⁻¹)`, i.e. `ω_μ^I_J = e^I_ν ∇_μ e^ν_J` | Holst eq. (3), p. 2 (`A_α^{IJ} = e^{βI} ∇_α e_β^J`, the solution of the connection equation) | Same (`∇` from `Lightlike.christoffel g`). |
| `gaugeCurv`: `F_μν = ∂_μ ω_ν − ∂_ν ω_μ + [ω_μ, ω_ν]` | Holst p. 1 (`F_αβ^{IJ}` the curvature of `A_α^{IJ}`); Ashtekar–Lewandowski eq. (2.2), p. 10 (`Ω := dω + ω ∧ ω`) | Same in components. |
| `gaugeCurv_tetradConn`: `F(ω(e)) = e R e⁻¹` | Holst, text before eq. (4), p. 2 (with (3), `F` becomes the Riemann tensor) | Same. |
| `holstDensity γ`: `½ det e · e^α_I e^β_J (F^{IJ} − (1/γ) ½ ε^{IJ}_{KL} F^{KL})` | Holst eq. (1), p. 1, with `α = β⁻¹` (p. 2) and `β = γ`; Ashtekar–Lewandowski eq. (2.6), p. 11 | Same with `α = 1/γ` and `16πG = 1`-type normalization `½` of Holst (1). |
| `holstStar_tetradConn`: the dual term vanishes on `ω(e)` | Holst eq. (4), p. 2 (`= ε^{αβγδ} R_{αβγδ} = 0` since `R_{[αβγ]δ} = 0`) | Same; the Bianchi identity is `IsCoordMetric.bianchi_first`. |
| `palatini_tetradConn`, `holstDensity_tetradConn`: on `ω(e)`, `holstDensity = ½ det e R(g)` | Holst, p. 2 ("(1) differ from the case α = 0 ... by at most a canonical transformation"); Ashtekar–Lewandowski p. 11 (the Holst term does not change the equations of motion) | Same content: on the solution of the connection equation the Holst action is the Palatini (Einstein–Hilbert) action. |

## Trust checks

* `spinConn_one`: the flat triad has zero spin connection; `gauss_abConn_antisymm_violates`: an antisymmetric `K`
  violates the Gauss constraint.
* `holstStar_rotation`: the Holst dual term of the constant connection `ω_0 = L₁₂`, `ω_1 = L₁₃` is `4` (so the vanishing
  on `ω(e)` is not trivial).
