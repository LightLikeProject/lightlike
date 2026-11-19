# G3-089: couplings and the 1-Wasserstein distance

Source: W. Huang, R. Wang, Y. Wu, D. Meng, *Exact Endpoint Asymptotics and Almost-Sure Limits for Uniform Empirical
Measures in Two Dimensions*, arXiv:2610.21070 (source key `huang-wang-wu-meng-2026`, location verified).

Read: Section 3.2.1, p. 5, the statement (KR): for Borel probability measures `ν`, `η` on a compact metric space
`(M, d)`, `W₁(ν, η) = inf_{γ ∈ Π(ν, η)} ∫ d dγ = sup_{Lip(u) ≤ 1} ∫ u d(ν - η)`, with "the easy direction is immediate:
for any coupling `γ` and unit Lipschitz function `u`, `∫ u d(ν - η) ≤ ∫ d dγ`". Section 8.1, pp. 46-47, the proof
(finite grid, finite-dimensional linear programming duality (8.1), then approximation).

| Source | Lean |
|---|---|
| `Π(ν, η)`, the probability couplings | `couplings`, `prod_mem_couplings` |
| `W₁(ν, η) = inf_γ ∫ d dγ` | `wasserstein1`, `wasserstein1_le` |
| the easy direction | `integral_sub_le_of_mem_couplings`, `integral_sub_le_wasserstein1` |
| (check) | `wasserstein1_dirac`: `W₁(δₓ, δ_y) = d(x, y)` |

Tests (`TestsWasserstein.lean`): the diagonal coupling, `W₁(μ, μ) = 0`, and `W₁(δₓ, δ_y) > 0` for `x ≠ y`.

The setting is the source's: Borel probability measures on a compact metric space. The equality (KR), the hard
direction, is the next piece: Monge-Kantorovich duality with an optimal coupling, whose proof here goes through the
Hahn-Banach theorem and the Riesz-Markov-Kakutani theorem, then the `c`-transform for the cost `d`.
