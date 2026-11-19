# G3-089: Monge-Kantorovich duality and Kantorovich-Rubinstein

Source: W. Huang, R. Wang, Y. Wu, D. Meng, arXiv:2610.21070 (source key `huang-wang-wu-meng-2026`, location verified).

## Source locations (read)

| Piece | Source location | What it says | Lean |
|---|---|---|---|
| KR1 | Section 3.2.1, p. 5 | `Π(ν, η)`, `W₁ = inf_γ ∫ d dγ`; "the easy direction is immediate" | `Wasserstein.lean` |
| KR2 | Section 8.1, (8.1), p. 46 | finite transport problem: min over couplings = max over `a_i + b_j ≤ d(x_i, x_j)`, with a minimum attained | `MongeKantorovich.lean` |
| KR3 | Section 8.1, (8.2), p. 46 | for feasible `(a, b)`, `u_i = min_j (d(x_i, x_j) - b_j)` has `a_i ≤ u_i`, `u_i ≤ -b_i`, `|u_i - u_l| ≤ d(x_i, x_l)` | `ctrans`, `le_ctrans`, `ctrans_le_neg`, `lipschitzWith_ctrans` |
| KR3 | Section 3.7 (1), p. 16 | "the minimum distance-cost coupling equals the supremum of signed pairings over real unit Lipschitz tests" | `exists_optimal_coupling_dist` (the minimum is attained) |
| KR3 | Section 3.2.1, p. 5, (KR) | `inf_γ ∫ d dγ = sup_{Lip u ≤ 1} ∫ u d(ν - η)` on a compact metric space | `wasserstein1_eq_sSup` |

## Route

The source proves (KR) on a finite `δ`-net by linear-programming duality (8.1), the `c`-transform step (8.2) and a
`2δ` approximation. The proof here works on `X` directly: the functional
`ω(k) = inf {∫ f dμ + ∫ g dν | f, g ∈ C(X), k ≤ f ⊕ g}` is sublinear on `C(X × X)` and dominates every coupling; the
Hahn-Banach theorem extends `t k₀ ↦ t ω(k₀)` to a linear `L ≤ ω`, which is positive and has `L(f ∘ fst) = ∫ f dμ`,
`L(g ∘ snd) = ∫ g dν`; the Riesz-Markov-Kakutani theorem gives a measure `σ` with `∫ k dσ = L k`, a probability coupling
of `μ` and `ν` with `∫ k₀ dσ = ω(k₀)`. Taking `k₀ = -h` gives an optimal coupling for the cost `h` and the duality.
KR3 then applies the source's `c`-transform (8.2) on `X` instead of on the net.

The statements are for Borel probability measures on a compact metric space, the source's setting. KR2 holds for
every continuous cost; the source uses the cost `d` only.

Tests: `TestsMongeKantorovich.lean`, the separable cost `a(x) + b(y)`, whose dual value is `∫ a dμ + ∫ b dν`.
