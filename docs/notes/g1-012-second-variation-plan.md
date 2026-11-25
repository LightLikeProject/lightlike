# Second variation of a null normal family: route and required lemmas

Goal: for a flow family `F (σ, t) = Γ (zS σ) t` of future null normal geodesics from a spacelike codimension-two
surface `S` (`FocalImpliesChron`), a degenerate Gram matrix `Q (σ₀, t₀)` with `0 < t₀ < L` puts `γ (L)` in `I⁺(S)`.

## Mathematical route

1. A degenerate `Q (σ₀, t₀)` gives a non-zero Jacobi field `J = Σ cᵢ ∂ᵢF (σ₀, ·)` with `J (t₀) = 0`, `J ⟂ γ'`,
   `J (0) ∈ T S`.
2. Let `W` be `J` on `[0, t₀]` and `0` on `[t₀, L]`, plus a small multiple of a field `η` with
   `η (t₀) = -J' (t₀)`. The index form `I (W, W) = ∫ (|W'|² - R (W, γ', γ', W)) dt - B (W (0), W (0))` is negative.
3. Let `N` be the parallel null field along `γ` with `g (γ', N) = -1`. For `α (s, t) = exp_{γ t} (s W + s² φ N)` the
   second-order coefficient of `g (∂ₜα, ∂ₜα)` is `|W'|² - R (W, γ', γ', W) - 2 φ'`. With `φ' = (1/2) (|W'|² - R) + δ`
   (`δ > 0`) and `φ (L) = 0`, the value `φ (0)` is forced; the boundary condition on `S` at order `s²` holds exactly
   when `I (W, W) + 2 δ L < 0`.
4. The family starts on `S` after a correction of order `s³` supported near `t = 0` and ends at `γ (L)`; for small
   `s ≠ 0` the curve `α (s, ·)` is a future timelike curve from `S` to `γ (L)`.

## Lemmas needed (none is in the repository)

* **L1 (parallel transport):** a parallel transverse null field along a geodesic of a manifold, across charts.
* **L2 (second-order expansion):** in one chart, `g (α) (α_t, α_t) = s² (|DW|² - R (W, γ', γ', W) - 2 φ') + O (s³)`
  uniformly in `t`, for `α (s, t) = γ t + s W t + s² Z t` with `Z = φ N + (second-order term of exp)`.
* **L3 (gluing):** a family `α (s, ·)` on `[0, L]` defined chartwise on a partition and matched at the nodes up to
  `O (s³)` corrections.
* **L4 (index form):** `I (J̃, J̃) = 0` for the broken Jacobi field and `I (J̃ + εη, J̃ + εη) < 0`.
* **L5 (start on `S`):** a curve in `S` with prescribed first and second order jet (from `exists_surface_param`).
* **L6 (conclusion):** a family of timelike curves from points of `S` to `γ L` gives `γ L ∈ I⁺(S)`.

## Size

L2 and L3 are the bulk: the second variation of `g (∂ₜα, ∂ₜα)` in coordinates and its transport across several
charts along `γ ([0, L])`.
