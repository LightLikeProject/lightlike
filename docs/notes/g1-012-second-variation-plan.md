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

## Chart-level lemmas (proved)

* `hasDerivAt_normK`, `hasDerivAt_normK_second`: for a curve `c` and a field `Y` along it, in a chart,
  `d/ds g (c) (Y, Y) = 2 g (D_s Y, Y)` and the second derivative is `2 (g (K' + Γ (c', K), Y) + g (K, K))`.
* `coeffK_zero_eq`, `hasDerivAt_E_gpair`: at `s = 0` the coefficient of `s²` is
  `|D_t W|² - g (R (w, W) W, w) + d/dt g (E, w)` with `E = D_s α_s`, for a geodesic `t ↦ α (0, t)` with velocity `w`.
* `tidal_swap`: `g (R (w, W) W, w) = g (R (W, w) w, W)`.
* `uniform_neg_local`: if `g (α) (α_t, α_t)` has vanishing first `s`-jet and negative second-order coefficient at
  `(0, t₀)`, it is negative for `0 < |s|` small, uniformly for `t` near `t₀`.

## Route of the remaining lemmas

* The coefficient with `Z̃ = 0` is the intrinsic function `A_W (t) = (1/2) ∂ₛ² g (α₀) (∂ₜα₀, ∂ₜα₀)` of the
  intrinsic family `α₀ (s, t) = exp_{γ t} (s W t)`; it is the chart expression `|D_t W|² - g (R (w, W) W, w)` in
  every chart, so no transformation law across charts is needed.
* The correction `Z̃ = φ N` with `N = X / (-g (w, X))` for a smooth future timelike field `X` has `g (N, w) = -1`
  and `g (E, w) = -2 φ`; then the coefficient is `A_W - 2 φ'`, and `φ' = (1/2) A_W + δ` gives a negative coefficient
  `-2 δ`. The boundary conditions `φ (L) = 0` and the value of `φ (0)` fixed by the curve in `S` give the
  condition `I (W) + 2 δ L < Ψ₀`.
* For the Jacobi part, `A_J = d/dt g (D J, J) = (1/2) Q''`-type boundary terms through the intrinsic Gram function
  `Qg`; the kink field `η` and the correction at the start are supported in single charts.
* The family is `α (s, t) = Ξ ⟨γ t, s W + s² Z̃⟩` with `Ξ z = Γ z 1` from the smooth flow germ at the zero phase;
  homogeneity `Ξ ⟨p, λ v⟩ = Γ ⟨p, v⟩ λ` gives `D Ξ (p, 0) = id` and `D² Ξ (p, 0) (v, v) = -Γ (p) (v, v)`.
