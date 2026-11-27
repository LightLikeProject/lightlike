# The odd K-types of the Plancherel formula of SL(2,ℝ): the route

Notation as in `sl2r-plancherel-route.md`. The odd principal series `P^{1,iν}` (central character `-1`) has
`K`-types of odd weight. Its base block is the matrix coefficient `Φ^{odd}_ν(ξ) = ⟨e_0, π(a(ξ)) e_0⟩` between the
weight-`1` vector and itself (`oddCoeff`, `SL2ROddPlancherel/BaseCoefficient.lean`), the analogue of the spherical
coefficient of the even series. Its Plancherel density is `ρ coth(πρ)`, `ρ = ν/2` (Kitaev, arXiv:1711.08169,
Eq. (79) at `μ = 1/2`: `s sinh(2πs)/(cosh(2πs) + cos(2πμ)) = s coth(πs)`).

## What is proved (step O1)

* `oddCoeff_eq_integral`: `Φ^{odd}_ν(ξ) = ∫ (1 + u) u^{iρ-1} / (2 cosh(ξ/2) (1 + x²)) dx`, `u = u_ξ(x)` (the even
  spherical variable). So `Φ^{odd}` is a combination of two even spherical averages at the complex-shifted
  parameters `ν ± i`; this is why `tanh` becomes `coth` (`tanh(πρ + iπ/2) = coth(πρ)`).
* `oddCoeff_mehler`: `2 cosh(ξ/2) Φ^{odd}_ν(ξ) = ∫_{-ξ}^{ξ} e^{iρt} 2 cosh(t/2)/√(2(cosh ξ - cosh t)) dt`.
* `integral_sinh_mul_oddCoeff`: for `F` continuous with compact support and `G(v) = F(v)/√(2(1 + |v|))`,
  `∫_{ξ>0} sinh ξ F(cosh ξ) Φ^{odd}_ν(ξ) dξ = (1/2) ∫ e^{iρt} 2 cosh(t/2) 𝒜G(t) dt`, with `𝒜` the Abel transform.

## The odd base Plancherel identity (step O2): statement

For `F` smooth with compact support, `G = F/√(2(1+v))`, `g = 𝒜G` and `h(t) = 2 cosh(t/2) g(t)`,

  `π² ∫_{v>1} |F|² dv = ¼ ∫_{ρ>0} ρ coth(πρ) |ĥ(ρ)|² dρ`,   `ĥ(ρ) = ∫ e^{iρt} h(t) dt`,

with no discrete part (the Jacobi parameters of the weight `(1,1)` block are `(α, β) = (0, 1)`, and discrete
terms need `|β| > α + 1`). The constant is the same as in the even case `norm_sq_eq_sph`.

Evidence (not a proof): numerical integration (mpmath, 20 digits) for `F(v) = e^{-v}` gives `4π² ∫|F|² / ∫ρ coth|ĥ|² =
1.0000000000002` for the odd formula and the same ratio for the even formula with `tanh` and `h = 𝒜F`.

## Route for O2: complex contour shift from the even theorem

Write `a(z) = ∫ e^{izt} g(t) dt` (entire, even), `ã(z) = conj a(conj z)`, so `ĥ(ρ) = a(ρ - i/2) + a(ρ + i/2)`.

1. Expand `|ĥ|²` into the four products `a(ρ∓i/2) ã(ρ±i/2)`.
2. Shift the contour of each term by `±i/2`. `ρ coth(πρ)` becomes `(z ± i/2) tanh(πz)`, which has no pole between the
   two lines (the pole of `tanh` at `z = ∓i/2` on the old line is cancelled by the factor `z ± i/2`). The two terms
   `a(ρ∓i/2) ã(ρ∓i/2)` give `2 ∫ z tanh(πz) |a(z)|² dz`, the even norm of `G`.
3. For the mixed terms use the Abel transform of `vG`:
   `𝒜(vG)(t) = cosh t · g(t) + ½ ∫_{|t|}^∞ sinh s g(s) ds`, whose Fourier transform is
   `½ (a(ρ+i) + a(ρ-i)) + (a(ρ-i) - a(ρ+i))/(4iρ)` (the Legendre recursion `(2μ+1) v P_μ = (μ+1) P_{μ+1} + μ P_{μ-1}`).
   Polarising the even theorem for `(G, vG)` gives `∫ v |G|²`, and the two sides agree after the substitution
   `z → -z` (both `a` and `ã` are even).
4. Hence `2π² ∫ (1 + v) |G|² = ¼ ∫ ρ coth(πρ) |ĥ|² dρ`, which is the claim since `|F|² = 2(1 + v) |G|²`.

Needed analysis: rapid decay of `a(x + iy)` in `x`, uniformly for `|y| ≤ 1` (integration by parts, `g` smooth with
compact support); a contour-shift lemma for holomorphic functions on a closed strip with such decay (rectangle
integral and `R → ∞`, Mathlib `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`); the polarised even
theorem; the formula for `𝒜(vG)`.

## Step O3 (odd blocks from the base)

The raising and lowering ladders of the radial profiles, with half-integer `(l, r)`, carry the base block `(1/2, 1/2)`
to every odd block; the factor `(l + 1/2)² + ρ²` of the even recursion becomes an integer-shifted product
(`(k + 1)² + ρ²`). The interface needed by the assembly of all blocks is, per odd block `(m, n)`, an isometry from the
continuous part of `L²(0,∞)` onto the weighted `L²` with the density `ρ coth(πρ)`, equal on `√(sinh) χ` to
`ρ ↦ √(ρ coth(πρ)) ∫ χ conj Φ^{odd,2ρ}_{m,n} sinh`, plus the discrete part for `|β| > α + 1`.
