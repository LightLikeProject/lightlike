# Borel summability

## Abstract (Alpha)

This API is the start of the Nevanlinna–Sokal theorem on Borel summability, in the form proved by Benedetti, Gurau,
Keppler and Lettera (Theorem 1, Appendix B), whose proof represents the Borel transform by contour integrals along
vertical lines. It proves Hankel's formula on a vertical line (the integral of `e^{xw} w^{-k-1}` along `Re w = c`,
divided by `2πi`, is `x^k/k!` for `k ≥ 1`) and, for `f` analytic in the disk `C_R = {Re z⁻¹ > 1/R}` with Taylor
remainders `|f(z) - ∑_{k<q} a_k z^k| ≤ K q! ρ^{-q} |z|^q`, that the Borel transform `B(t) = ∑ a_k t^k/k!` converges for
`|t| < ρ` and equals, for `0 < x < ρ`, the vertical-line integral `b₀(x)` of the proof, which does not depend on the
line.

## Content (Alpha)

For `Re s > 0`, `∫_0^∞ t^k e^{-st} dt = k!/s^{k+1}`, by integration by parts [1]. The vertical line `Re w = c` is
parametrized as `w = c + 2πiξ`, so that `dw/(2πi) = dξ`; `‖c + 2πiξ‖^{-n}` is integrable for `n ≥ 2` and `c > 0`. The
Fourier transform of `t^k e^{-ct}` (`t > 0`, `0` for `t ≤ 0`) is its Laplace transform `k!/(c + 2πiξ)^{k+1}`, and
Fourier inversion gives Hankel's formula `∫ e^{x(c + 2πiξ)} (c + 2πiξ)^{-(k+1)} dξ = x^k/k!` for `k ≥ 1` and
`x, c > 0`, eq. (B.2) of the source for integer `k ≥ 1` [1] {1}.

A function analytic on a closed vertical strip and bounded there by `C/|w|²` has the same integral along its two
boundary lines, by Cauchy's theorem on rectangles [2]. For `f` analytic in `C_R` with `|f(z) - a₀| ≤ M|z|`, the
function `b₀(x) = a₀ + (1/2π) ∫ e^{x(c+iy)} (f((c+iy)⁻¹) - a₀)/(c+iy) dy` (eq. (B.3) in `w = z⁻¹`, the term `a₀` taken
out so that the integral converges absolutely) therefore does not depend on `c > 1/R` [2] {1}. Under the
hypotheses of the theorem (eq. (2.4) with `β = 0`), `|a_q| ≤ K q! ρ^{-q}` (eq. (B.1)), the Borel transform converges
for `|t| < ρ`, and along the line `Re w = c` the expansion of `f` up to order `n + 1` gives the partial sum of
`B(x)` up to `x^n` by Hankel's formula, with a remainder at most `(K/2) e^{xc} (n+1)!/(ρc)^{n+1}` (eqs. (B.4)-(B.5)).
On the line `c = (n+1)/x` and with Stirling's bound `(n+1)! ≤ e √(n+1) ((n+1)/e)^{n+1}` the remainder is at most
`(K/2) e (n+1) (x/ρ)^{n+1}`, so `b₀(x) = B(x)` for `0 < x < ρ` [3] {1}.

**Missing.** The rest of the proof of the Nevanlinna–Sokal theorem (the derivatives `b_m` of (B.6) and their bounds,
the continuation of `B` to the strip `{dist(t, ℝ₊) < ρ}` with its exponential bound (B.7), and the Laplace
reconstruction (B.8)) is not formalised yet.

## Lean References

1. Lightlike/FieldTheory/Borel/Hankel.lean - `FieldTheory.Borel.integral_pow_mul_cexp_neg`, `FieldTheory.Borel.vline`,
   `FieldTheory.Borel.integrable_inv_norm_vline_pow`, `FieldTheory.Borel.laplaceKernel`,
   `FieldTheory.Borel.fourier_laplaceKernel`, `FieldTheory.Borel.hankel_vertical`
2. Lightlike/FieldTheory/Borel/Contour.lean - `FieldTheory.Borel.integral_vertical_eq`, `FieldTheory.Borel.borelIntegrand`,
   `FieldTheory.Borel.borelZero`, `FieldTheory.Borel.borelZero_indep`
3. Lightlike/FieldTheory/Borel/Transform.lean - `FieldTheory.Borel.SokalHyp`, `FieldTheory.Borel.SokalHyp.norm_coeff_le`,
   `FieldTheory.Borel.borelT`, `FieldTheory.Borel.SokalHyp.hasSum_borelT`, `FieldTheory.Borel.hankel_vertical_y`,
   `FieldTheory.Borel.SokalHyp.norm_borelZero_sub_sum_le`, `FieldTheory.Borel.factorial_succ_le_stirling`,
   `FieldTheory.Borel.SokalHyp.borelZero_eq_borelT`

## References

1. D. Benedetti, R. Gurau, H. Keppler, D. Lettera, The small-N series in the zero-dimensional O(N) model:
   constructive expansions and transseries, arXiv:2210.14776v2, Theorem 1, eqs. (2.4)-(2.6), pp. 5-6; Appendix B,
   eqs. (B.1)-(B.8), pp. 24-25.
