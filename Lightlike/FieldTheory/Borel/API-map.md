# Borel summability

## Abstract (Alpha)

This API is the start of the Nevanlinna–Sokal theorem on Borel summability, in the form proved by Benedetti, Gurau,
Keppler and Lettera (Theorem 1, Appendix B), whose proof represents the Borel transform by contour integrals along
vertical lines. It proves the Laplace transform of `t^k` for a complex rate and Hankel's formula on a vertical line:
the integral of `e^{xw} w^{-k-1}` along `Re w = c`, divided by `2πi`, is `x^k/k!` for `k ≥ 1`.

## Content (Alpha)

For `Re s > 0`, `∫_0^∞ t^k e^{-st} dt = k!/s^{k+1}`, by integration by parts [1]. The vertical line `Re w = c` is
parametrized as `w = c + 2πiξ`, so that `dw/(2πi) = dξ`; `‖c + 2πiξ‖^{-n}` is integrable for `n ≥ 2` and `c > 0`. The
Fourier transform of `t^k e^{-ct}` (`t > 0`, `0` for `t ≤ 0`) is its Laplace transform `k!/(c + 2πiξ)^{k+1}`, and
Fourier inversion gives Hankel's formula `∫ e^{x(c + 2πiξ)} (c + 2πiξ)^{-(k+1)} dξ = x^k/k!` for `k ≥ 1` and
`x, c > 0`, eq. (B.2) of the source for integer `k ≥ 1` [1] {1}.

**Missing.** The rest of the proof of the Nevanlinna–Sokal theorem (the function `b_0` of (B.3) and its independence
of the contour, its identification with the Borel transform, the continuation to the strip and the Laplace
reconstruction (B.8)) is not formalised yet.

## Lean References

1. Lightlike/FieldTheory/Borel/Hankel.lean - `FieldTheory.Borel.integral_pow_mul_cexp_neg`, `FieldTheory.Borel.vline`,
   `FieldTheory.Borel.integrable_inv_norm_vline_pow`, `FieldTheory.Borel.laplaceKernel`,
   `FieldTheory.Borel.fourier_laplaceKernel`, `FieldTheory.Borel.hankel_vertical`

## References

1. D. Benedetti, R. Gurau, H. Keppler, D. Lettera, The small-N series in the zero-dimensional O(N) model:
   constructive expansions and transseries, arXiv:2210.14776v2, Theorem 1, eqs. (2.4)-(2.6), pp. 5-6; Appendix B,
   eqs. (B.1)-(B.8), pp. 24-25.
