# Stationary phase for integrals with a complex phase

## Abstract (Alpha)

This API proves the stationary phase theorem for oscillatory integrals `∫ a(x) e^{iτφ(x)} dx` with a
complex phase `φ` whose imaginary part is nonnegative, a smooth compactly supported amplitude `a` and
finitely many nondegenerate critical points. The integral equals the sum, over the critical points,
of `e^{iτφ(x₀)} (2π/τ)^{n/2} det(−iH)^{−1/2} a(x₀)` up to a remainder of order `τ^{−n/2−1}`, the
square root being the product of the principal roots of the eigenvalues of `−iH`. Away from the
critical points the integral is of order `τ^{−k}` for every `k`. The proof is that of the source: a
Gaussian model integral and its Fourier transform, the quadratic-phase lemma, the reduction of a
general phase to its quadratic part by Hadamard's lemma and integration by parts, amplitudes that
vanish to high order, and a localisation by a partition of unity. A one-dimensional Laplace estimate
with an explicit uniform constant is included. Higher-order terms of the expansion are not stated.

## Content (Alpha)

The theorem is Theorem 7.7.5 of Hörmander {1}. For a smooth phase `φ` with `Im φ ≥ 0` on the support
of a smooth compactly supported amplitude `a`, whose critical points in the support (`Im φ = 0`,
`dφ = 0`) form a finite set `K` of nondegenerate points (`det(−iH) ≠ 0`), the leading term is
`Σ_{x₀ ∈ K} e^{iτφ(x₀)} (2π/τ)^{n/2} invSqrtDet(−iH(x₀)) a(x₀)` with error `O(τ^{−n/2−1})`
[1]. Critical points on the boundary of the support are allowed, with `Im φ ≥ 0` assumed on the
support only; the version with Hörmander's hypothesis, `Im φ ≥ 0` on an open set containing the
support, is a corollary [1]. The same holds on `Fin n → ℝ` [1], and for an amplitude supported near
one critical point that is not interior to its support [1]. For an amplitude supported in a small
ball around a nondegenerate critical point the proof reduces the phase to its quadratic part [2],
with Hadamard's lemma [9], amplitudes vanishing to high order [7] and flat functions [8].

Away from the critical points, the non-stationary phase estimate (Theorem 7.7.1 of {1}) gives
`O(τ^{−k})` for every `k` where `dF ≠ 0` or `Im F > 0`, and a smooth partition of unity localises the
integral to the critical points [3].

The model integral is the Gaussian with a complex symmetric quadratic form of positive definite real
part, equal to `(2π)^{n/2} invSqrtDet A` with the branch fixed by the product of the principal roots
of the eigenvalues, not by the principal root of the determinant [5]; its Fourier transform is the
complex Gaussian [6]. The quadratic-phase lemma (Lemma 7.7.3 of {1}) gives the leading term for a
quadratic phase [4]. A one-dimensional Laplace estimate with an explicit constant uniform in the
phase and the amplitude is proved for use by consumers whose phase depends on further parameters {2} [10].

Trust checks: a test phase `x²/2 + x³ + i x⁴` with one critical point reproduces the leading term
`(2π/τ)^{1/2} e^{iπ/4}` [11]; the hypothesis `dF ≠ 0` of the non-stationary estimate cannot be
dropped [12]; wrong constants in the Fourier transform of a Gaussian and in the Laplace estimate are
refuted [13] [14].

## Lean References

1. Lightlike/Oscillatory/StationaryPhase.lean - `Oscillatory.stationary_phase`,
   `Oscillatory.stationary_phase_of_isOpen`, `Oscillatory.stationary_phase_pi`,
   `Oscillatory.stationary_phase_pi_of_isOpen`, `Oscillatory.stationary_phase_local_boundary`,
   `Oscillatory.hess`
2. Lightlike/Oscillatory/PhaseReduction.lean - `Oscillatory.stationary_phase_local`,
   `Oscillatory.hessMat`, `Oscillatory.hessMat_eq`
3. Lightlike/Oscillatory/Localisation.lean - `Oscillatory.nonstationary_phase`,
   `Oscillatory.exists_bound_noncritical`, `Oscillatory.integral_localise`
4. Lightlike/Oscillatory/QuadraticPhase.lean - `Oscillatory.quadratic_phase`,
   `Oscillatory.quadratic_phase_base`, `Oscillatory.quadratic_phase_uniform`
5. Lightlike/Oscillatory/Gaussian.lean - `Oscillatory.integral_gauss_sq_mul_det`,
   `Oscillatory.integral_gauss_eq_invSqrtDet`, `Oscillatory.invSqrtDet`
6. Lightlike/Oscillatory/GaussFourier.lean - `Oscillatory.integral_gaussLin`
7. Lightlike/Oscillatory/Vanishing.lean - `Oscillatory.Vanish`, `Oscillatory.exists_bound_vanish`,
   `Oscillatory.exists_bound_quad`
8. Lightlike/Oscillatory/Flat.lean - `Oscillatory.flat_mul_divCoord`, `Oscillatory.vanish_of_flat`
9. Lightlike/Oscillatory/Hadamard.lean - `Oscillatory.hadamard`,
   `Oscillatory.contDiff_intervalIntegral_param`
10. Lightlike/Oscillatory/LaplaceRay.lean - `Oscillatory.laplace_ray_uniform`
11. Lightlike/Oscillatory/StationaryPhaseTests.lean - `Oscillatory.stationary_phase_testPhase`
12. Lightlike/Oscillatory/LocalisationTests.lean -
    `Oscillatory.nonstationary_phase_needs_noncritical`
13. Lightlike/Oscillatory/GaussFourierTests.lean - `Oscillatory.integral_gaussLin_wrong_constant`
14. Lightlike/Oscillatory/LaplaceRayTests.lean - `Oscillatory.laplace_ray_gaussian_wrong_constant`

## References

1. L. Hörmander, *The Analysis of Linear Partial Differential Operators I: Distribution Theory and
   Fourier Analysis*, 2nd ed., Springer-Verlag, 1990, §7.7, Theorems 7.7.1 and 7.7.5, Lemma 7.7.3.
2. F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Ch. 3, §7.
