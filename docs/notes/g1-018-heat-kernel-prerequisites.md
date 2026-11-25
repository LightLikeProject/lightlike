# GE8: what a general heat-trace theorem needs

The milestone GE8 asks for the expansion `Tr e^{-tD} ∼ Σ_k a_k t^{k-n/2}` of a Laplace-type operator `D` on a compact
Riemannian manifold, with `a₁ = (4π)^{-n/2} ∫ R/6` for `D = -Δ`. The library proves the coefficients on the round
spheres `S²`, `S³`, the flat tori, products and potential shifts (`Lightlike/Geometry/HeatKernel`), through the
explicit spectra. The definition `HasHeatExpansion` states the expansion for any trace function `K`. A statement for
an arbitrary compact manifold needs four prerequisites; each is listed with what exists.

1. **The operator on a manifold.** The Laplace–Beltrami operator `Δ f = div grad f` on smooth functions of a Riemannian
   manifold, with the Riemannian measure, and its symmetry `∫ g Δf = ∫ f Δg` on a closed manifold.
   Mathlib has the Laplacian of an inner product space (`Mathlib/Analysis/InnerProductSpace/Laplacian.lean`), not of a
   manifold. The library has the divergence theorem on a manifold with the metric measure written in charts
   (`Lightlike/Spacetime/EHManifold/ManifoldDivergence.lean`, `divergence_theorem_manifold`), which gives the symmetry
   once the operator is defined chart-wise by `(1/√det g) ∂ᵢ (√det g gⁱʲ ∂ⱼ f)`; the definition, its independence
   of the chart and the symmetry are not written.
2. **Discrete spectrum.** A self-adjoint realisation of `-Δ` on `L²(M)` with compact resolvent, hence eigenvalues of
   finite multiplicity tending to `∞`, so that `Tr e^{-tΔ} = Σ e^{-t λ_j}` makes sense. Mathlib has the spectral theory
   of compact self-adjoint operators, not Rellich compactness on a manifold, the Sobolev spaces or elliptic regularity.
3. **A parametrix.** The Seeley–DeWitt construction: a local Gaussian ansatz `(4πt)^{-n/2} e^{-d²/4t} Σ_k t^k u_k`, the
   transport equations for the `u_k` along geodesics (the exponential map and the Jacobian `det` of `exp` from
   `Lightlike/Geodesic/ExpDiffeo.lean` are the inputs) and the remainder estimate by Duhamel's formula. None of the
   three steps (the transport recursion, the Duhamel remainder bound, the passage from the local expansion of the kernel
   on the diagonal to the trace) is in Mathlib or the library.
4. **The coefficient.** `u₀ = 1` and `u₁ (x, x) = R(x)/6` from the second jet of `det exp` (the volume density in normal
   coordinates is `1 - Ric(v, v)/6 + …`), then `a₁ = (4π)^{-n/2} ∫ R/6`. The curvature side is on hand
   (`Lightlike.scalarCurvature`, and its value `n (n-1)` on the round sphere in `StereoCurvature.lean`); the volume density
   expansion in normal coordinates is not.

The first complete result along this route is a₁ on an arbitrary closed manifold given the existence of an expansion
with a fixed leading coefficient; it needs 1 and 2 to define the trace and 4 for the identification, and 3 only to
prove existence.

## The smallest case beyond the library

A flat torus `ℝⁿ/Λ` for a non-rectangular lattice `Λ` has the heat trace `Σ_{k∈ℤⁿ} e^{-t Q(k)}` with `Q` a positive
definite integral quadratic form, and the expansion `vol/(4πt)^{n/2}` with every further coefficient zero. The
step that Mathlib's one-variable Poisson summation does not give directly is the sum over one variable with a real
shift. `Lightlike.HeatKernel.tsum_exp_neg_shift` states it,
`Σ_n e^{-πa(n+s)²} = a^{-1/2} Σ_n e^{-πn²/a} e^{2π i n s}`, and `abs_tsum_shift_sub_le` bounds the difference of the
left side from `a^{-1/2}` by `a^{-1/2} Σ_{n≠0} e^{-πn²/a}`, uniformly in `s`. The remaining part of the lattice case
is the reduction of `Q` to a sum of squares of shifted linear forms (an `LDLᵀ` decomposition over `ℝ` and the reindexing
of `ℤⁿ` over the first variable), with the uniform error summed over the other variables; it is not written.
