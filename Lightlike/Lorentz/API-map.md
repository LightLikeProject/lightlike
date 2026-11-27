# SL(2,ℂ) and its unitary principal series

## Abstract (Alpha)

This API develops the harmonic analysis of SL(2,ℂ), the double cover of the restricted Lorentz
group, that Lorentzian spin foam models need: its Haar measure, the unitary principal series
representations labelled by a half-integer `k` and a real `ρ`, their Casimir operators, and the
decomposition of each principal series representation into irreducible representations of the
subgroup SU(2), the Plancherel formula of SL(2,ℂ) in its radial and full forms, and the
Lorentzian EPRL vertex amplitude with a proof that it is finite. For SL(2,ℝ) it gives the Haar
measure in the Iwasawa chart, the principal series on `L²(ℝ)` and the holomorphic discrete
series on the weighted Bergman spaces as strongly continuous unitary representations, and the
Casimir value of each.

## Content (Alpha)

SL(2,ℂ) is perfect, so its modular character is trivial and its left Haar measure is also right
invariant [1]. The principal series representation `(k, ρ)` acts on `L²(ℂ)` through Möbius
transformations and a multiplier, in the convention of Rühl {1} and of Barrett and collaborators
{2}. Each operator is unitary, the assignment is a group homomorphism [2], and the action is
jointly continuous [3].

On homogeneous functions on `ℂ²` of the matching degree, the two Casimir operators act as the
scalars `k² − ρ² − 1` and `kρ` [4].

Restricted to SU(2), the representation `(k, ρ)` is the Hilbert direct sum of the spins `|k| + ℓ`
for `ℓ ∈ ℕ`, each occurring exactly once [5].

An explicit Haar measure is the image of `|d|⁻² d⁶(b, c, d)` under the Bruhat chart
`(b, c, d) ↦ [[(1 + bc)/d, b], [c, d]]` [6]. Every element is `u diag(eʳ⁄², e⁻ʳ⁄²) v` with
`u, v ∈ SU(2)` [7]. Here `‖g‖² / 2 = cosh r`, with `r` the hyperbolic distance from the origin
to `g · o`, and the integral of a function of `t = cosh r` is `4π³ ∫_{t > 1} √(t² − 1) (·) dt`
[8]. The SU(2)-invariant vector of the representation `(0, ρ)` gives the spherical function
`sin(ρr) / (ρ sinh r)` [9], and for radial functions
`∫ |f|² dg = (2π⁴)⁻¹ ∫_{ρ > 0} ρ² |f̂(ρ)|² dρ` [10].

The full Plancherel formula {3} {4} is proved. In the variables of Perez and Rovelli {10} its constant is
`1/(32π⁴)`, which is four times smaller than the constant printed there; it agrees with Rühl {1} as
quoted by Simão {11}. The formula is stated with the
principal series `π_{n,ρ}` labelled by `n ∈ ℤ` and `ρ ∈ ℝ` (`n = 2k`), for functions that are
restrictions of smooth compactly supported functions on 2 × 2 complex arrays. Its ingredients are a
second chart adapted to the action on a fixed point `z` [11], derivatives of parametric integrals
[12], the integral kernel of `π_{n,ρ}(f)` on `L²(ℂ)` and the diagonal of the kernel of `f* ∗ f`
[13], and the SU(2) conjugation average `F♮` [14]. Let `Φ(μ)` be the integral of `F` over the upper
triangular matrices with diagonal `(μ, μ⁻¹)`. Harish-Chandra's limit formula {5} gives `∂ₜ² Φ(eᵗ) +
∂ₜ² Φ(eⁱᵗ) = −8π F(1)` at `t = 0` for SU(2)-invariant `F` [15], and the trace of `π_{n,ρ}(F)` is `π`
times a Mellin transform `M(n, ρ)` of `Φ` for `F♮` [16]. Fourier inversion against the density gives
`Σ_n ∫ (n² + 4ρ²) M(n, ρ) dρ = 16π³ F(1)` [17], hence the trace form `Σ_n ∫ (n² + 4ρ²) tr π_{n,ρ}(F)
dρ = 16π⁴ F(1)` and the Hilbert–Schmidt form `Σ_n ∫ (n² + 4ρ²) ‖π_{n,ρ}(f)‖²_HS dρ = 16π⁴ ∫ |f|² dg`
[18]. Without the density the sum of the traces is `2π³ Φ(1)` for `F♮`, and wrong densities or
constants give false statements [19]. In the labels `σ = 2ρ` of Perez and Rovelli {10} and with
their measure, which is `haarC`, the constant of the trace form is `1/(32π⁴)`, and with Rühl's
measure `(2π)⁻⁴ haarC` it is `1/2` {1} {11} [18]; the constant `1/(8π⁴)` of {10} gives four times
`F(1)` [19]. The operator `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg`, a Bochner integral in `L²(ℂ)`, acts
by the kernel `K_f`, so the Hilbert–Schmidt form is a statement about these operators, with
`‖π_{n,ρ}(f)‖²_HS` taken as `∫∫ |K_f|²`; that this double integral is the Hilbert–Schmidt norm is
not formalised [25]. An odd test function, which is not bi-SU(2)-invariant, has kernels of parity
`(−1)^{n+1}`, so its even terms vanish and some odd `n` contributes [19].

Every matrix coefficient between vectors with a pointwise bound `C (1 + |z|²)⁻¹` is bounded by
`C² I(g)`, where `I(g) = π r / sinh r` is the spherical kernel at `ρ = 0`; the SU(2)-adapted
vectors have such bounds. `I` lies in `L^{5/2}` of the Haar measure but not in `L²` [20]. The
EPRL vertex amplitude {6} {7} on the 4-simplex is an integral over `V₀, …, V₃ ∈ SL(2,ℂ)` with
`V₄ = 1` of a product over the ten links `ab` of matrix coefficients of
`π_{k,ρ}(V_a⁻¹ V_b)`; Hölder's inequality on the five stars bounds the integral of the product of
the ten kernels by `(∫ I^{5/2})⁴` [21]. The amplitude uses the labels `k = j`, `ρ = γ(j + 1)`
{8} and the vectors of the lowest SU(2) spin `j`, contracted with arbitrary intertwiner
coefficients as they stand, without the `ε` twist of the bra legs that the EPRL contraction of
invariant intertwiners uses, so it is not claimed to equal their amplitude; it is finite for every
`γ`, every spin assignment and all coefficients [22], the form of the finiteness theorem of Engle
and Pereira {7}, whose label `(n, ρ) = (2j, 2γj)` is `ρ = γj` here. For spins zero it is the
integral of ten
spherical functions, the Lorentzian Barrett–Crane kernel {9}; it is nonzero for `γ` near `0`;
without the gauge fixing `V₄ = 1` the dominating integral is infinite; and the second Casimir on
the EPRL vectors is `γ j(j + 1)`, which holds exactly for `ρ = γ(j + 1)` and so not for the label
`ρ = γj` [23]. Physlib's covering
map, reindexed to `Fin 4` with the signature `(−,+,+,+)`, preserves the project's `η`, and the
link variable `cosh r_ab` of the amplitude is `−η(N_a, N_b)` for the normals `N_a = Λ(V_a) e₀`,
unit future timelike vectors [24].

For SL(2,ℝ) {11}: the group is perfect, so its modular character is trivial, and the measure of
the Iwasawa chart is a multiple of Mathlib's Haar measure [26]. Weighted composition operators
`f ↦ c · (f ∘ T)` on `L²` come with criteria for unitarity and strong continuity [27]. The
principal series acts unitarily on `L²(ℝ)`, jointly continuously in `(g, f)` [28]. The holomorphic
discrete series acts unitarily on the weighted Bergman space `A²_n` of the upper half-plane, a
closed subspace that the action preserves and that is nonzero for `n ≥ 2` [29] [30]. The Casimir
operator is `-(1 + ν²)/4` on the principal series and `(n/2)(n/2 - 1)` on holomorphic functions,
attained by the nonzero vector `lowestVec n` of `A²_n` [31]. For the principal-series model with parameter
`ν = iτ`, no positive definite sesquilinear form on smooth functions has the generators skew when `|τ| > 1`,
and none when `τ = 1`, by the sign of the Casimir on the `K`-fixed vector; for `|τ| < 1` (the complementary
series) there is no such obstruction [42] [43].

The Taylor coefficients at 0 of a holomorphic function on the unit disc are the Fourier modes of its restriction
to a circle [62], and the disc integral of k(w) conj(w)^m ρ(|w|) is 2π a_m ∫ s^{2m+1} ρ [63]. For n ≥ 2 the vectors
e_k(z) = (z − i)^k (z + i)^{-(n+k)} of the weighted Bergman space `A²_n` are mutually orthogonal, by their rotation
character [64]; they are complete, have explicit norms and form an orthonormal Hilbert basis [65]. Two non-negative
power series with the same sum for every x with 0 ≤ x < 1 have the same coefficients [66]. The vector `D_n(diag(A, 1/A)) e_0` is the
coherent function (A z + i/A)^{-n}, whose pairing with e_k gives C(n−1+k, n−1) ‖e_k‖² = ‖e_0‖² [67]; the characters of
the box (0, 1]² are orthogonal [68]. The matrix coefficients ⟨e_j, D_n(g) e_k⟩ are K × K-eigenfunctions with a
single Fourier component [69]; the angular Fourier series of the coherent matrix coefficient [70] and its Plancherel
norm as a series over the K-weight pairs [71] give Schur orthogonality for the K-weight vectors [72]. Coefficients of
distinct K-weight pairs are orthogonal [73], Pythagoras holds for finite sums of mutually orthogonal L² functions [74],
and Schur orthogonality ∫ |⟨v, D_n(g) w⟩|² dg = (2π |c_0|² / ‖e_0‖²) ‖v‖² ‖w‖² holds for all v, w in `A²_n`, so that
the formal degree of `D_n` is (n − 1)/(8π²) [75]. The normalised coefficients form an orthonormal system of
`L²(SL(2,ℝ))`, and the squared norm of the projection of f onto its closed span is the sum of the squared inner
products [76]; this is d_n times the Hilbert–Schmidt norm of `D_n(f)`, the discrete series term of the Plancherel
formula [77]. The antiholomorphic series `D_n⁻` has the conjugate coefficients, which are orthogonal to those of
`D_{n'}⁺` [78].

At a(ξ) = diag(e^{ξ/2}, e^{-ξ/2}) the coefficient is ⟨e_j, D_n(a(ξ)) e_l⟩ = ‖e_j‖² cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2)), with
P_{jl} the j-th Taylor coefficient of (t + w)^l (1 + t w)^{-(n+l)} [79]. The profile polynomials are differentiable in t
[80] and satisfy the ladder relations of the generating function [81]; the radial profiles satisfy the ladder
equations ψ_{j,k+1}' + b ψ_{j,k+1} = (k+1) ψ_{jk}, ψ_{j0}' + b ψ_{j0} = 0 and ψ_{jl}' − b ψ_{jl} = −(n+l) ψ_{j,l+1} [82],
and decay like e^{-nξ/2} [83]. The profiles of `D_n` and `D_{n'}` with n ≠ n' and equal K × K-weights are orthogonal in
`L²((0, ∞), sinh ξ dξ)` [84]. In the ladder operators of the K-type equations the lowest weight profile is killed by the
raising operator for `D_n⁺` and by the lowering operator for `D_n⁻` [85]. The coefficients of distinct series are
orthogonal in `L²(SL(2,ℝ))`, by rotation invariance for different K × K-weights and by the radial Pythagoras identity
for equal weights [86] [87], and the radial `L²` norm of ⟨e_j, D_n(a(ξ)) e_k⟩ is 2 ‖e_j‖² ‖e_k‖² / (n − 1) [87]; the
coefficients of all holomorphic and antiholomorphic discrete series form an orthonormal system, and the squared norm of
the projection onto its closed span is the sum over all series of the squared norms of the projections onto the
isotypic subspaces, at most ‖f‖² [88]. The radial profile of `D_{2ν}⁻` of K-type (ν + k, −(ν + j)) is orthogonal to every
image of a test function under the (ν + k)-fold raising chain [89], and also to the images that are continuous on
the closed half-line and vanish only for large ξ [90]; this holds for chains with an offset a ∈ {0, 1/2} of the
K-type, i.e. for the radial profiles of `D_n⁻` for even and odd n alike [95].

The radial profiles are real for a real normalisation constant, because the Taylor coefficients at 0 of a function
holomorphic on the unit disc with h(conj w) = conj h(w) are real [93]. For s, l ≥ 1 the radial profiles of `D_{2ν}⁻`, 1 ≤ ν ≤
min(l, s), times √(sinh ξ) form an orthogonal basis of the discrete part of the (l, −s) block of the `K × K`
decomposition (`discSpan s l`) [94]; hence the sum over ν of the squared coefficients ⟨conj u_{(s−ν, l−ν)}, F⟩ equals
(2π)² times the squared norm of the projection of the block F_{(2s, 2l)} onto `discSpan s l` [94], and summing over all
blocks, the squared norms of the projections of F onto the even antiholomorphic discrete series add up to (2π)² times
the squared norms of the projections of the blocks onto their discrete parts; the same holds for the holomorphic
series applied to the complex conjugate of F [94].

Topological irreducibility of a unitary representation (the only closed invariant subspaces are 0 and
everything) follows from a complete family of K-weight vectors with pairwise distinct weights and a connected
linking graph (`⟪e_a, π(g) e_b⟫ ≠ 0` for some g) [96]. The holomorphic discrete series `D_n⁺` is irreducible for
every `n ≥ 2`, and so is `D_n⁻`, defined as `D_n⁺` composed with the automorphism `g ↦ JgJ`, `J = diag(1, −1)`,
which negates the K-weights [97]. For the principal series of both parities the vectors
`e_k(x) = (1 + x²)^{(iν−1−ε)/2} (x − i)^{k+ε} (x + i)^{−k}` of K-weight `2k + ε` are orthogonal eigenvectors of
the rotations [98], satisfy the ladder relation `x e_k' − w e_k = ((s − k)/2) e_{k+1} + ((s + k + ε)/2) e_{k−1}`,
and the matrix coefficient between neighbouring weights has derivative `(s − k) ‖e_{k+1}‖²` at 0, which vanishes
only for `ν = 0` and `1 + ε + 2k = 0` [99]; the weight vectors are complete in `L²(ℝ)` [100]. Hence the principal
series of SL(2,R) is irreducible for every real ν when the parity is even and for every ν ≠ 0 when it is odd; the
single excluded case, the odd series at ν = 0, is exactly where the linking argument breaks [101].

Further results of this area in the results catalogue:
The spherical Plancherel theorem for SL(2,R): the spherical transform is a unitary equivalence from
L²(1,∞) onto L²(0,∞), with the density ρ tanh(πρ) [32]. The spherical Plancherel formula for SL(2,R) on
smooth compactly supported functions of the hyperbolic distance, with the density ρ tanh(πρ) [33]. For the K-type (l, r) of radial functions, the squared L² norm of the l-fold ladder image of the profile sinh^r ξ G^{(r)}(cosh ξ) is the Plancherel integral with the extra weights ∏_{k<l}((k+1/2)² + ρ²) and ∏_{k<r}((k+1/2)² + ρ²) [44]. The invariant measure of the upper half-plane is, in hyperbolic polar coordinates about i, sinh ξ dξ dφ, with φ the angle and ξ the hyperbolic distance [45]; the Haar measure of SL(2,ℝ), normalised by the Iwasawa chart, is in the Cartan coordinates k_α a(ξ) k_θ twice the product of sinh ξ dξ with dα on (-π/2, π/2) and dθ on a period [46]; over the full torus of angles in (0, 2π]² the factor 2 is absorbed [48]. Parseval's identity on the square (0,1]² holds for continuous functions [47], and with it the integral of |f|² against the Haar measure is (2π)² times the integral over ξ > 0 of sinh ξ times the sum of the squared moduli of the K × K Fourier components of f [49]. For a C¹ function of the four entries of g, the partial derivatives of its restriction to the coordinates k_α a(ξ) k_θ are expressed by the right derivatives in three fixed directions [50]; on the K × K Fourier components the sum and the difference A ± iB of two of them act as the raising and lowering ladder operators f' ∓ ((n cosh ξ − m)/(2 sinh ξ)) f, from the component (m, n) to (m, n ± 2) [51], and the integral of |A + iB|² is (2π)² times the integral over ξ > 0 of sinh ξ times the sum of the squared moduli of the raised components [52]. Since the element −1 of SL(2,ℝ) is a rotation by π that commutes with every a(ξ), the K × K Fourier component (m, n) of a continuous function vanishes when m − n is odd, so only the even components (m, n both even, integer K-types) and the odd ones (both odd, half-integer K-types) occur [53]. A classical solution G of the lowered ladder equation on (0, ∞) is orthogonal, in L²((0, ∞), sinh ξ dξ), to every ladder image of a C¹ function that vanishes for large ξ and whose product with G and sinh ξ tends to 0 at 0 [54]. Conversely, a function locally integrable on (0, ∞) that is orthogonal to the ladder images of all smooth compactly supported functions is almost everywhere a multiple of the kernel function sinh ξ^{-(l+1)} tanh(ξ/2)^{-r} of the lowered ladder, itself orthogonal to every such ladder image [55]. Every smooth compactly supported function on (0, ∞) is the K-type (l, r) ladder image of a radial generator, so the K-type Plancherel identity holds for every test function of the block [56]. It extends to a linear isometry of L²(0, ∞), sending π √(sinh ξ) times the ladder image of G to √(ρ tanh(πρ) w_l w_r)/2 times the spherical transform of G [57]. For the opposite-sign K-types (l, -s) the ladder images of the radial generators satisfy the same identity, with the weights w_l w_s [58]. A test function of (0, ∞) is such an image exactly when it is orthogonal to the min(l, s) functions (cosh ξ − 1)^(i+s)/sinh^(l+s) ξ, l − s ≤ i < l, the discrete directions of the block [59] [60]. In L²(0, ∞) the closure of these images is the orthocomplement of the span of the discrete directions, and the weighted transform is isometric on them [61]. The K × K decomposition extends to all of L²(SL(2,R)): every F has components in L²(0, ∞) with ‖F‖² = (2π)² Σ_m ‖F_m‖² [91]. In an opposite-sign block, ‖H‖² is the square norm of the weighted transform of the continuous part plus the square norm of the projection onto the discrete directions [92]. The
massive one-particle representation of the Poincaré group, induced from SU(2): it preserves the L² norm,
is covariant under translations, has P² = m², W² = −m² s(s+1) and n+1 states per momentum [34]. The
massless one-particle representation of finite helicity h/2, induced from the character of ISO(2): it
preserves the L² norm of the light cone, has P² = 0, W = (h/2) P and W² = 0 [34]. The Pauli–Lubanski
square of the massive spin-n/2 representation is W² = −m² s(s+1), with s = n/2 and the signature
(+,−,−,−) [35]. The little groups of the Poincaré group: the stabilizer of the rest momentum m·1 in
SL(2,C) is SU(2) and is compact, and the stabilizer of the light-like momentum is the group of upper
triangular matrices with the phase character, with the translations as the kernel of the phase [36]. For
massless states of finite helicity the Pauli–Lubanski vector is W = (h/2) P [37]. The massive
one-particle representations of the Poincaré group on L²(d³p / 2ω_p) are irreducible: a closed subspace
invariant under all translations and all U(A) is 0 or everything [38]. The massless one-particle
representations of finite helicity on L²(d³p / 2|p|) are irreducible: a closed subspace invariant under
all translations and all helicity representations is 0 or everything [39]. The little group of a
tachyonic momentum is not compact: the stabilizer of the standard momentum (0, 0, 0, κ) contains the
boosts along the first spatial axis [40]. Wigner's classification of irreducible, strongly continuous,
unitary, positive-energy representations of the Poincaré group, stated as a precise proposition with a
non-vacuity check (stated, not proven) [41].

## Lean References

1. Lightlike/Lorentz/SL2C.lean - `Lorentz.SL2C.isPerfect`,
   `Lorentz.SL2C.modularCharacter_eq_one`, `Lorentz.SL2C.haar_isMulRightInvariant`,
   `Lorentz.SL2C.haar_univ`
2. Lightlike/Lorentz/PrincipalSeries.lean - `Lorentz.principalSeries`,
   `Lorentz.principalSeries_mem_unitary`, `Lorentz.principalSeries_mul`,
   `Lorentz.principalSeries_one`, `Lorentz.principalSeries_norm`, `Lorentz.principalSeries_inner`
3. Lightlike/Lorentz/Continuity.lean - `Lorentz.continuous_principalSeries`,
   `Lorentz.continuous_principalSeries_action`
4. Lightlike/Lorentz/Homogeneous.lean - `Lorentz.casimir1_eq`, `Lorentz.casimir2_eq`
5. Lightlike/Lorentz/SU2Decomposition.lean - `Lorentz.principalSeries_suV`,
   `Lorentz.principalSeries_isHilbertSum`, `Lorentz.intertwiner_eq_smul`,
   `Lorentz.intertwiner_eq_zero`
6. Lightlike/Lorentz/HaarChart.lean - `Lorentz.haarC`, `Lorentz.isHaarMeasure_haarC`
7. Lightlike/Lorentz/Cartan.lean - `Lorentz.exists_cartan`
8. Lightlike/Lorentz/Radial.lean - `Lorentz.coshDist`, `Lorentz.lintegral_coshDist`
9. Lightlike/Lorentz/Spherical.lean - `Lorentz.sphVec`, `Lorentz.inner_sphVec_eq_sphericalFn`
10. Lightlike/Lorentz/SphericalPlancherel.lean - `Lorentz.spherical_plancherel`
11. Lightlike/Lorentz/FixedChart.lean - `Lorentz.fixChart`, `Lorentz.haarC_eq_map_fixChart`
12. Lightlike/Lorentz/ParamIntegral.lean - `Lorentz.contDiff_parametric_integral_infty`
13. Lightlike/Lorentz/PlancherelKernel.lean - `Lorentz.psKernel`,
    `Lorentz.psKernel_selfConv_diag`
14. Lightlike/Lorentz/SU2Average.lean - `Lorentz.su2Avg`, `Lorentz.su2Avg_eq_self`
15. Lightlike/Lorentz/LimitFormula.lean - `Lorentz.orbInt`, `Lorentz.limit_formula`
16. Lightlike/Lorentz/PlancherelTrace.lean - `Lorentz.integral_psKernel_diag`
17. Lightlike/Lorentz/PlancherelFourier.lean - `Lorentz.hasSum_density_orbInt`
18. Lightlike/Lorentz/Plancherel.lean - `Lorentz.plancherel_trace`, `Lorentz.plancherel`
    `Lorentz.plancherel_trace_perezRovelli`, `Lorentz.plancherel_trace_ruhl`,
    `Lorentz.mult_eq_prMult`, `Lorentz.integral_haarC_eq_bruhat`
19. Lightlike/Lorentz/PlancherelTests.lean - `Lorentz.hasSum_trace_flat`,
    `Lorentz.testLF_wrong_density`, `Lorentz.testLF_wrong_constant`,
    `Lorentz.testLF_perezRovelli_constant`, `Lorentz.psKernel_odd`, `Lorentz.testOdd_plancherel`
20. Lightlike/Lorentz/KernelBound.lean - `Lorentz.norm_inner_principalSeries_le`,
    `Lorentz.exists_decaysWith_suV`, `Lorentz.lintegral_kernelE_rpow_lt_top`,
    `Lorentz.lintegral_kernelE_sq_eq_top`
21. Lightlike/Lorentz/StarBound.lean - `Lorentz.gauge`, `Lorentz.lintegral_star`,
    `Lorentz.lintegral_linkProd_le`, `Lorentz.lintegral_linkProd_kernelE_lt_top`
22. Lightlike/Lorentz/EPRL.lean - `Lorentz.eprlVec`, `Lorentz.eprlVertex`,
    `Lorentz.integrable_linkProd_inner`, `Lorentz.integrable_eprlIntegrand`,
    `Lorentz.eprlVertex_eq_integral`, `Lorentz.lintegral_enorm_eprlIntegrand_lt_top`
23. Lightlike/Lorentz/EPRLTests.lean - `Lorentz.eprlVertex_spinZero`,
    `Lorentz.exists_pos_eprlVertex_spinZero_ne_zero`, `Lorentz.lintegral_linkProd_ungauged_eq_top`,
    `Lorentz.casimir2_eprlVec_fun`, `Lorentz.casimir2_hvec_eq_iff`,
    `Lorentz.casimir2_wrong_label_ne`
24. Lightlike/Lorentz/Signature.lean - `Lorentz.lorentzMat`,
    `Lorentz.lorentzMat_transpose_mul_eta_mul_self`, `Lorentz.coshDist_inv_mul`
25. Lightlike/Lorentz/PlancherelOperator.lean - `Lorentz.piOp`, `Lorentz.inner_piOp`,
    `Lorentz.coeFn_piOp`, `Lorentz.plancherel_piOp`
26. Lightlike/Lorentz/SL2R.lean - `Lorentz.SL2R.isPerfect`,
    `Lorentz.SL2R.modularCharacter_eq_one`, `Lorentz.SL2R.exists_iwasawa`,
    `Lorentz.SL2R.haarR_eq_smul`, `Lorentz.SL2R.integral_haarR`
27. Lightlike/Lorentz/WeightedComp.lean - `Lorentz.weightedCompL2`,
    `Lorentz.mem_unitary_of_inner`, `Lorentz.continuous_of_dense_coeff`,
    `Lorentz.continuous_action_of_norm`
28. Lightlike/Lorentz/SL2RPrincipal.lean - `Lorentz.SL2R.principalSeries`,
    `Lorentz.SL2R.principalSeries_mem_unitary`, `Lorentz.SL2R.continuous_principalSeries_action`
29. Lightlike/Lorentz/SL2RDiscrete.lean - `Lorentz.SL2R.discreteAction`,
    `Lorentz.SL2R.discreteAction_mem_unitary`, `Lorentz.SL2R.discreteAction_mem_holoSubmodule`
30. Lightlike/Lorentz/SL2RBergman.lean - `Lorentz.SL2R.isClosed_holoSubmodule`,
    `Lorentz.SL2R.discreteSeries`, `Lorentz.SL2R.discreteSeries_mem_unitary`,
    `Lorentz.SL2R.holoSubmodule_ne_bot`, `Lorentz.SL2R.continuous_discreteSeries`
31. Lightlike/Lorentz/SL2RCasimir.lean - `Lorentz.SL2R.casimir_principal`,
    `Lorentz.SL2R.commutator_principal`, `Lorentz.SL2R.casimir_discrete`,
    `Lorentz.SL2R.casimir_lowestVec`
32. Lightlike/Lorentz/SL2RPlancherel/SphericalSurjective.lean -
    `Lorentz.SL2RPlancherel.sphericalL2Equiv`, `Lorentz.SL2RPlancherel.surjective_sphericalL2`
33. Lightlike/Lorentz/SL2RPlancherel/SphericalClean.lean - `Lorentz.SL2RPlancherel.norm_sq_eq_sph`
34. Lightlike/Lorentz/PoincareIrreps/Classification.lean - `Lorentz.Poincare.wigner_massive`,
    `Lorentz.Poincare.wigner_massless`
35. Lightlike/Lorentz/PoincareIrreps/PauliLubanski.lean - `Lorentz.Poincare.pauliLubanski_square`,
    `Lorentz.Poincare.momentum_dot_pauliLubanski`, `Lorentz.Poincare.spinJ_casimir`
36. Lightlike/Lorentz/PoincareIrreps/Momentum.lean - `Lorentz.Poincare.stabilizer_restMom`,
    `Lorentz.Poincare.isCompact_stabilizer_restMom`, `Lorentz.Poincare.mem_stabilizer_lightMom`,
    `Lorentz.Poincare.mem_ker_phase`
37. Lightlike/Lorentz/PoincareIrreps/MasslessPL.lean - `Lorentz.Poincare.lightPL_eq`,
    `Lorentz.Poincare.lightPL_square`, `Lorentz.Poincare.helChar_upper`
38. Lightlike/Poincare/ShellSourceMeasure.lean - `Poincare.irreducible_massive_sourceMeasure`
39. Lightlike/Poincare/ConeSourceMeasure.lean - `Poincare.irreducible_massless_coneSourceMeasure`
40. Lightlike/Poincare/LittleGroups.lean - `Poincare.boost_mem_littleGroup_tachyon`,
    `Poincare.not_isCompact_littleGroup_tachyon`
41. Lightlike/Lorentz/PoincareIrreps/ClassificationStatement.lean -
    `Lorentz.Poincare.WignerClassification`, `Lorentz.Poincare.trivialRep_classified`
42. Lightlike/Lorentz/SL2RPlancherel/NoInvariantFormBoundary.lean -
    `Lorentz.SL2RPlancherel.eq_zero_of_casimir_zero`,
    `Lorentz.SL2RPlancherel.no_invariant_form_smooth_boundary`: no positive definite skew form for `τ = 1`
43. Lightlike/Lorentz/SL2RPlancherel/NoInvariantForm.lean - `Lorentz.SL2RPlancherel.no_invariant_form`,
    `Lorentz.SL2RPlancherel.no_invariant_form_smooth`: no positive definite skew form for `|τ| > 1`
44. Lightlike/Lorentz/SL2RPlancherel/KTypeLR.lean - `Lorentz.SL2RPlancherel.norm_sq_ktype_lr`,
    `Lorentz.SL2RPlancherel.Nform_succ`, `Lorentz.SL2RPlancherel.LRClaim_all`
45. Lightlike/Lorentz/SL2RPlancherel/HyperbolicPolar.lean -
    `Lorentz.SL2R.lintegral_upperHalfPlane_polar`, `Lorentz.SL2R.lintegral_tanh_half`
46. Lightlike/Lorentz/SL2RPlancherel/PolarIntegral.lean -
    `Lorentz.SL2R.lintegral_haarR_polar`, `Lorentz.SL2R.smul_I_polar`
47. Lightlike/Lorentz/SL2RPlancherel/TorusParseval.lean - `Lorentz.SL2RPlancherel.hasSum_sq_box`
48. Lightlike/Lorentz/SL2RPlancherel/PolarTorus.lean - `Lorentz.SL2R.lintegral_haarR_torus`
49. Lightlike/Lorentz/SL2RPlancherel/KKParseval.lean -
    `Lorentz.SL2RPlancherel.lintegral_norm_sq_eq_kk`
50. Lightlike/Lorentz/SL2RPlancherel/SmoothRight.lean - `Lorentz.SL2R.hasDerivAt_kakP_theta`,
    `Lorentz.SL2R.hasDerivAt_kakP_xi`, `Lorentz.SL2R.hasDerivAt_kakP_alpha`
51. Lightlike/Lorentz/SL2RPlancherel/LadderComponents.lean - `Lorentz.SL2R.kk_ladder_up`,
    `Lorentz.SL2R.kk_ladder_down`
52. Lightlike/Lorentz/SL2RPlancherel/LadderNorm.lean - `Lorentz.SL2R.lintegral_norm_sq_raise`
53. Lightlike/Lorentz/SL2RPlancherel/ParityKK.lean - `Lorentz.SL2R.kkCoeff_eq_zero_of_odd`
54. Lightlike/Lorentz/SL2RPlancherel/LadderOrth.lean - `Lorentz.SL2RPlancherel.ladUp_orth_ker`
55. Lightlike/Lorentz/SL2RPlancherel/LadderComplete.lean -
    `Lorentz.SL2RPlancherel.ae_eq_const_mul_ladKer_of_orth`,
    `Lorentz.SL2RPlancherel.integral_ladUp_mul_ladKer`, `Lorentz.SL2RPlancherel.ladDown_ladKer`
56. Lightlike/Lorentz/SL2RPlancherel/LadderSurjective.lean -
    `Lorentz.SL2RPlancherel.exists_hLR_eq`, `Lorentz.SL2RPlancherel.norm_sq_eq_of_isTest`
57. Lightlike/Lorentz/SL2RPlancherel/KTypeBlockL2.lean - `Lorentz.SL2RPlancherel.blockL2`,
    `Lorentz.SL2RPlancherel.norm_blockL2`, `Lorentz.SL2RPlancherel.blockL2_apply`
58. Lightlike/Lorentz/SL2RPlancherel/KTypeOpposite.lean - `Lorentz.SL2RPlancherel.norm_sq_ktype_opp`
59. Lightlike/Lorentz/SL2RPlancherel/LadderOppositeSurjective.lean - `Lorentz.SL2RPlancherel.exists_hLRN_eq`
60. Lightlike/Lorentz/SL2RPlancherel/LadderOppositeOrth.lean - `Lorentz.SL2RPlancherel.integral_hLRN_mul_phiN`
61. Lightlike/Lorentz/SL2RPlancherel/KTypeOppositeL2.lean - `Lorentz.SL2RPlancherel.closure_range_blockEN`,
    `Lorentz.SL2RPlancherel.norm_blockFN`
62. Lightlike/Lorentz/SL2RPlancherel/DiscCircleMode.lean - `Lorentz.SL2RPlancherel.discCoeff`,
    `Lorentz.SL2RPlancherel.integral_circleMap_mode`, `Lorentz.SL2RPlancherel.eq_zero_of_discCoeff_eq_zero`:
    the Taylor coefficients of a holomorphic function on the unit disc as circle Fourier modes
63. Lightlike/Lorentz/SL2RPlancherel/DiscMode.lean - `Lorentz.SL2RPlancherel.integral_ball_mode`: the disc
    integral of k(w) conj(w)^m ρ(|w|) is 2π a_m ∫ s^{2m+1} ρ
64. Lightlike/Lorentz/SL2RPlancherel/DiscreteBasis.lean - `Lorentz.kVec`, `Lorentz.kClass`,
    `Lorentz.discreteAction_rot_kClass`, `Lorentz.kClass_orthogonal`: the K-weight vectors
    (z - i)^k (z + i)^{-(n+k)} of the weighted Bergman space A²_n and their rotation character
65. Lightlike/Lorentz/SL2RPlancherel/DiscreteBasisComplete.lean -
    `Lorentz.SL2RPlancherel.inner_kClass_holo`, `Lorentz.SL2RPlancherel.kClass_complete`,
    `Lorentz.SL2RPlancherel.norm_sq_kClass`, `Lorentz.SL2RPlancherel.kBasis`: completeness of the K-weight
    vectors, their norms, and the orthonormal Hilbert basis of A²_n
66. Lightlike/Lorentz/SL2RPlancherel/NonnegSeriesUnique.lean - `Lorentz.SL2RPlancherel.coeff_eq_of_hasSum`: two
    non-negative power series with the same sum on [0, 1) have the same coefficients
67. Lightlike/Lorentz/SL2RPlancherel/DiscreteCoherent.lean - `Lorentz.SL2RPlancherel.cohFun`,
    `Lorentz.SL2RPlancherel.discreteAction_diag_lowest`, `Lorentz.SL2RPlancherel.inner_kClass_diag_lowest`,
    `Lorentz.SL2RPlancherel.choose_mul_norm_sq_kClass`: D_n(diag(A, 1/A)) e₀ is the coherent function
    (A z + i/A)^{-n}, its pairing with e_k, and C(n-1+k, n-1) ‖e_k‖² = ‖e₀‖²
68. Lightlike/Lorentz/SL2RPlancherel/BoxCharacter.lean - `Lorentz.SL2RPlancherel.integral_box_char`: orthogonality of
    the characters on the box (0,1]²
69. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurK.lean - `Lorentz.SL2RPlancherel.mcoef`,
    `Lorentz.SL2RPlancherel.mcoef_rot`, `Lorentz.SL2RPlancherel.kkCoeff_mcoef`,
    `Lorentz.SL2RPlancherel.lintegral_norm_sq_mcoef`: the matrix coefficients of the K-weight vectors are
    K × K-eigenfunctions with a single Fourier component
70. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurCoh.lean - `Lorentz.SL2RPlancherel.hasSum_inner_rot`,
    `Lorentz.SL2RPlancherel.hasSum_kkProfile_coh`, `Lorentz.SL2RPlancherel.kkCoeff_coh`: the angular Fourier
    series of the coherent matrix coefficient and its K × K components
71. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurKfin.lean - `Lorentz.SL2RPlancherel.lintegral_norm_sq_coh`: the
    Plancherel norm of the coherent matrix coefficient as a series over the K-weight pairs
72. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurKfinal.lean -
    `Lorentz.SL2RPlancherel.lintegral_norm_sq_mcoef_kvec`: Schur orthogonality for the K-weight vectors of D_n⁺
73. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurOrth.lean - `Lorentz.SL2RPlancherel.integral_mcoef_orth`:
    matrix coefficients of distinct K-weight pairs are orthogonal in L²(SL(2,ℝ))
74. Lightlike/Lorentz/SL2RPlancherel/OrthSumL2.lean -
    `Lorentz.SL2RPlancherel.lintegral_norm_sq_sum_of_orth`: Pythagoras for finite sums of mutually orthogonal L²
    functions
75. Lightlike/Lorentz/SL2RPlancherel/DiscreteSchurAll.lean - `Lorentz.SL2RPlancherel.schurRatio`,
    `Lorentz.SL2RPlancherel.lintegral_norm_sq_mcoef_finite`, `Lorentz.SL2RPlancherel.lintegral_norm_sq_mcoef_eq`:
    Schur orthogonality ∫ |⟨v, D_n(g) w⟩|² dg = (2π|c₀|²/‖e₀‖²) ‖v‖² ‖w‖² for all v, w in A²_n
76. Lightlike/Lorentz/SL2RPlancherel/DiscreteProjection.lean - `Lorentz.SL2RPlancherel.uFun`,
    `Lorentz.SL2RPlancherel.uLp_orthonormal`, `Lorentz.SL2RPlancherel.discreteSpace`,
    `Lorentz.SL2RPlancherel.norm_sq_starProjection_discrete`: the normalised matrix coefficients of D_n⁺ form an
    orthonormal system of L²(SL(2,ℝ)) and the squared norm of the projection onto its closed span is the sum of
    the squared inner products
77. Lightlike/Lorentz/SL2RPlancherel/DiscretePlancherelTerm.lean - `Lorentz.SL2RPlancherel.formalDegree`,
    `Lorentz.SL2RPlancherel.schurRatio_eq`, `Lorentz.SL2RPlancherel.norm_sq_starProjection_discrete_eq`: the
    formal degree d_n = (n-1)/(8π²) and the discrete series term of the Plancherel formula, ‖P_n f‖² = d_n Σ
    |∫ f conj(⟨ê_j, D_n(g) ê_l⟩) dg|²
78. Lightlike/Lorentz/SL2RPlancherel/DiscreteMinus.lean - `Lorentz.SL2RPlancherel.integral_mcoef_mul_mcoef`,
    `Lorentz.SL2RPlancherel.uLpBar`, `Lorentz.SL2RPlancherel.inner_uLp_uLpBar`,
    `Lorentz.SL2RPlancherel.discreteSpace_orthogonal_bar`: the antiholomorphic series D_n⁻ by conjugation (its
    coefficients are the conjugates of those of D_n⁺) and the orthogonality of the coefficients of D_n⁺ and D_n'⁻ in
    L²(SL(2,ℝ)) (opposite K-weights)
79. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfile.lean - `Lorentz.SL2RPlancherel.genFun`,
    `Lorentz.SL2RPlancherel.profPoly`, `Lorentz.SL2RPlancherel.mcoef_aR`: the matrix coefficient of the K-weight
    vectors of D_n⁺ at a(ξ) in closed form, ⟨e_j, D_n(a(ξ)) e_l⟩ = ‖e_j‖² cosh(ξ/2)^(-n) P_jl(tanh(ξ/2)), P_jl the
    j-th Taylor coefficient of (t + w)^l (1 + t w)^(-(n+l))
80. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileLadder.lean - `Lorentz.SL2RPlancherel.hasDerivAt_profPoly`:
    the profile polynomials are differentiable in t, with derivative the Taylor coefficient of the t-derivative of
    the generating function (differentiation under the Cauchy integral)
81. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileRel.lean - `Lorentz.SL2RPlancherel.profPoly_lower`,
    `Lorentz.SL2RPlancherel.profPoly_lower_zero`, `Lorentz.SL2RPlancherel.profPoly_raise`: the ladder relations
    t(1-t²) P' + (l(1+t²) - j(1-t²)) P_jl = 2 l t P_{j,l-1} and
    t(1-t²) P' + (j(1-t²) - l(1+t²) - 2 n t²) P_jl = -2 (n+l) t P_{j,l+1} for the profile polynomials
82. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileODE.lean - `Lorentz.SL2RPlancherel.profileFun`,
    `Lorentz.SL2RPlancherel.ladB`, `Lorentz.SL2RPlancherel.profileFun_up`, `Lorentz.SL2RPlancherel.profileFun_up_zero`,
    `Lorentz.SL2RPlancherel.profileFun_down`, `Lorentz.SL2RPlancherel.profile_eq_mcoef`: the radial profiles
    ψ_jl(ξ) of the discrete series satisfy ψ_{j,k+1}' + b ψ_{j,k+1} = (k+1) ψ_jk, ψ_j0' + b ψ_j0 = 0 and
    ψ_jl' - b ψ_jl = -(n+l) ψ_{j,l+1}, b = ((n+2l) cosh ξ - (n+2j))/(2 sinh ξ)
83. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileDecay.lean - `Lorentz.SL2RPlancherel.norm_profPoly_le`,
    `Lorentz.SL2RPlancherel.norm_profileFun_le`: the Cauchy bound for the profile polynomials and the decay
    |ψ(ξ)| ≤ C e^(-nξ/2) of the radial profiles
84. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfilePair.lean - `Lorentz.SL2RPlancherel.profPair`,
    `Lorentz.SL2RPlancherel.profPair_eq_zero_of_ne`: the radial profiles of D_n⁺ and D_n'⁺, n ≠ n', with equal
    K × K-weights are orthogonal in L²((0,∞), sinh ξ dξ) (integration by parts along the ladder)
85. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileLadderForm.lean - `Lorentz.SL2RPlancherel.ladUp_profileFun_zero`,
    `Lorentz.SL2RPlancherel.ladUp_profileFun_succ`, `Lorentz.SL2RPlancherel.ladDown_profileFun`,
    `Lorentz.SL2RPlancherel.ladDown_profileFun_zero_minus`: the radial profiles of the discrete series in the ladder
    operators of the K-type equations: the lowest weight profile is killed by the raising operator (D_n⁺) and by the
    lowering operator (D_n⁻)
86. Lightlike/Lorentz/SL2RPlancherel/DiscreteInnerOrth.lean - `Lorentz.SL2RPlancherel.integral_mcoef_orth_gen`,
    `Lorentz.SL2RPlancherel.integral_norm_sq_block`, `Lorentz.SL2RPlancherel.integral_re_eq_zero_of_pythag`: tools for
    the orthogonality of distinct discrete series: coefficients with different K × K-weights are orthogonal (rotation
    invariance), the Plancherel identity in the K × K-components for a single-weight function as a real integral, and
    the Pythagoras criterion for Re ∫ F conj G = 0
87. Lightlike/Lorentz/SL2RPlancherel/DiscreteOrthDifferent.lean - `Lorentz.SL2RPlancherel.inner_uLp_uLp_ne`,
    `Lorentz.SL2RPlancherel.integral_sinh_norm_sq_mcoef_aR`: the normalised matrix coefficients of D_n⁺ and D_n'⁺ are
    orthogonal in L²(SL(2,ℝ)) for n ≠ n' (equal K × K-weights: radial Pythagoras from the orthogonality of the profiles;
    different weights: rotation invariance), and the radial L² norm of ⟨e_j, D_n(a(ξ)) e_k⟩
88. Lightlike/Lorentz/SL2RPlancherel/DiscretePlancherelTotal.lean - `Lorentz.SL2RPlancherel.discFam_orthonormal`,
    `Lorentz.SL2RPlancherel.norm_sq_starProjection_discreteAll`,
    `Lorentz.SL2RPlancherel.norm_sq_starProjection_discreteAll_le`: the normalised coefficients of all holomorphic and
    antiholomorphic discrete series form an orthonormal system of L²(SL(2,ℝ)); the squared norm of the projection onto
    its closed span is the sum over all series of the squared norms of the projections onto the isotypic subspaces
    (the discrete part of the Plancherel formula), at most ‖f‖²
89. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileImages.lean - `Lorentz.SL2RPlancherel.integral_ladUp_mul_conj`,
    `Lorentz.SL2RPlancherel.integral_ladUpChain_mul_profile`: the lowering operator is adjoint to the raising operator on
    test functions, and the radial profile of the antiholomorphic series D_{2ν}⁻ of K-type (ν + k, -(ν + j)) is orthogonal
    to every image of a test function under the (ν + k)-fold raising chain
90. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileBdry.lean -
    `Lorentz.SL2RPlancherel.integral_ladUp_mul_conj_of_cont`,
    `Lorentz.SL2RPlancherel.integral_chain_mul_conj_eq_zero`: the same orthogonality for chains of ladder images that
    are continuous on [0, ∞) and vanish for large ξ but not near 0 (the images of the radial generators),
    `Lorentz.SL2RPlancherel.integral_chain_mul_conj_eq_zero_off`: the same with an offset a of the K-type
91. Lightlike/Lorentz/SL2RPlancherel/KKL2.lean - `Lorentz.SL2RPlancherel.kkL2`,
    `Lorentz.SL2RPlancherel.norm_sq_eq_tsum_kkL2`, `Lorentz.SL2RPlancherel.inner_eq_tsum_kkL2`
92. Lightlike/Lorentz/SL2RPlancherel/KTypeOppositeIso.lean - `Lorentz.SL2RPlancherel.blockL2N`,
    `Lorentz.SL2RPlancherel.norm_sq_eq_cont_add_disc`
93. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileReal.lean - `Lorentz.SL2RPlancherel.conj_discCoeff`,
    `Lorentz.SL2RPlancherel.conj_profPoly`, `Lorentz.SL2RPlancherel.conj_profileFun`: the profile polynomials and the
    radial profiles of the discrete series are real
94. Lightlike/Lorentz/SL2RPlancherel/DiscreteBlock.lean - `Lorentz.SL2RPlancherel.span_psiVec_eq_discSpan`,
    `Lorentz.SL2RPlancherel.sum_norm_sq_inner_uLpBar`, `Lorentz.SL2RPlancherel.tsum_norm_sq_discreteBar_even`,
    `Lorentz.SL2RPlancherel.tsum_norm_sq_discrete_even`: the discrete part of the opposite-sign blocks is spanned by the
    radial profiles of `D_{2ν}⁻`, and the even discrete series part of the Plancherel formula, block by block
95. Lightlike/Lorentz/SL2RPlancherel/DiscreteProfileChain.lean -
    `Lorentz.SL2RPlancherel.integral_chain_mul_profile_eq_zero`: ladder chain images with an offset a ∈ {0, 1/2} are
    orthogonal to the radial profiles of `D_n⁻`, n = 2(a + ν)

96. Lightlike/Lorentz/SL2RIrreducible/Criterion.lean - `Lorentz.SL2R.IsTopologicallyIrreducible`,
    `Lorentz.SL2R.isTopologicallyIrreducible_of_weights`, `Lorentz.SL2R.isTopologicallyIrreducible_comp`
97. Lightlike/Lorentz/SL2RIrreducible/Discrete.lean - `Lorentz.SL2R.discreteSeries_isIrreducible`,
    `Lorentz.SL2R.discreteSeriesMinus`, `Lorentz.SL2R.discreteSeriesMinus_rot`,
    `Lorentz.SL2R.discreteSeriesMinus_isIrreducible`
98. Lightlike/Lorentz/SL2RIrreducible/PrincipalWeights.lean - `Lorentz.SL2R.weightVec`,
    `Lorentz.SL2R.principalSeries_rot_weightL2`, `Lorentz.SL2R.inner_weightL2_of_ne`
99. Lightlike/Lorentz/SL2RIrreducible/PrincipalLadder.lean - `Lorentz.SL2R.ladder_weightVec`,
    `Lorentz.SL2R.hasDerivAt_diagPairing`, `Lorentz.SL2R.exists_inner_ne_zero`
100. Lightlike/Lorentz/SL2RIrreducible/PrincipalComplete.lean - `Lorentz.SL2R.weightL2_complete`
101. Lightlike/Lorentz/SL2RIrreducible/Principal.lean - `Lorentz.SL2R.principalSeries_isIrreducible`,
    `Lorentz.SL2R.weightExp_sub_eq_zero_iff`, `Lorentz.SL2R.exists_weightExp_sub_eq_zero_iff`

## References

1. W. Rühl, *The Lorentz Group and Harmonic Analysis*, W. A. Benjamin, 1970.
2. J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann, R. Pereira, Lorentzian spin foam
   amplitudes: graphical calculus and asymptotics, *Class. Quantum Grav.* 27 (2010) 165009.
3. I. M. Gel'fand, M. A. Naimark, Unitary representations of the Lorentz group, *Izv. Akad. Nauk
   SSSR Ser. Mat.* 11 (1947) 411–504.
4. M. A. Naimark, *Linear Representations of the Lorentz Group*, Pergamon, 1964.
5. A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton University Press, 1986.
6. J. Engle, E. Livine, R. Pereira, C. Rovelli, LQG vertex with finite Immirzi parameter,
   *Nucl. Phys. B* 799 (2008) 136–149, arXiv:0711.0146.
7. J. Engle, R. Pereira, Regularization and finiteness of the Lorentzian loop quantum gravity
   vertices, *Phys. Rev. D* 79 (2009) 084034, arXiv:0805.4696.
8. Y. Ding, C. Rovelli, Physical boundary Hilbert space and volume operator in the Lorentzian
   new spin-foam theory, arXiv:1006.1294 (2010).
9. J. W. Barrett, L. Crane, A Lorentzian signature model for quantum general relativity,
   *Class. Quantum Grav.* 17 (2000) 3101, arXiv:gr-qc/9904025.
10. A. Perez, C. Rovelli, 3+1 spinfoam model of quantum gravity with spacelike and timelike
    components, arXiv:gr-qc/0011037 (2000), App. A.
11. J. D. Simão, Investigations on Lorentzian spin-foams and semiclassical space-times, PhD
    thesis, Friedrich-Schiller-Universität Jena, 2024, arXiv:2405.01360, App. B.
