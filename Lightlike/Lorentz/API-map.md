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

The irreducibility of the principal series is not yet formalized. [TODO]

Further results of this area in the results catalogue:
The spherical Plancherel theorem for SL(2,R): the spherical transform is a unitary equivalence from
L²(1,∞) onto L²(0,∞), with the density ρ tanh(πρ) [32]. The spherical Plancherel formula for SL(2,R) on
smooth compactly supported functions of the hyperbolic distance, with the density ρ tanh(πρ) [33]. For the K-type (l, r) of radial functions, the squared L² norm of the l-fold ladder image of the profile sinh^r ξ G^{(r)}(cosh ξ) is the Plancherel integral with the extra weights ∏_{k<l}((k+1/2)² + ρ²) and ∏_{k<r}((k+1/2)² + ρ²) [44]. The invariant measure of the upper half-plane is, in hyperbolic polar coordinates about i, sinh ξ dξ dφ, with φ the angle and ξ the hyperbolic distance [45]; the Haar measure of SL(2,ℝ), normalised by the Iwasawa chart, is in the Cartan coordinates k_α a(ξ) k_θ twice the product of sinh ξ dξ with dα on (-π/2, π/2) and dθ on a period [46]; over the full torus of angles in (0, 2π]² the factor 2 is absorbed [48]. Parseval's identity on the square (0,1]² holds for continuous functions [47], and with it the integral of |f|² against the Haar measure is (2π)² times the integral over ξ > 0 of sinh ξ times the sum of the squared moduli of the K × K Fourier components of f [49]. For a C¹ function of the four entries of g, the partial derivatives of its restriction to the coordinates k_α a(ξ) k_θ are expressed by the right derivatives in three fixed directions [50]; on the K × K Fourier components the sum and the difference A ± iB of two of them act as the raising and lowering ladder operators f' ∓ ((n cosh ξ − m)/(2 sinh ξ)) f, from the component (m, n) to (m, n ± 2) [51], and the integral of |A + iB|² is (2π)² times the integral over ξ > 0 of sinh ξ times the sum of the squared moduli of the raised components [52]. Since the element −1 of SL(2,ℝ) is a rotation by π that commutes with every a(ξ), the K × K Fourier component (m, n) of a continuous function vanishes when m − n is odd, so only the even components (m, n both even, integer K-types) and the odd ones (both odd, half-integer K-types) occur [53]. A classical solution G of the lowered ladder equation on (0, ∞) is orthogonal, in L²((0, ∞), sinh ξ dξ), to every ladder image of a C¹ function that vanishes for large ξ and whose product with G and sinh ξ tends to 0 at 0 [54]. Conversely, a function locally integrable on (0, ∞) that is orthogonal to the ladder images of all smooth compactly supported functions is almost everywhere a multiple of the kernel function sinh ξ^{-(l+1)} tanh(ξ/2)^{-r} of the lowered ladder, itself orthogonal to every such ladder image [55]. The
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
