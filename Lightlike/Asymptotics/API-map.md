# Saddle points of the 6j symbol

## Abstract (Alpha)

This API studies Racah's single-sum formula for the 6j symbol as an oscillatory sum and locates
its saddle points. For the six edge lengths of a tetrahedron it relates the saddle points to the
tetrahedron's geometry: they are complex exactly when the tetrahedron is Euclidean, the phase at
the saddle has the Regge action as its imaginary part, and its second derivative there is given
by the volume. A steepest-descent evaluation of the sum then proves the Ponzano–Regge
asymptotic formula for the 6j symbol of every Euclidean tetrahedron.

## Content (Alpha)

The saddle points of the phase of Racah's sum {1} are the roots of a quadratic whose discriminant
is `−576` times the squared volume of the tetrahedron, so they are complex conjugate exactly when
the squared volume is positive [1]. The saddle point is a root of that quadratic [1].

For a Euclidean tetrahedron the derivative of the phase vanishes at the saddle [1]. The real part
of the phase there is the rate of the prefactor, and its imaginary part is the Regge action
`Σₑ ℓₑ θₑ` {2} [1]. The second derivative of the phase at the saddle, times the product of the
face sums, is `−24 i √vol2` [1]. For lengths that do not form a Euclidean tetrahedron the
analysis is shown not to apply [2].

For the steepest-descent proof the phase is continued to the closed upper half-plane: it is
continuous up to the real axis, where its imaginary part is an explicit piecewise-linear
function, holomorphic inside, its derivative vanishes only at the saddle, and it behaves like
`−2πiz` at infinity [3]. The descent flow `z' = −1/ψ'(z)` lowers `Re ψ` at unit rate and keeps
`Im ψ` fixed; from every point below the saddle level its solution exists until it lands on the
real axis [5]. The proof uses an escape lemma for maximal solutions of autonomous differential
equations, which Mathlib lacks [4]. At the saddle the phase obeys a cubic Taylor bound, the
saddle is nondegenerate, and the two valleys contain rays along which `Re ψ` falls
quadratically and whose end points reach every nearby level of `Im ψ` [8]. Between the largest
face sum and the smallest quadrilateral sum the phase continues holomorphically across the real
axis with `Im ψ' = π`, so no descent path lands there [10]. Descent paths from the end points
of opposite valley rays land at two different real points: a common landing point would let a
primitive of `e^{Nψ}` on a disc compare the two half-Gaussians of Laplace's method, which add,
with an exponentially smaller bound along the paths [12]. Hence the saddle level `Im ψ(s)` lies
strictly between `π` times every face sum and `π` times every quadrilateral sum, and the two
descent paths land on opposite sides of the middle interval [14]. Racah's sum is a contour
integral: the kernel `π T(z) / sin(πz)`, with `T` entire and built from `1/Γ`, has residue
Racah's term at each integer, and for real `x₁` left of the largest face sum and `x₂` right of
the smallest quadrilateral sum the kernel has a primitive `Φ` on the closed upper half-plane
minus the integers, continuous at `x₁` and `x₂`, with `racahSum = −Im (Φ(x₂) − Φ(x₁)) / π` [16].
The factors of that kernel are bounded uniformly through the Stirling exponent
`f(w) = w log w − w`: `‖1/Γ(w + ½)‖ ≤ exp(3/(4‖w‖) − Re f(w))` for every `w` with `‖w‖² ≥ 2`,
the left half-plane by reflection with `Re f(−w) = −Re f(w) − π |Im w|`, and
`‖Γ(w + ½)‖ ≤ √(2π) exp(3/(4‖w‖) + Re f(w))` for `Re w ≥ 0`; with absolute constants the bounds
hold for all `w` [18]. Together they bound the kernel itself: for every `c > 0` there is a
constant `C`, independent of the spins, with `|π T(z) / sin(πz)| ≤ C exp(Re ψ(z + 3/2))` for
`Im z > 0` wherever `Im z ≥ c`, or `Re z` lies left of a face sum, or right of a quadrilateral
sum, minus `½`; `ψ` is the continued phase of the lengths `J + ½`. The proof shifts each face
factor by `½`, at a cost of at most `log 2` (sharp at `−¼`), and near the real axis pairs
`sin(πz)` with one `1/Γ` factor by reflection [20].
The lengths of the limit are `ℓ = λj + ½ = λ m_λ` with `m_λ = j + 1/(2λ) → j`, and the phase
scales exactly: for real `c > 0`, `ψ_{cl}(cz) = c ψ_l(z)` (the `c log c` terms cancel because
`ΣA = ΣB`), `ψ'` has degree 0 on the upper half-plane, `ψ''` degree −1, the saddle point degree 1
and the squared volume degree 6; Euclidean tetrahedra form an open set that is closed under
rescaling, so `m_λ` and `ℓ` are Euclidean for all large `λ` when `j` is [22].
The descent paths land strictly inside the outer intervals: one in `(0, A_max)`, the other right
of `B_min`, since `bdry` takes the values `π A_max` and `π B_min` at the ends of the middle piece
and is at least `π ΣA > π B_min` on `(−∞, 0]`. The phase `(m, z) ↦ ψ_m(z)` is jointly continuous
on `ℝ⁶ × H̄`, so `ψ_m → ψ_j` uniformly on compact subsets of the closed upper half-plane as
`m → j`, and the saddle point and the phase at the saddle depend continuously on the lengths of
a Euclidean tetrahedron [24].
On the vertical line through the saddle, `sin(Im ψ'(x + iy))` has the sign of a quadratic in
`y²` whose roots are `(Im s)²` and one more point, so `Im ψ'` changes sign only at the saddle and
`Re ψ` has a strict minimum there along the line: every other point of the open upper half-plane
with the real part of the saddle has `Re ψ > Re ψ(s)`, and no descent path from the saddle
crosses the line [26].
The descent direction `saddleDir l = exp(i (Σᵢ arg(s − Aᵢ)/2 − π/4))` satisfies `b u₀² = −‖b‖`
for `b = ψ''(s)/2` and has positive real part; the descent path leaving `s` along `+saddleDir`
lands beyond some `Bₖ` and the one along `−saddleDir` in `(0, Aᵢ)`, which fixes the orientation
of the contour [28]. The valley rays have a radius and a cubic constant that depend only on lower
bounds for `Im s` and `‖b‖`, and `s`, `b` and `saddleDir` are continuous in the lengths, so near
a Euclidean tetrahedron the rays work with one set of constants [30].
On the upper half-plane, after the rescaling `z = Nw − 3/2`, Racah's kernel has the exact leading
form `(2π)² N² K(Nw − 3/2) = e^{N ψ(w)} P(w) (1 + O(1/N))`, with an explicit amplitude `P` and one
constant for all spins whose rescaled face and quadrilateral sums stay bounded [32].
Along a valley ray `t ↦ s + tv` the increment of the rescaled primitive `F(w) = Φ(Nw − 3/2)` is
half of a Gaussian: `(2π)² N^{3/2} e^{−N ψ(s)} (F(s + rv) − F(s)) = ε P(s) u₀ √(π/‖b‖)/2 +
O(N^{−1/2})`, uniformly in the data, and for a Euclidean tetrahedron
`P(s) u₀ = e^{−iπ/4}/√(∏ᵢ |s − Aᵢ|)` with `‖b‖ ∏ᵢ |s − Aᵢ| = 12 √V` [34]. The outer pieces of
the contour, from the ends of the rays along the steepest-descent lines to real points near the
landing points, are `O(λ e^{λ(D_λ − δ)})`, exponentially below the saddle contribution of size
`λ^{−3/2} e^{λ D_λ}`; adding the four pieces gives the asymptotics
of Racah's sum, `V^{1/4} e^{−λ c} R(λj) − cos(S_R(ℓ) + π/4)/(√(12π) (2π)²) → 0` for every
Euclidean tetrahedron with integer edges `j` and `ℓ = λj + ½`, and with it the Ponzano–Regge
formula `√(12π √V²(ℓ)) {λj} − cos(S_R(ℓ) + π/4) → 0` without hypotheses [36].
Trust checks are in [6], [7], [9], [11], [13], [15], [17], [19], [21], [23], [25], [27], [29],
[31], [33], [35] and [37].

The Morse lemma with parameters: a smooth function of a variable and a parameter with a critical point at the origin for every parameter near a base value and a nondegenerate Hessian at the base value is, in coordinates that depend smoothly on the parameter, its value at the origin plus half the Hessian of the base value; the coordinate change is a local diffeomorphism. The proof is Hadamard's lemma with a smooth parameter, which makes the remainder a smooth family of self-adjoint endomorphisms equal to the identity at the base point, followed by a smooth square root of such endomorphisms near the identity from the inverse function theorem; composing with Sylvester's law gives the diagonal form with signs, and the number of negative signs is the index of the Hessian; the function x cubed at the origin has no such chart [38].

A positive measure on the half line whose Laplace transform grows like `e^{a/β}` in the logarithmic sense, `β log L(β) → a > 0` as `β → 0⁺`, has a counting function with `log F(X) / (2 √(a X)) → 1`: a logarithmic Tauberian theorem of Ingham type, the growth behind the Cardy formula [41] {3}. The upper bound is the saddle estimate `F(X) ≤ e^{β X} L(β)`, from the window estimates of the Laplace transform [39] {3}. For the lower bound the Laplace transform is split into three windows around the saddle `x = a / β²`; the outer two are bounded by the Laplace transform at slightly different `β`, so the middle window carries at least half of `L(β)` [40] {3}. The theorem is weaker than Ingham's, which gives the asymptotics of `F` itself; Ingham's theorem with the power correction is open.

Karamata's Tauberian theorem for a regularly varying Laplace transform is proved: if `L(β) ~ β^{-α} ℓ(1/β)` as `β → 0⁺` with `α > 0` and `ℓ` slowly varying (eventually positive, `ℓ(c t)/ℓ(t) → 1` for every `c > 0`), then the counting function `F(t)` satisfies `F(t) / (t^α ℓ(t)) → 1/Γ(α+1)` [42]. The proof scales the Laplace transform [42], evaluates polynomials in `exp(-x/t)` against the measure [43], extends to continuous functions by Weierstrass approximation, with limit functional `∫ e^{-x} k(e^{-x}) x^{α-1}/Γ(α) dx` [44], and sandwiches the indicator of the interval from `0` to `t` between two continuous ramp functions [45], whose limit values tend to `1/Γ(α+1)` [46]. Lebesgue measure (`α = 1`, `ℓ = 1`) returns the exact value `1`. The comparison of the statement with the literature is pending: no source was opened at a cited location.

## Lean References

1. Lightlike/Asymptotics/Saddle.lean - `Asymptotics.disc_eq`, `Asymptotics.saddle_root`,
   `Asymptotics.IsEuclid.dphase_saddle`, `Asymptotics.IsEuclid.re_phase_saddle`,
   `Asymptotics.IsEuclid.im_phase_saddle`, `Asymptotics.IsEuclid.d2phase_saddle`
2. Lightlike/Asymptotics/Tests.lean - `Asymptotics.not_isEuclid_lorentzian`,
   `Asymptotics.saddleQ_lorentzian`
3. Lightlike/Asymptotics/Contour.lean - `Asymptotics.phaseC`, `Asymptotics.im_phaseC_ofReal`,
   `Asymptotics.continuousOn_phaseC`, `Asymptotics.hasDerivAt_phaseC`,
   `Asymptotics.IsEuclid.norm_dphaseC_ge`, `Asymptotics.norm_phaseC_add_le`
4. Lightlike/Asymptotics/Lift.lean - `Asymptotics.IsLift`, `Asymptotics.IsLift.eqOn`,
   `Asymptotics.exists_isLift`, `Asymptotics.exists_isLift_tendsto_not_mem`
5. Lightlike/Asymptotics/Descent.lean - `Asymptotics.descentField`,
   `Asymptotics.IsEuclid.phaseC_lift`, `Asymptotics.IsEuclid.re_phaseC_saddle`,
   `Asymptotics.IsEuclid.exists_descent`
6. Lightlike/Asymptotics/ContourTests.lean - `Asymptotics.bdry_regular_ne_naive`,
   `Asymptotics.phaseC_unbalanced_not_le`
7. Lightlike/Asymptotics/DescentTests.lean - `Asymptotics.escape_one`,
   `Asymptotics.not_bdd_lifetime_univ`, `Asymptotics.exists_descent_regular`
8. Lightlike/Asymptotics/Valley.lean - `Asymptotics.d2phaseC`,
   `Asymptotics.norm_phaseC_taylor_le`, `Asymptotics.IsEuclid.d2phaseC_saddle_ne_zero`,
   `Asymptotics.valleyDir`, `Asymptotics.exists_valley`, `Asymptotics.IsEuclid.exists_valley`
9. Lightlike/Asymptotics/ValleyTests.lean - `Asymptotics.d2phaseC_saddle_regular`,
   `Asymptotics.exists_re_phaseC_gt`, `Asymptotics.exists_valley_regular`
10. Lightlike/Asymptotics/Landing.lean - `Asymptotics.phaseM`,
   `Asymptotics.phaseC_eq_phaseM`, `Asymptotics.im_dphaseM_ofReal`,
   `Asymptotics.eventually_phaseC_ne_add_pos`, `Asymptotics.not_tendsto_middle`,
   `Asymptotics.IsEuclid.exists_descent_outside`
11. Lightlike/Asymptotics/LandingTests.lean - `Asymptotics.dphaseM_regular`,
   `Asymptotics.im_phaseM_regular`, `Asymptotics.not_eventually_phaseC_ne_add_pos_right`,
   `Asymptotics.exists_descent_outside_regular`
12. Lightlike/Asymptotics/Closing.lean - `Asymptotics.exists_ball_superset_of_isCompact`,
   `Asymptotics.primitive_sub_eq_integral`, `Asymptotics.IsEuclid.norm_primitive_lift_sub_le`,
   `Asymptotics.laplace_valley`, `Asymptotics.IsEuclid.not_landing_eq`,
   `Asymptotics.IsEuclid.exists_landing_ne`
13. Lightlike/Asymptotics/ClosingTests.lean - `Asymptotics.lead_eq_half_gaussian`,
   `Asymptotics.landing_eq_same_valley_regular`, `Asymptotics.exists_landing_ne_regular`
14. Lightlike/Asymptotics/Level.lean - `Asymptotics.eq_of_bdry_eq_of_not_mem`,
   `Asymptotics.IsEuclid.level_bounds`, `Asymptotics.IsEuclid.pi_faceSum_lt_level`,
   `Asymptotics.IsEuclid.landing_sides`
15. Lightlike/Asymptotics/LevelTests.lean - `Asymptotics.level_regular`,
   `Asymptotics.bdry_regular_twice`, `Asymptotics.landing_sides_regular`
16. Lightlike/Asymptotics/ContourIdentity.lean - `Asymptotics.exists_primitive_im_sub`,
   `Asymptotics.racahT`, `Asymptotics.racahKernel`, `Asymptotics.racahT_eq_Gamma`,
   `Asymptotics.racahT_natCast`, `Asymptotics.tendsto_mul_racahKernel`,
   `Asymptotics.racahSum_eq_im_primitive`
17. Lightlike/Asymptotics/ContourIdentityTests.lean - `Asymptotics.racahSum_regular`,
   `Asymptotics.racahT_regular`, `Asymptotics.tendsto_mul_racahKernel_regular`,
   `Asymptotics.im_log_pole_wrong`, `Asymptotics.im_primitive_regular`,
   `Asymptotics.racahKernel_intCast`
18. Lightlike/Asymptotics/GammaBounds.lean - `Asymptotics.re_stirF_neg`,
   `Asymptotics.norm_cos_le_exp_abs_im`, `Asymptotics.abs_re_stirF_le`,
   `Asymptotics.Gamma_half_add_mul_Gamma_half_sub`, `Asymptotics.norm_inv_Gamma_half_add_le`,
   `Asymptotics.norm_Gamma_half_add_le`, `Asymptotics.exists_norm_inv_Gamma_half_add_le`,
   `Asymptotics.exists_norm_Gamma_half_add_le`
19. Lightlike/Asymptotics/GammaBoundsTests.lean - `Asymptotics.re_stirF_I`,
   `Asymptotics.Gamma_half_mul_self`, `Asymptotics.re_stirF_neg_wrong`,
   `Asymptotics.norm_Gamma_bounds_two_I`, `Asymptotics.stirF_zero`,
   `Asymptotics.inv_Gamma_neg_nat`
20. Lightlike/Asymptotics/KernelBound.lean - `Asymptotics.re_xlog_le_re_xlog_add_half`,
   `Asymptotics.exists_inv_norm_sin_pi_mul_le`, `Asymptotics.exists_norm_Gamma_half_add_le_of_im`,
   `Asymptotics.pi_div_norm_sin_mul_norm_inv_Gamma_sub`,
   `Asymptotics.pi_div_norm_sin_mul_norm_inv_Gamma_natCast_sub`, `Asymptotics.kernelExp`,
   `Asymptotics.exists_norm_racahKernel_le_kernelExp`, `Asymptotics.kernelExp_le_re_phase`,
   `Asymptotics.exists_norm_racahKernel_le`
21. Lightlike/Asymptotics/KernelBoundTests.lean - `Asymptotics.re_xlog_half_shift_sharp`,
   `Asymptotics.re_xlog_half_shift_wrong`, `Asymptotics.racahKernel_bound_ones`,
   `Asymptotics.re_xlog_zero`
22. Lightlike/Asymptotics/Homogeneity.lean - `Asymptotics.faceSum_smul`,
   `Asymptotics.quadSum_smul`, `Asymptotics.xlog_ofReal_mul`, `Asymptotics.phaseC_smul_add`,
   `Asymptotics.phaseC_smul`, `Asymptotics.phaseC_faceSum_smul`, `Asymptotics.phase_smul`,
   `Asymptotics.dphaseC_smul`, `Asymptotics.d2phase_smul`, `Asymptotics.qa_smul`,
   `Asymptotics.qb_smul`, `Asymptotics.vol2l_smul`, `Asymptotics.saddle_smul`,
   `Asymptotics.isEuclid_smul_iff`, `Asymptotics.lengthsDir`, `Asymptotics.lengths_eq_smul`,
   `Asymptotics.tendsto_lengthsDir`, `Asymptotics.isOpen_isEuclid`,
   `Asymptotics.eventually_isEuclid_lengths`
23. Lightlike/Asymptotics/HomogeneityTests.lean - `Asymptotics.saddle_two_regular`,
   `Asymptotics.saddle_two_regular_eq`, `Asymptotics.isEuclid_two_regular`,
   `Asymptotics.im_phase_two_regular`, `Asymptotics.im_phase_two_regular_of_smul`,
   `Asymptotics.phaseC_smul_wrong`, `Asymptotics.dphaseC_smul_zero`,
   `Asymptotics.exists_isEuclid_lengths_ones`
24. Lightlike/Asymptotics/UniformContour.lean - `Asymptotics.bdry_of_nonpos`,
   `Asymptotics.pos_lt_of_bdry_eq`, `Asymptotics.lt_of_bdry_eq_right`,
   `Asymptotics.IsEuclid.landing_strict_left`, `Asymptotics.IsEuclid.landing_strict_right`,
   `Asymptotics.IsEuclid.landing_sides_strict`, `Asymptotics.continuousOn_phaseC_lengths`,
   `Asymptotics.eventually_norm_phaseC_sub_lt`,
   `Asymptotics.eventually_norm_phaseC_lengthsDir_sub_lt`, `Asymptotics.continuous_qa`,
   `Asymptotics.continuous_qb`, `Asymptotics.continuousOn_saddle`,
   `Asymptotics.continuousOn_phaseC_saddle`, `Asymptotics.tendsto_saddle_lengthsDir`,
   `Asymptotics.tendsto_phaseC_saddle_lengthsDir`
25. Lightlike/Asymptotics/UniformContourTests.lean - `Asymptotics.landings_regular`,
   `Asymptotics.bdry_unbalanced_zero`, `Asymptotics.landing_sides_strict_regular`,
   `Asymptotics.saddle_lengthsDir_ones`, `Asymptotics.exists_uniform_ball_regular`,
   `Asymptotics.saddle_zero`, `Asymptotics.not_isEuclid_zero`
26. Lightlike/Asymptotics/Ridge.lean - `Asymptotics.ridgePoly_eq`,
   `Asymptotics.sin_im_dphaseC_vertical`, `Asymptotics.tendsto_im_dphaseC_vertical`,
   `Asymptotics.continuousOn_im_dphaseC_vertical`, `Asymptotics.hasDerivAt_re_phaseC_vertical`,
   `Asymptotics.im_dphaseC_vertical_sign`, `Asymptotics.re_phaseC_vertical_gt`,
   `Asymptotics.IsEuclid.re_phaseC_vertical_gt`,
   `Asymptotics.IsEuclid.re_phaseC_saddle_lt_of_re_eq`
27. Lightlike/Asymptotics/RidgeTests.lean - `Asymptotics.ridgeCoeffs_regular`,
   `Asymptotics.ridgePoly_regular`, `Asymptotics.ridgePoly_regular_roots`,
   `Asymptotics.ridgePoly_unbalanced`, `Asymptotics.ridgePoly_unbalanced_not_quadratic`,
   `Asymptotics.re_phaseC_vertical_gt_regular`, `Asymptotics.im_dphaseC_zero_regular`
28. Lightlike/Asymptotics/Orientation.lean - `Asymptotics.saddleCoeff`,
   `Asymptotics.saddleDir`, `Asymptotics.norm_saddleDir`, `Asymptotics.d2phaseC_saddle_eq`,
   `Asymptotics.IsEuclid.saddleCoeff_ne_zero`, `Asymptotics.prod_saddle_sub_faceSum`,
   `Asymptotics.saddleDir_sq`, `Asymptotics.saddleDir_sq_mul_norm`,
   `Asymptotics.IsEuclid.mul_saddleDir_sq`, `Asymptotics.arg_le_arg_sub_ofReal`,
   `Asymptotics.IsEuclid.sum_arg_lt`, `Asymptotics.IsEuclid.re_saddleDir_pos`,
   `Asymptotics.IsEuclid.re_lift_ne`, `Asymptotics.IsEuclid.re_saddle_le_of_lift`,
   `Asymptotics.IsEuclid.le_re_saddle_of_lift`, `Asymptotics.IsEuclid.re_saddleDir_sub_pos`,
   `Asymptotics.IsEuclid.exists_contour`
29. Lightlike/Asymptotics/OrientationTests.lean - `Asymptotics.saddleDir_sq_regular`,
   `Asymptotics.IsEuclid.saddleCoeff_mul_exp_sum_arg`, `Asymptotics.IsEuclid.saddleCoeff_mul_sq_ne`,
   `Asymptotics.IsEuclid.re_neg_saddleDir_neg`, `Asymptotics.exists_contour_regular`,
   `Asymptotics.saddleCoeff_zero`
30. Lightlike/Asymptotics/UniformValley.lean - `Asymptotics.valleyRadius`,
   `Asymptotics.valleyRadius_pos`, `Asymptotics.valley_bounds`,
   `Asymptotics.IsEuclid.saddle_sub_mem_slitPlane`, `Asymptotics.continuousOn_saddleCoeff`,
   `Asymptotics.continuousOn_saddleDir`, `Asymptotics.tendsto_saddleCoeff_lengthsDir`,
   `Asymptotics.tendsto_saddleDir_lengthsDir`, `Asymptotics.IsEuclid.eventually_valley_bounds`
31. Lightlike/Asymptotics/UniformValleyTests.lean - `Asymptotics.norm_saddleCoeff_regular`,
   `Asymptotics.valleyRadius_regular`, `Asymptotics.IsEuclid.vertical_not_valley`,
   `Asymptotics.valley_bounds_regular`, `Asymptotics.valleyRadius_zero`
32. Lightlike/Asymptotics/KernelLead.lean - `Asymptotics.stirRho`, `Asymptotics.leadP`,
   `Asymptotics.kernelErr`, `Asymptotics.stir_exponent_eq`,
   `Asymptotics.sin_pi_mul_sub_three_halves`, `Asymptotics.racahKernel_eq_lead`,
   `Asymptotics.norm_leadP`, `Asymptotics.norm_leadP_le`, `Asymptotics.leadP_smul`,
   `Asymptotics.hasDerivAt_leadP`, `Asymptotics.norm_leadP_sub_le`, `Asymptotics.norm_stirRho_le`,
   `Asymptotics.norm_stirMu_le_of_im`, `Asymptotics.norm_kernelErr_smul_le`,
   `Asymptotics.norm_exp_div_one_add_sub_one_le`, `Asymptotics.kernelLeadC`,
   `Asymptotics.norm_racahKernel_sub_lead_le`
33. Lightlike/Asymptotics/KernelLeadTests.lean - `Asymptotics.leadP_zero_I`,
   `Asymptotics.leadP_zero_two_I`, `Asymptotics.stirRho_one`, `Asymptotics.leadP_smul_wrong_power`,
   `Asymptotics.racahKernel_lead_zero`, `Asymptotics.leadP_zero_zero`,
   `Asymptotics.one_add_exp_half_eq_zero`
34. Lightlike/Asymptotics/SaddleRay.lean - `Asymptotics.norm_sub_le_of_path`,
   `Asymptotics.laplace_amp_uniform`, `Asymptotics.hasDerivAt_rescale`,
   `Asymptotics.ray_estimate`, `Asymptotics.leadP_mul_saddleDir`,
   `Asymptotics.IsEuclid.norm_saddleCoeff_mul_prod`, `Asymptotics.IsEuclid.im_lead_main`
35. Lightlike/Asymptotics/SaddleRayTests.lean - `Asymptotics.exp_neg_half_sum_log_four`,
   `Asymptotics.im_rescale_two_I`, `Asymptotics.im_lead_main_regular`,
   `Asymptotics.exp_neg_quarter_ne`, `Asymptotics.norm_sub_le_of_path_segment`,
   `Asymptotics.hasDerivAt_rescale_id`, `Asymptotics.not_ne_intCast_zero`
36. Lightlike/Asymptotics/SaddleAssembly.lean - `Asymptotics.kernelRegion`,
   `Asymptotics.scaledKernel`, `Asymptotics.exists_norm_scaledKernel_le`,
   `Asymptotics.IsEuclid.prefactorRate_smul`, `Asymptotics.IsEuclid.reggeAction_smul`,
   `Asymptotics.abs_lead_sub_le`, `Asymptotics.IsEuclid.outer_side`,
   `Asymptotics.racahSumAsymptotics`, `Asymptotics.ponzanoReggeFormula`
37. Lightlike/Asymptotics/SaddleAssemblyTests.lean -
   `Asymptotics.racahSumAsymptotics_regular`, `Asymptotics.not_ponzanoReggeFormulaWith_zero`,
   `Asymptotics.not_ponzanoReggeFormulaWith_neg_quarter`, `Asymptotics.ponzanoReggeFormula_regular`,
   `Asymptotics.kernelRegion_one_zero`, `Asymptotics.kernelRegion_zero_four`,
   `Asymptotics.not_kernelRegion_one_four`
38. Lightlike/Asymptotics/MorseLemma.lean - `Morse.morse_lemma_with_parameters`,
   `Morse.morse_coordinates`, `Morse.hadamard_integral`, `Morse.exists_smooth_selfadjoint_root`,
   `Morse.contDiff_integral_unit_infty`, `Morse.morse_diagonal`, `Morse.HasDiagonalMorseChart`,
   `Morse.not_hasDiagonalMorseChart_cube`
39. Lightlike/Asymptotics/Tauberian/Window.lean - `Tauberian.laplace`, `Tauberian.counting`,
    `Tauberian.counting_mul_exp_le`, `Tauberian.laplace_eq_split`
40. Lightlike/Asymptotics/Tauberian/Lower.lean - `Tauberian.counting_lower`
41. Lightlike/Asymptotics/Tauberian/Ingham.lean - `Tauberian.laplace_bounds`, `Tauberian.log_counting_le`,
    `Tauberian.lower_eventually`, `Tauberian.ingham_log`
42. Lightlike/Asymptotics/Tauberian/Scaling.lean - `Tauberian.SlowlyVarying`, `Tauberian.tendsto_scaled_laplace`
43. Lightlike/Asymptotics/Tauberian/PolyIntegral.lean - `Tauberian.integral_poly_eq_sum`, `Tauberian.tendsto_poly_integral`
44. Lightlike/Asymptotics/Tauberian/Functional.lean - `Tauberian.Phi`, `Tauberian.Lam`, `Tauberian.tendsto_lam`
45. Lightlike/Asymptotics/Tauberian/Ramp.lean - `Tauberian.rampUp`, `Tauberian.rampDown`, `Tauberian.mul_rampUp_eq_one`
46. Lightlike/Asymptotics/Tauberian/Karamata.lean - `Tauberian.counting_le_integral_rampUp`, `Tauberian.integral_rampDown_le_counting`, `Tauberian.karamata`

## References

1. G. Racah, Theory of complex spectra II, *Phys. Rev.* 62 (1942) 438.
2. G. Ponzano, T. Regge, Semiclassical limit of Racah coefficients, in *Spectroscopic and Group
   Theoretical Methods in Physics*, North-Holland, 1968.
3. B. Mukhametzhanov and A. Zhiboedov, Modular invariance, tauberian theorems and microcanonical entropy, JHEP 10 (2019) 261, arXiv:1904.06359, Section 1 (the paragraph before eq. (1.8)).
