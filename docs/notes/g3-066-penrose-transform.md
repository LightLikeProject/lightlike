# G3-066: the Penrose transform by contour integrals

Lean: `Lightlike/GR/PenroseTransform.lean` (namespace `Lightlike.Spinor`, on G3-067's `ZeroRestMass.lean`).

## Mathlib check

`Mathlib/Analysis/Calculus/ParametricCircleIntegral.lean` (`hasFDerivAt_circleIntegral_of_dominated_of_fderiv_le`) differentiates
circle integrals in a parameter; `circleIntegral.integral_fun_sum`, `integral_const_mul`, `integral_congr`; the symmetry of
iterated derivatives of analytic functions `ContDiffAt.iteratedFDeriv_comp_perm`; `Tuple.sort`,
`Tuple.comp_perm_comp_sort_eq_comp_sort`; `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right` and
`ContinuousLinearEquiv.iteratedFDeriv_comp_left` (no smoothness needed). Nothing on twistor integrals in Mathlib or Physlib.

## Sources read

T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196 (pdftotext and rendered pages):
* p. 6: `⟨κ ω⟩ := κ^α ω_α` (1.10), with (1.5)–(1.7).
* p. 25: helicity conventions (3.15): `h > 0`: `φ̃_{α̇₁⋯α̇_{2|h|}}`, `∂^{βα̇₁} φ̃_{α̇₁⋯} = 0`; `h = 0`: `□Φ = 0`; `h < 0`:
  `φ_{α₁⋯α_{2|h|}}`, `∂^{α₁β̇} φ_{α₁⋯} = 0`.
* pp. 27–28: (3.25)–(3.30): "`⟨λ dλ⟩` is the natural holomorphic measure on CP¹ of projective weight +2"; `f` of weight
  `−2s − 2` (3.27); the restriction `f(Z)|_X = f(x^{βα̇} λ_β, λ_α, …)` (3.28); the integral (3.29); the computation (3.30)
  "Clearly, the first term in the parentheses vanishes, since `λ^α λ_α = 0`. So if our twistor representative `f` is
  holomorphic …, our integral formula does indeed obey the z.r.m. equation".
* p. 30: (3.39) `{helicity h z.r.m. fields on M_C} ≅ H^{0,1}(PT, O(2h − 2))`; the integral formulae (3.40) `h < 0`,
  (3.41) `h = 0`, (3.42) `h > 0` (`∂/∂μ^{α̇₁} ⋯ ∂/∂μ^{α̇_{2h}} f|_X`); "You can readily check that the h ≥ 0 integral formulae
  obey the z.r.m. equations by using holomorphicity and the incidence relations".

M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464:
* p. 3: (1.1) `φ = ∮_{Γ⊂CP¹} f((z + ct) + (x + iy)λ, (x − iy) − (z − ct)λ, λ) dλ`, "the most elementary of Penrose's series of
  twistor integral formulae for massless fields"; (1.2) the wave equation by differentiating under the integral sign.
* §2.3, pp. 8–9: `f` holomorphic on `U₀ ∩ U₁`, homogeneous of degree −2, restricted to the plane of (2.7), "Integrate the
  cohomology class along a contour Γ in L_p. This gives (1.1) with λ = Z³/Z²"; "This correspondence extents to solutions of
  zero–rest–mass equations with higher spin, and elements of H¹(PT, O(k))".

M. Wolf, *A First Course on Twistors, Integrability and Gluon Scattering Amplitudes*, arXiv:1001.3871v2, §2.1 (pdftotext and the
rendered page 12):
* p. 11: (2.1) `φ(x) = −(1/2πi) ∮_C dλ_α̇ λ^α̇ f(x^{αβ̇} λ_β̇, λ_α̇)`, `C` a closed curve in `U₊ ∩ U₋ ⊂ CP¹`, `f` of homogeneity −2 "as
  only then is the integral well-defined"; (2.2) `□φ = 0` "by differentiating under the integral".
* p. 12: Exercise 2.1, `f = 1/(z¹z²)` gives `φ = 1/det x`; (2.3) `φ_{α̇₁⋯α̇_{2h}}(x) = −(1/2πi) ∮ dλ_α̇ λ^α̇ λ_{α̇₁}⋯λ_{α̇_{2h}} f(x^{αβ̇}λ_β̇, λ_α̇)`
  (positive helicity `h`, `f` of homogeneity `−2h − 2`) solves (2.4) `∂^{αα̇₁} φ_{α̇₁⋯α̇_{2h}} = 0`; (2.5)
  `φ_{α₁⋯α_{2h}}(x) = −(1/2πi) ∮ dλ_α̇ λ^α̇ ∂/∂z^{α₁} ⋯ ∂/∂z^{α_{2h}} f` (negative helicity `−h`, `f` of homogeneity `2h − 2`), (2.6).

## How each Lean statement matches

* `incid`, `twistorPt`: Adamo's restriction (3.28), `μ^{α̇} = x^{βα̇} λ_β`; `angle`: `⟨κ ν⟩ = κ^α ν_α` (1.10).
* `penroseNeg`, `penroseScalar`, `penrosePos`: `∮_{C(c,R)} ⟨λ(z) λ'(z)⟩ (…) dz` along a section `λ(z)` of the line of `x`, with the
  integrands of (3.40), (3.41), (3.42). `∂^{n+1}f/∂μ^{α̇₁}⋯` is `dmuIter` (iterated derivative, indices in increasing order).
* `hasFDerivAt_circleIntegral_twistorPt`, `pd_circleIntegral_twistorPt`: differentiation under the integral sign (ADM p. 3)
  for `f` `C¹` on an open `W` containing the twistor points of the contour over the open `U` (domination by compactness of
  `closedBall × sphere`).
* `penroseNeg_isZrmNeg`, `penroseScalar_isZrmScalar`, `penrosePos_isZrmPos`: the transforms are z.r.m. fields of helicity
  `−(n + 1)/2`, `0`, `(n + 1)/2` on `U` (3.30), (3.40)–(3.42); for `h = 0` this is ADM (1.2).
* `penroseScalar_elementary`, `penroseScalar_elementary_isZrmScalar`: Wolf's Exercise 2.1 with `f = 1/(μ⁰μ¹)` and `λ(z) = (1, z)` on
  `|z| = R` separating the poles (`|x⁰⁰| < R |x¹⁰|`, `R |x¹¹| < |x⁰¹|`): the transform is `2πi / det x` (partial fractions,
  `circleIntegral.integral_sub_inv_of_mem_ball`, Cauchy's theorem `DiffContOnCl.circleIntegral_eq_zero`), a constant multiple of
  Wolf's `1/det x` (normalisation and the sign of `⟨λ dλ⟩` differ), and it solves the wave equation.
* `penroseNeg_integrand_rescale`, `penroseScalar_integrand_rescale`, `penrosePos_integrand_rescale`: the homogeneity count:
  replacing the section `λ` by `s λ` multiplies the integrand by `s^{2 + (n+1) + d}`, `s^{2 + d}`, `s^{2 + d − (n+1)}` for `f`
  homogeneous of degree `d` (`⟨λ dλ⟩` weight 2, `λ_{α₁}⋯` weight `n + 1`, `∂_μ^{n+1}` weight `−(n + 1)`, via
  `iteratedFDeriv_smul_of_homogeneous`). `penroseNeg_rescale`, `penroseScalar_rescale`, `penrosePos_rescale`: for
  `d = 2h − 2` (`−(n+1) − 2`, `−2`, `n − 1`) the exponent is 0 and the transform does not depend on the section.

## Differences

1. Representation: the row's `(ω, π_{A'})` with `ω = i x π` are Adamo's `(μ^{α̇}, λ_α)` with `μ = x λ` (3.28) (no `i`; G3-062
   relates the two incidence relations); helicity signs as Adamo (3.15): `h < 0` has undotted indices and the factors `λ`.
2. Representation: the contour is a circle `C(c, R)` in a parameter `z` with a section `λ(z)` of the line `X ≅ CP¹`
   (ADM: λ = Z³/Z², `λ(z) = (1, z)` is one choice); twistor functions are functions of `(μ, λ) ∈ ℂ² × ℂ²`, homogeneous where
   the homogeneity count is stated; "holomorphic on the relevant region" is `C¹` (`h ≤ 0`) or analytic (`h > 0`) on an open
   set containing the twistor points of the contour.
3. Convention (against Wolf): Wolf's twistor `(z^α, λ_α̇)`, `z^α = x^{αβ̇} λ_β̇`, has the chirality opposite to Adamo's
   `(μ^{α̇}, λ_α)`; exchanging dotted and undotted indices, Wolf's (2.3) is `penroseNeg` and (2.5) is `penrosePos`, and Wolf's
   helicity `h` is `−h` here (Adamo (3.15)); the homogeneities agree (`−2h − 2 = 2(−h) − 2`). Wolf's normalisation `−1/(2πi)` is
   omitted. (The `h = 0` contour form is also ADM (1.1) p. 3; for `h ≠ 0` Adamo prints the Dolbeault form (3.40), (3.42).)
4. Not claimed: the Dolbeault isomorphism (3.39) and the converse (every z.r.m. field arises); the gap row asks for the
   contour-integral formula.
