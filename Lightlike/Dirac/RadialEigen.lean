import Mathlib
import Lightlike.Dirac.ConformalDirac

/-!
# Radial eigenspinors of the round sphere in the stereographic chart

For spinors of the form `f(y) = α(h) v + β(h) y·v` (`h = (1+‖y‖²)/2`, `v` a constant spinor) the Dirac
operator of the unit `n`-sphere acts by a first-order ODE system in `h`
(`diracF_stereo_radial`): `D f = λ f` as soon as
`h α' − ((n−1)/2) α = λ β` and `−h(2h−1) β' − (h + (n−1)/2) β = λ α`.

For `n = 2` and `α = h^{-1/2} P(1/h)`, `β = h^{-1/2} Q(1/h)` with real polynomials `P, Q`, the system becomes
`−(X P)' = λ Q`, `(2 − X) Q' − Q = λ P` (`diracF_stereo_poly_eigen`).  Taking leading coefficients gives
`λ² = (deg P + 1)²`, the Dirac spectrum `±(k+1)` of `S²`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Radial ODE reduction.** If `α, β` satisfy the two scalar ODE identities at `h = stereoH x`, the
spinor `α(h) v + β(h) y·v` is an eigenspinor of the Dirac operator of `Sⁿ` at `x`. -/
theorem diracF_stereo_radial (ρ : CliffordRep n V) (v : V) {α β : ℝ → ℝ} {α' β' lam : ℝ} (x : E n)
    (hα : HasDerivAt α α' (stereoH x)) (hβ : HasDerivAt β β' (stereoH x))
    (h1 : stereoH x * α' - ((n : ℝ) - 1) / 2 * α (stereoH x) = lam * β (stereoH x))
    (h2 : -(stereoH x * (2 * stereoH x - 1)) * β' - (stereoH x + ((n : ℝ) - 1) / 2) * β (stereoH x) =
      lam * α (stereoH x)) :
    diracF ρ stereoF stereoOmega (fun y => α (stereoH y) • v + β (stereoH y) • Yop ρ y v) x =
      lam • (α (stereoH x) • v + β (stereoH x) • Yop ρ x v) := by
  have hs : ‖x‖ ^ 2 = 2 * stereoH x - 1 := by unfold stereoH; ring
  have hY : Yop ρ x (Yop ρ x v) = (-‖x‖ ^ 2) • v := Yop_sq ρ x v
  rw [diracF_stereo, dirac_radial_h ρ v x hα hβ]
  simp only [map_add, map_smul, hY]
  rw [hs]
  match_scalars
  · linear_combination h1
  · linear_combination h2

open Polynomial in
/-- The scalar profile `u ↦ u^{-1/2} P(1/u)` has derivative `-(1/2) u^{-3/2} P(1/u) - u^{-1/2} u^{-2} P'(1/u)`. -/
lemma hasDerivAt_profile (P : ℝ[X]) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * P.eval t⁻¹)
      ((-(1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ) - 1)) * P.eval u⁻¹ +
        u ^ (-(1 / 2 : ℝ)) * (P.derivative.eval u⁻¹ * (-(u ^ 2)⁻¹))) u := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ) - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu)
  have h2 : HasDerivAt (fun t : ℝ => P.eval t⁻¹) (P.derivative.eval u⁻¹ * (-(u ^ 2)⁻¹)) u :=
    (P.hasDerivAt u⁻¹).comp u (hasDerivAt_inv hu)
  exact h1.mul h2

open Polynomial in
/-- **Polynomial radial eigenspinors of `S²`.** Let `P, Q` be real polynomials with
`−(X P)' = λ Q` and `(2 − X) Q' − Q = λ P`.  Then `f = h^{-1/2}(P(1/h) v + Q(1/h) y·v)` satisfies
`D f = λ f` for the Dirac operator of the unit 2-sphere in the stereographic chart. -/
theorem diracF_stereo_poly_eigen (ρ : CliffordRep 2 V) (v : V) (P Q : ℝ[X]) (lam : ℝ)
    (hP : -(X * P).derivative = C lam * Q) (hQ : (C 2 - X) * Q.derivative - Q = C lam * P) (x : E 2) :
    diracF ρ stereoF stereoOmega
        (fun y => (stereoH y ^ (-(1 / 2 : ℝ)) * P.eval (stereoH y)⁻¹) • v +
          (stereoH y ^ (-(1 / 2 : ℝ)) * Q.eval (stereoH y)⁻¹) • Yop ρ y v) x =
      lam • ((stereoH x ^ (-(1 / 2 : ℝ)) * P.eval (stereoH x)⁻¹) • v +
        (stereoH x ^ (-(1 / 2 : ℝ)) * Q.eval (stereoH x)⁻¹) • Yop ρ x v) := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  have e1 : stereoH x ^ (-(1 / 2 : ℝ) - 1) = stereoH x ^ (-(1 / 2 : ℝ)) / stereoH x :=
    Real.rpow_sub_one hne _
  have c1 := congrArg (Polynomial.eval (stereoH x)⁻¹) hP
  have c2 := congrArg (Polynomial.eval (stereoH x)⁻¹) hQ
  simp only [derivative_mul, derivative_X, eval_neg, eval_add, eval_mul, eval_X, eval_C,
    eval_sub, one_mul] at c1 c2
  refine diracF_stereo_radial ρ v x (hasDerivAt_profile P hne) (hasDerivAt_profile Q hne) ?_ ?_
  all_goals
    simp only [e1, Nat.cast_ofNat]
    generalize stereoH x ^ (-(1 / 2 : ℝ)) = q
    generalize Polynomial.eval (stereoH x)⁻¹ P = p at c1 c2 ⊢
    generalize Polynomial.eval (stereoH x)⁻¹ Q = r at c1 c2 ⊢
    generalize Polynomial.eval (stereoH x)⁻¹ (derivative P) = p' at c1 c2 ⊢
    generalize Polynomial.eval (stereoH x)⁻¹ (derivative Q) = r' at c1 c2 ⊢
    generalize stereoH x = h at hne c1 c2 ⊢
    field_simp at c1 c2 ⊢
    first
      | linear_combination 2 * q * c1
      | linear_combination 2 * q * c2

open Polynomial in
/-- **Dirac eigenspinors of `S²` with eigenvalue `3ε`** (`ε = ±1`), the case `k = 2` of the spectrum `±(k+1)`:
`P = 6 − 12 X + 5 X²`, `Q = −ε (2 − 8 X + 5 X²)`. -/
theorem diracF_stereo_eigen_three (ρ : CliffordRep 2 V) (v : V) {ε : ℝ} (hε : ε * ε = 1) (x : E 2) :
    diracF ρ stereoF stereoOmega
        (fun y => (stereoH y ^ (-(1 / 2 : ℝ)) * (C 6 - C 12 * X + C 5 * X ^ 2 : ℝ[X]).eval (stereoH y)⁻¹) • v +
          (stereoH y ^ (-(1 / 2 : ℝ)) *
            (-(C ε * (C 2 - C 8 * X + C 5 * X ^ 2)) : ℝ[X]).eval (stereoH y)⁻¹) • Yop ρ y v) x =
      (3 * ε) • ((stereoH x ^ (-(1 / 2 : ℝ)) * (C 6 - C 12 * X + C 5 * X ^ 2 : ℝ[X]).eval (stereoH x)⁻¹) • v +
        (stereoH x ^ (-(1 / 2 : ℝ)) *
          (-(C ε * (C 2 - C 8 * X + C 5 * X ^ 2)) : ℝ[X]).eval (stereoH x)⁻¹) • Yop ρ x v) := by
  have hε' : (C ε * C ε : ℝ[X]) = 1 := by rw [← C_mul, hε, C_1]
  refine diracF_stereo_poly_eigen ρ v _ _ (3 * ε) ?_ ?_ x
  · simp only [derivative_mul, map_add, map_sub, derivative_X, derivative_X_pow, C_mul, C_ofNat,
      derivative_ofNat, Nat.cast_ofNat, Nat.reduceSub]
    linear_combination (3 * (2 - 8 * X + 5 * X ^ 2 : ℝ[X])) * hε'
  · simp only [derivative_mul, map_add, map_sub, derivative_X, derivative_X_pow, C_mul, C_ofNat,
      derivative_ofNat, Nat.cast_ofNat, Nat.reduceSub, derivative_neg, derivative_C]
    ring

end Lightlike.Dirac
