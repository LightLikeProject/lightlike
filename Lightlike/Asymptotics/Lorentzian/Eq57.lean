import Lightlike.Asymptotics.Lorentzian.VertexFormula

/-!
# The constants of the two-point formula, as named hypotheses

The two-point formula `weighted_two_points` has constants `A_i = c (2π)^{n/2}
(det(-∂²S(x_i)))^{-1/2} aLoc(x_i)`. In the source (BDFHP, eq. (57)) the constant of a critical
point has the shape `(2π)^22 · 24 / √(det H) · Π_{ab} 2 k_ab c_ab Ω_ab`, with the overall sign
`(-1)^(χ+M)` of eq. (53). This file states the explicit shape `eq57Constant` and the corollary in
which the identification of the amplitude at the critical point with the factors of the source
is a named hypothesis (`hamp₁`, `hamp₂`).

Assumed, not proved, and stated here as hypotheses:
* the value `c · aLoc(x_i) = mult · Π_e f_e(x_i)` of the amplitude at each critical point
  (the factors `2 k c Ω`, the Haar density of the gauge-fixed integral, and the multiplicity of
  the spin lift);
* the reading of the source's `√(det H)`. In Section 6.4 of the source, directly after eq. (57),
  `H|crit` is "the Hessian matrix of the action (17) evaluated at the critical points", that is
  the second derivatives of `S` itself, and the formula contains `√(det H)` with no minus sign and
  no statement of the branch of the root. Here it is read as `(det (-∂²S))^{-1/2}` with the
  branch of `invSqrtDet`. The radicands `det H` and `det (-H)` agree for even `n`, in particular
  for `n = 44` (`det_neg_of_even`), but the branch of the root is still a hypothesis: for
  `H = -1` on `ℂ²` the two readings give `1` and `-1` (`invSqrtDet_neg_one_two`), and for odd `n`
  the radicands themselves differ (`det_gauss_hessian`);
* the closed form of the Hessian and the Haar measure on `SL(2, ℂ)` are not provided.
-/

open Complex Filter Asymptotics Lightlike.Oscillatory MeasureTheory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- The shape of the constant of eq. (57): `sgn · (2π)^{n/2} · mult · (det D)^{-1/2} · Π_e f e`,
with `D` the matrix `-∂²S` at the critical point, `mult` the multiplicity (24 in the source) and
`f e` the factors `2 k_e c_e Ω_e` of the ten triangles. The value of `n` is `44` for the vertex. -/
noncomputable def eq57Constant (n : ℕ) (sgn mult : ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin 10 → ℂ) : ℂ :=
  sgn * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * mult * invSqrtDet D * ∏ e, f e

/-- **The two-point formula with the constants of the source shape.** If the amplitude at each of
the two critical points, times the weight constant `c`, equals `sgn · mult · Π f_i` (hypotheses
`hamp₁`, `hamp₂`, the identification of the constants of eq. (57), assumed), the formula of
`weighted_two_points` holds with `A_i = eq57Constant n sgn mult (-hessMat S x_i) f_i`. -/
theorem weighted_two_points_eq57 {S aLoc aFar : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0) (x₁ x₂ : Fin n → ℝ) (hne : x₁ ≠ x₂)
    (hK : ∀ x ∈ tsupport aLoc, ((S x).re = 0 ∧ fderiv ℝ S x = 0) ↔ x ∈ ({x₁, x₂} : Finset _))
    (hKs₁ : x₁ ∈ tsupport aLoc) (hKs₂ : x₂ ∈ tsupport aLoc)
    (hdet₁ : (-hessMat S x₁).det ≠ 0) (hdet₂ : (-hessMat S x₂).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (θ : ℝ) (h₁ : S x₁ = I * θ) (h₂ : S x₂ = -(I * θ)) (c : ℂ) (m : ℝ)
    (sgn₁ sgn₂ mult : ℂ) (f₁ f₂ : Fin 10 → ℂ)
    (hamp₁ : c * aLoc x₁ = sgn₁ * mult * ∏ e, f₁ e)
    (hamp₂ : c * aLoc x₂ = sgn₂ * mult * ∏ e, f₂ e) :
    (fun lam : ℕ => (c * (((lam : ℝ) ^ m : ℝ) : ℂ)) *
        (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
      (((lam : ℝ) ^ (m - (n : ℝ) / 2) : ℝ) : ℂ) *
        (eq57Constant n sgn₁ mult (-hessMat S x₁) f₁ * cexp (I * (lam : ℝ) * θ) +
          eq57Constant n sgn₂ mult (-hessMat S x₂) f₂ * cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) := by
  have h := weighted_two_points hS ha hc hRe x₁ x₂ hne hK hKs₁ hKs₂ hdet₁ hdet₂ hint hfar
    θ h₁ h₂ c m
  have e1 : c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₁) * aLoc x₁ =
      eq57Constant n sgn₁ mult (-hessMat S x₁) f₁ := by
    unfold eq57Constant
    rw [show c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₁) * aLoc x₁ =
      (c * aLoc x₁) * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₁) by ring,
      hamp₁]
    ring
  have e2 : c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₂) * aLoc x₂ =
      eq57Constant n sgn₂ mult (-hessMat S x₂) f₂ := by
    unfold eq57Constant
    rw [show c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₂) * aLoc x₂ =
      (c * aLoc x₂) * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₂) by ring,
      hamp₂]
    ring
  rwa [e1, e2] at h

/-- Control: a wrong multiplicity changes the constant. With `mult = 0` the constant is `0`, so
the shape is not insensitive to the hypotheses (`eq57Constant` is linear in `mult`). -/
theorem eq57Constant_mult_zero (n : ℕ) (sgn : ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin 10 → ℂ) : eq57Constant n sgn 0 D f = 0 := by
  simp [eq57Constant]

/-- Control: the constant of the two critical points differ by their sign when `sgn₂ = -sgn₁`
and everything else agrees, so swapping the sign hypotheses swaps the roles, as for
`swap_constants_fails`. -/
theorem eq57Constant_neg_sgn (n : ℕ) (sgn mult : ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin 10 → ℂ) : eq57Constant n (-sgn) mult D f = -eq57Constant n sgn mult D f := by
  simp [eq57Constant]

end Lightlike.Asymptotics.Lorentzian
