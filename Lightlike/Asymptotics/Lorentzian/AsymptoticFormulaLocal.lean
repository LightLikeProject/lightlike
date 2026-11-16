import Lightlike.Asymptotics.Lorentzian.AsymptoticFormula
import Lightlike.Asymptotics.Lorentzian.VertexLocal

/-!
# The two-point asymptotic formula for an action smooth only on an open set

`weighted_two_points`, `weighted_two_points_eq57` and `lorVertex_asymptotic_formula` with the global
hypothesis `ContDiff ℝ ∞ S` replaced by `ContDiffOn ℝ ∞ S U` on an open `U` containing the support of
`a_loc` (`weighted_asymptotics_local`), the Lorentzian action having logarithms. The statements and
the named hypotheses are those of the global versions.

## Main results

* `weighted_two_points_local`, `weighted_two_points_eq57_local`: the two-point formula and the
  constants of BDFHP eq. (57) for such an action.
* `lorVertex_asymptotic_formula_local`: the formula for the vertex in a chart.
-/

open Complex Filter MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL
open _root_.Asymptotics
open scoped Real ContDiff Topology Matrix
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- **Two critical points with conjugate phases** (the shape of BDFHP eq. (57)). With
`K = {x₁, x₂}`, `S(x₁) = iθ`, `S(x₂) = -iθ` and the weight `w(λ) = c λ^m`, the integral
`w(λ) ∫ (aLoc + aFar) e^{λS}` equals `λ^{m-n/2} (A₁ e^{iλθ} + A₂ e^{-iλθ})` up to
`O(λ^{m-n/2-1})`, where `A_i = c (2π)^{n/2} (det(-∂²S(x_i)))^{-1/2} aLoc(x_i)` is the named
constant of the point `x_i`. Assumed here, not computed: that these `A_i` are the explicit
constants of the source (the leading coefficient `c` of the dimension factors, the Haar density in
`aLoc`, the sign); that `S(x₁) = -S(x₂)` is the phase `±iγ Σ k Θ`. -/
theorem weighted_two_points_local {S aLoc aFar : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hS : ContDiffOn ℝ ∞ S U)
    (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0) (x₁ x₂ : Fin n → ℝ) (hne : x₁ ≠ x₂)
    (hK : ∀ x ∈ tsupport aLoc, ((S x).re = 0 ∧ fderiv ℝ S x = 0) ↔ x ∈ ({x₁, x₂} : Finset _))
    (hKs₁ : x₁ ∈ tsupport aLoc) (hKs₂ : x₂ ∈ tsupport aLoc)
    (hdet₁ : (-hessMat S x₁).det ≠ 0) (hdet₂ : (-hessMat S x₂).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (θ : ℝ) (h₁ : S x₁ = I * θ) (h₂ : S x₂ = -(I * θ)) (c : ℂ) (m : ℝ) :
    (fun lam : ℕ => (c * (((lam : ℝ) ^ m : ℝ) : ℂ)) *
        (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
      (((lam : ℝ) ^ (m - (n : ℝ) / 2) : ℝ) : ℂ) *
        ((c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₁) * aLoc x₁) *
            cexp (I * (lam : ℝ) * θ) +
          (c * (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-hessMat S x₂) * aLoc x₂) *
            cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) := by
  have hw : (fun lam : ℕ => c * (((lam : ℝ) ^ m : ℝ) : ℂ)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ m) := by
    refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun lam => ?_)
    rw [norm_mul, Complex.norm_real]
  have h := weighted_asymptotics_local hU hS hsU ha hc hRe {x₁, x₂} hK
    (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hKs₁
        · rw [Finset.mem_singleton.mp hx]; exact hKs₂)
    (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hdet₁
        · rw [Finset.mem_singleton.mp hx]; exact hdet₂)
    hint hfar _ m hw
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have hl : (0 : ℝ) < lam := by exact_mod_cast hlam
  rw [Finset.sum_pair hne, h₁, h₂]
  have hp : ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * ((lam : ℝ) ^ (-((n : ℝ) / 2)) : ℝ) := by
    rw [Real.div_rpow (by positivity) hl.le, Real.rpow_neg hl.le, div_eq_mul_inv]
  have hm : ((lam : ℝ) ^ (m - (n : ℝ) / 2) : ℝ) =
      ((lam : ℝ) ^ m : ℝ) * ((lam : ℝ) ^ (-((n : ℝ) / 2)) : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hl]
  rw [hp, hm]
  push_cast
  ring_nf

/-- **The two-point formula with the constants of the source shape.** If the amplitude at each of
the two critical points, times the weight constant `c`, equals `sgn · mult · Π f_i` (hypotheses
`hamp₁`, `hamp₂`, the identification of the constants of eq. (57), assumed), the formula of
`weighted_two_points` holds with `A_i = eq57Constant n sgn mult (-hessMat S x_i) f_i`. -/
theorem weighted_two_points_eq57_local {S aLoc aFar : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hS : ContDiffOn ℝ ∞ S U)
    (hsU : tsupport aLoc ⊆ U)
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
  have h := weighted_two_points_local hU hS hsU ha hc hRe x₁ x₂ hne hK hKs₁ hKs₂ hdet₁ hdet₂ hint hfar
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

/-- **The asymptotic formula of the Lorentzian vertex with two parity-related critical points**
(BDFHP, arXiv:0907.2440, Sec. 6.4 p. 30, eqs. (53), (57)), at the level of one chart of dimension `n`
(`n = 44` for the vertex): the amplitude of the scaled data `(λ j, λ p)` minus
`λ^{m - n/2} (A₁ e^{iλθ} + A₂ e^{-iλθ})` is `O(λ^{m - n/2 - 1})`, with `A_i = eq57Constant n sgn_i
mult (-H_i) f_i` and `H_i` the Hessian of the action at the critical point `x_i`.

**Assumptions, not results** (named hypotheses; none is proved here):
* `hpull`: the vertex amplitude of the scaled data equals the chart integral of a smooth amplitude
  `aLoc + aFar` times `e^{λ S}` (the chart `chart` and the pull-back of the Haar measure and of the
  densities of `Ω`: step 5 of the plan);
* `hK`, `hne`, `hKs₁`, `hKs₂`: the critical points with `Re S = 0` in the support of `aLoc` are
  exactly `x₁ ≠ x₂` (the classification of the critical set: step 4; BDFHP Sec. 5.4.3);
* `hdet₁`, `hdet₂`: the Hessians of `-S` at the two points are invertible (BDFHP take this as the
  nondegeneracy assumption; step 6);
* `hint`, `hfar`: the remainder away from the critical points is `O(λ^{-n/2-1})`;
* `h₁`, `h₂`: the values of the action at the critical points are `±iθ` (`θ = γ Σ k Θ`, BDFHP
  Sec. 6.2 p. 25);
* `hamp₁`, `hamp₂`: the amplitude at each critical point, times the weight constant `c`, is
  `sgn · mult · Π f` (the identification of the constants of eq. (57)).
What is proved is the passage from these hypotheses to the formula (`weighted_two_points_eq57`), with
the scaling `S(λ j, λ p) = λ S(j, p)` (`lorAction_smul`) and the finiteness of the vertex
(`integrable_lorOuter`, `integrable_lorInner`) available separately. -/
theorem lorVertex_asymptotic_formula_local {n : ℕ} {j p : Fin 10 → ℝ} {g : BdryData} {cc : Fin 10 → ℂ}
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ (lorChartAction j p g chart) U) {aLoc aFar : (Fin n → ℝ) → ℂ}
    (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (lorChartAction j p g chart x).re ≤ 0)
    (x₁ x₂ : Fin n → ℝ) (hne : x₁ ≠ x₂)
    (hK : ∀ x ∈ tsupport aLoc,
      ((lorChartAction j p g chart x).re = 0 ∧ fderiv ℝ (lorChartAction j p g chart) x = 0) ↔
        x ∈ ({x₁, x₂} : Finset (Fin n → ℝ)))
    (hKs₁ : x₁ ∈ tsupport aLoc) (hKs₂ : x₂ ∈ tsupport aLoc)
    (hdet₁ : (-lorHessian j p g chart x₁).det ≠ 0) (hdet₂ : (-lorHessian j p g chart x₂).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * lorChartAction j p g chart x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * lorChartAction j p g chart x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (θ : ℝ) (h₁ : lorChartAction j p g chart x₁ = I * θ)
    (h₂ : lorChartAction j p g chart x₂ = -(I * θ)) (c : ℂ) (m : ℝ)
    (sgn₁ sgn₂ mult : ℂ) (f₁ f₂ : Fin 10 → ℂ)
    (hamp₁ : c * aLoc x₁ = sgn₁ * mult * ∏ e, f₁ e)
    (hamp₂ : c * aLoc x₂ = sgn₂ * mult * ∏ e, f₂ e)
    (hpull : ∀ lam : ℕ, lorVertex (fun e => (lam : ℝ) * j e) (fun e => (lam : ℝ) * p e) cc g =
      c * (((lam : ℝ) ^ m : ℝ) : ℂ) *
        ∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * lorChartAction j p g chart x)) :
    (fun lam : ℕ => lorVertex (fun e => (lam : ℝ) * j e) (fun e => (lam : ℝ) * p e) cc g -
      (((lam : ℝ) ^ (m - (n : ℝ) / 2) : ℝ) : ℂ) *
        (eq57Constant n sgn₁ mult (-lorHessian j p g chart x₁) f₁ * cexp (I * (lam : ℝ) * θ) +
          eq57Constant n sgn₂ mult (-lorHessian j p g chart x₂) f₂ * cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) := by
  have h := weighted_two_points_eq57_local hU hS hsU ha hc hRe x₁ x₂ hne hK hKs₁ hKs₂ hdet₁ hdet₂ hint hfar
    θ h₁ h₂ c m sgn₁ sgn₂ mult f₁ f₂ hamp₁ hamp₂
  refine h.congr_left (fun lam => ?_)
  rw [hpull lam]
  rfl

end Lightlike.Asymptotics.Lorentzian
