import Lightlike.Asymptotics.Lorentzian.InnerIntegrable
import Lightlike.Asymptotics.Lorentzian.Eq57

/-!
# The asymptotic formula of the Lorentzian vertex with two critical points, as a reduction

`lorVertex_asymptotic_formula` (BDFHP, arXiv:0907.2440, Sec. 6.4 p. 30, eqs. (53), (57)) passes from
the named hypotheses listed in its docstring (a chart representation of the amplitude, two
nondegenerate critical points, the far-field decay and the identification of the constants) to the
two-term formula, by `weighted_two_points_eq57` and the scaling `S(λ j, λ p) = λ S(j, p)`
(`lorAction_smul`). **It is a reduction, not a result about the vertex:** every hypothesis is an
assumption (the classification of the critical set, the Hessians and the chart are not proved
here). The hypotheses of the engine are consistent: `toy_two_points` in `ExpPhaseTwoPoints.lean`
satisfies all of them for a model phase with two nondegenerate critical points.
-/

open MeasureTheory Filter Asymptotics Complex Lightlike.Oscillatory Lightlike.Asymptotics.EPRL
open scoped Real ContDiff Topology Matrix
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian


/-- `triAction` is linear in the pair of parameters `(k, p)`. -/
theorem triAction_smul (c : ℝ) (k p : ℝ) (Z ξ Z' ξ' : Spinor) :
    triAction (c * k) (c * p) Z ξ Z' ξ' = (c : ℂ) * triAction k p Z ξ Z' ξ' := by
  unfold triAction
  push_cast
  ring

/-- Scaling all spins and labels by `lam` scales the action: `S(λ j, λ p) = λ S(j, p)`. -/
theorem lorAction_smul (c : ℝ) (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C)
    (z : Fin 10 → Spinor) :
    lorAction (fun e => c * j e) (fun e => c * p e) g X z = (c : ℂ) * lorAction j p g X z := by
  unfold lorAction
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => triAction_smul c _ _ _ _ _ _

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
theorem lorVertex_asymptotic_formula {n : ℕ} {j p : Fin 10 → ℝ} {g : BdryData} {cc : Fin 10 → ℂ}
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)}
    (hS : ContDiff ℝ ∞ (lorChartAction j p g chart)) {aLoc aFar : (Fin n → ℝ) → ℂ}
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
  have h := weighted_two_points_eq57 hS ha hc hRe x₁ x₂ hne hK hKs₁ hKs₂ hdet₁ hdet₂ hint hfar
    θ h₁ h₂ c m sgn₁ sgn₂ mult f₁ f₂ hamp₁ hamp₂
  refine h.congr_left (fun lam => ?_)
  rw [hpull lam]
  rfl

end Lightlike.Asymptotics.Lorentzian
