import Lightlike.Asymptotics.Lorentzian.ExpPhase

/-!
# The asymptotic formula for an integral `w(λ) ∫ A e^{λ S}`

The Lorentzian vertex amplitude has the form `w(λ) ∫ A e^{λ S}` over a space of dimension `n`
(44 for the coherent EPRL vertex), with a polynomial weight `w(λ)` from the dimension factors,
a smooth action `S` with `Re S ≤ 0`, and a finitely many critical points. The integrand is
not compactly supported, so the amplitude is split as `A = a_loc + a_far`: `a_loc` has compact
support around the critical points, and the contribution of `a_far` is the hypothesis `hfar`,
of order `λ^{-n/2-1}`. Everything else is proved: the sum over the critical points, with the
Hessians entering as `-∂²S`, and the error.
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- **Asymptotics of `w(λ) ∫ (a_loc + a_far) e^{λ S}` under the hypothesis `hfar`.** With the
hypotheses of `expPhase_asymptotics` for `a_loc`, integrability of the remainder and
`∫ a_far e^{λS} = O(λ^{-n/2-1})`, and a weight `w(λ) = O(λ^m)`, the integral is
`w(λ) Σ_{x₀} e^{λ S(x₀)} (2π/λ)^{n/2} (det (-∂²S(x₀)))^{-1/2} a_loc(x₀)` up to
`O(λ^{m-n/2-1})`. -/
theorem weighted_asymptotics {S aLoc aFar : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0) (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport aLoc, ((S x).re = 0 ∧ fderiv ℝ S x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport aLoc) (hnd : ∀ x ∈ K, (-hessMat S x).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) :
    (fun lam : ℕ => w lam * (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
        w lam * ∑ x₀ ∈ K, cexp ((lam : ℝ) * S x₀) *
          ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) := by
  have hloc := expPhase_asymptotics hS ha hc hRe K hK hKs hnd
  have hloc' := hloc.comp_tendsto tendsto_natCast_atTop_atTop
  have hsplit : ∀ τ : ℝ, ∫ x, (aLoc x + aFar x) * cexp (τ * S x) =
      (∫ x, aLoc x * cexp (τ * S x)) + ∫ x, aFar x * cexp (τ * S x) := fun τ => by
    have h1 : Integrable fun x => aLoc x * cexp (τ * S x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hc.mul_right)
      exact ha.continuous.mul (Complex.continuous_exp.comp
        (continuous_const.mul hS.continuous))
    simp only [add_mul]
    exact integral_add h1 (hint τ)
  have hmain : (fun lam : ℕ => (∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x)) -
      ∑ x₀ ∈ K, cexp ((lam : ℝ) * S x₀) *
          ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)) := by
    have := hloc'.add hfar
    refine this.congr_left fun lam => ?_
    simp only [Function.comp, hsplit]
    ring
  have hprod := hw.mul hmain
  refine hprod.congr' (Eventually.of_forall fun lam => by simp only [mul_sub]) ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have : (0 : ℝ) < lam := by exact_mod_cast hlam
  rw [← Real.rpow_add this, sub_sub, add_sub_assoc']
  ring_nf

/-- **Two critical points with conjugate phases** (the shape of BDFHP eq. (57)). With
`K = {x₁, x₂}`, `S(x₁) = iθ`, `S(x₂) = -iθ` and the weight `w(λ) = c λ^m`, the integral
`w(λ) ∫ (aLoc + aFar) e^{λS}` equals `λ^{m-n/2} (A₁ e^{iλθ} + A₂ e^{-iλθ})` up to
`O(λ^{m-n/2-1})`, where `A_i = c (2π)^{n/2} (det(-∂²S(x_i)))^{-1/2} aLoc(x_i)` is the named
constant of the point `x_i`. Assumed here, not computed: that these `A_i` are the explicit
constants of the source (the leading coefficient `c` of the dimension factors, the Haar density in
`aLoc`, the sign); that `S(x₁) = -S(x₂)` is the phase `±iγ Σ k Θ`. -/
theorem weighted_two_points {S aLoc aFar : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
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
  have h := weighted_asymptotics hS ha hc hRe {x₁, x₂} hK
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

/-! ### Non-vacuity -/

/-- The hypotheses `hint` and `hfar` hold for the zero remainder, so the theorem contains the
compactly supported case of `expPhase_asymptotics`. -/
theorem hfar_zero (S : (Fin n → ℝ) → ℂ) :
    (∀ τ : ℝ, Integrable fun x : Fin n → ℝ => (0 : ℂ) * cexp (τ * S x)) ∧
    (fun lam : ℕ => ∫ x : Fin n → ℝ, (0 : ℂ) * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)) := by
  refine ⟨fun τ => by simp only [zero_mul]; exact integrable_zero _ _ _, ?_⟩
  simp only [zero_mul, integral_zero]
  exact isBigO_zero _ _

end Lightlike.Asymptotics.Lorentzian
