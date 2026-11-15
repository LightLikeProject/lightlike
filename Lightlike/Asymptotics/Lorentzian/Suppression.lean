import Lightlike.Asymptotics.Lorentzian.VertexFormula
import Lightlike.Oscillatory.Localisation

/-!
# Suppression without critical points

If no point of the support of the compactly supported amplitude is critical for the action
(`Re S < 0` or `dS ≠ 0` at each point), then `∫ a e^{τ S}` decays faster than any power of `τ`.
With the remainder hypothesis for every order, the whole integral `w(λ) ∫ (aLoc + aFar) e^{λS}`
is `O(λ^{-N})` for every `N` (BDFHP eq. (56), in a chart).
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- **Suppression for `e^{τ S}`.** If `Re S ≤ 0` on the support of the smooth compactly supported
`a`, and at each point of the support `Re S < 0` or `dS ≠ 0`, then `∫ a e^{τ S}` is `O(τ^{-k})`
for every `k`. -/
theorem expPhase_suppressed {S a : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hRe : ∀ x ∈ tsupport a, (S x).re ≤ 0)
    (hnc : ∀ x ∈ tsupport a, (S x).re < 0 ∨ fderiv ℝ S x ≠ 0) (k : ℕ) :
    ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, a x * cexp (τ * S x)‖ ≤ C * (τ ^ k)⁻¹ := by
  have hφ : ContDiff ℝ ∞ (fun x => -I * S x) := contDiff_const.mul hS
  have hder : ∀ x, fderiv ℝ (fun y => -I * S y) x = -I • fderiv ℝ S x := fun x => by
    rw [fderiv_const_mul (hS.differentiable (by simp) x)]
  have hI : ∀ τ : ℝ, ∀ x, cexp (I * τ * (-I * S x)) = cexp (τ * S x) := fun τ x => by
    congr 1
    have h : I * (τ : ℂ) * (-I * S x) = -(I * I) * (τ * S x) := by ring
    rw [h, I_mul_I]; ring
  have him : ∀ x, (-I * S x).im = -(S x).re := fun x => by simp
  obtain ⟨C, hC⟩ := exists_bound_noncritical hφ ha hc
    (fun x hx => by rw [him]; linarith [hRe x hx])
    (fun x hx => by
      rcases hnc x hx with h | h
      · left; rw [him]; linarith
      · right; rw [hder]
        intro h0
        exact h ((smul_eq_zero.mp h0).resolve_left (neg_ne_zero.mpr I_ne_zero))) k
  exact ⟨C, fun τ hτ => by simpa only [hI] using hC τ hτ⟩

/-- **The weighted suppression in a chart.** With `∫ aFar e^{λS} = O(λ^{-N})` for every `N`, the
integral `w(λ) ∫ (aLoc + aFar) e^{λ S}` is `O(λ^{m-N})` for every `N`, when there are no critical
points on the support of `aLoc`. -/
theorem weighted_suppressed {S aLoc aFar : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0)
    (hnc : ∀ x ∈ tsupport aLoc, (S x).re < 0 ∨ fderiv ℝ S x ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : ∀ N : ℕ, (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) (N : ℕ) :
    (fun lam : ℕ => w lam * ∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (N : ℝ))) := by
  obtain ⟨C, hC⟩ := expPhase_suppressed hS ha hc hRe hnc N
  have hloc : (fun lam : ℕ => ∫ x, aLoc x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with lam hlam
    have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
    have := hC lam h1
    have hpos : (0 : ℝ) < lam := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    simpa [div_eq_mul_inv, mul_comm] using this
  have hsplit : ∀ τ : ℝ, ∫ x, (aLoc x + aFar x) * cexp (τ * S x) =
      (∫ x, aLoc x * cexp (τ * S x)) + ∫ x, aFar x * cexp (τ * S x) := fun τ => by
    have h1 : Integrable fun x => aLoc x * cexp (τ * S x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hc.mul_right)
      exact ha.continuous.mul (Complex.continuous_exp.comp
        (continuous_const.mul hS.continuous))
    simp only [add_mul]
    exact integral_add h1 (hint τ)
  have hsum := (hloc.add (hfar N)).congr_left fun lam => (hsplit lam).symm
  have hprod := hw.mul hsum
  refine hprod.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have : (0 : ℝ) < lam := by exact_mod_cast hlam
  rw [← Real.rpow_add this]
  ring_nf

end Lightlike.Asymptotics.Lorentzian
