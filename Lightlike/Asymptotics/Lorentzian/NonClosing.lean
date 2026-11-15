import Lightlike.Asymptotics.Lorentzian.Suppression
import Lightlike.Asymptotics.Lorentzian.Stationary

/-!
# Suppression for boundary data whose normals do not close

BDFHP eq. (56): for boundary data with no critical point the vertex amplitude is `o(λ^{-K})` for
every `K`. In a chart, `weighted_suppressed` needs at each point of the support `Re S < 0` or
`dS ≠ 0`. This file derives that pointwise condition from the failure of closure of the normals
at a vertex (`stationary_iff_closure`): at a point with `Re S = 0` the first variation of the
action in the group directions at that vertex is `Σ_e logDeriv`, which does not vanish in every
direction when the normals do not close.

Named hypotheses, not proved here:
* `hchart`: at a point with `Re S = 0`, the derivative of the chart action along some tangent
  vector equals the sum of the log derivatives of the triangle factors under `X ↦ X exp(tL)`, for
  every `L` (the tangent space of the chart contains the group variations). No chart of
  `SL(2, ℂ)^4 × (ℂ P¹)^10` is constructed in the library.
* the passage from `Re S = 0` to spinors proportional to the boundary spinors, which is what makes
  the log derivative formula applicable (`triWeight_eq_one_iff`), needs the nonvanishing conditions
  of `re_triAction_le_zero`; it enters through `hchart` and `hRe`.
* `hnoclose`: at each point with `Re S = 0` the transported normals `ξ x e` do not close. For
  rotations alone they are the boundary normals.
* `hfar` for every order and the integrability `hint` are assumptions, not proved.

Excluded: the case of a single vector geometry (BDFHP eq. (55)), where the normals close and the
amplitude is not suppressed.
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- **Non-closing suppression in a chart.** Under `hchart` and `hnoclose` (see the module
docstring), every point of the support of `aLoc` has `Re S < 0` or `dS ≠ 0`, and the weighted
integral is `O(λ^{m-N})` for every `N`. -/
theorem lorVertex_suppressed {S aLoc aFar : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0)
    {ι : Type*} [Fintype ι] (nn : ι → ℕ) (γ : ℝ) (ξ : (Fin n → ℝ) → ι → Spinor)
    (hchart : ∀ x ∈ tsupport aLoc, (S x).re = 0 → ∀ c : Fin 3 → ℂ, ∃ v,
      fderiv ℝ S x v = ∑ e, logDeriv (nn e) (γ * ((nn e : ℝ) / 2)) c (ξ x e))
    (hnoclose : ∀ x ∈ tsupport aLoc, (S x).re = 0 →
      ¬ ∀ j, ∑ e, (nn e : ℝ) * spinVec (ξ x e) j = 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : ∀ N : ℕ, (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) (N : ℕ) :
    (fun lam : ℕ => w lam * ∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (N : ℝ))) := by
  refine weighted_suppressed hS ha hc hRe (fun x hx => ?_) hint hfar w m hw N
  by_cases h0 : (S x).re = 0
  · right
    intro hd
    have hnc := hnoclose x hx h0
    rw [← stationary_iff_closure] at hnc
    push Not at hnc
    obtain ⟨c, hc'⟩ := hnc
    obtain ⟨v, hv⟩ := hchart x hx h0 c
    rw [hd] at hv
    exact hc' (by simpa using hv.symm)
  · left
    exact lt_of_le_of_ne (hRe x hx) h0

/-- Control: two opposite triangles of equal spin violate `hnoclose`: their normals close. -/
theorem closing_violates_hnoclose (n : ℕ) :
    ∀ j, ∑ e : Fin 2, (((fun _ => n) e : ℕ) : ℝ) * spinVec (![e0, e1] e) j = 0 := by
  intro j
  fin_cases j <;> simp [Fin.sum_univ_two, spinVec_e0, spinVec_e1]

/-- Control: a single triangle of positive spin satisfies `hnoclose`: its normal does not close. -/
theorem single_satisfies_hnoclose (n : ℕ) (hn : 0 < n) :
    ¬ ∀ j, ∑ e : Fin 1, (((fun _ => n) e : ℕ) : ℝ) * spinVec ((fun _ => e0) e) j = 0 := by
  intro h
  have := h 2
  simp [spinVec_e0, hn.ne'] at this

end Lightlike.Asymptotics.Lorentzian
