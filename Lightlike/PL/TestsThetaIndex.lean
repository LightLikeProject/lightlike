import Lightlike.PL.IndexCurve

/-!
# Checks of the θ configuration and the index about a Jordan curve

Non-vacuity: the unit circle, as the injective continuous map `Circle → ℂ`, admits a θ configuration above it
satisfying the hypotheses of the ray argument, so `Theta.Setting` is satisfiable. Wrong-model check: three collinear
points have vanishing cross product, so the nondegeneracy hypothesis of `loopIndex_omega1` excludes them.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

/-- Non-vacuity: the unit circle has a θ configuration above it. -/
example : ∃ T : Theta, Theta.Setting T ∧ range T.γ₁ ∪ range T.γ₂ = range (fun w : Circle => (w : ℂ)) ∧
    ∃ a b : ℝ, a < b ∧ b < a + 2 * π ∧
      (∀ t : I, T.γ₁ t = ((Circle.exp (a + (t : ℝ) * (b - a)) : Circle) : ℂ)) ∧
      (∀ t : I, T.γ₂ t = ((Circle.exp (b + (t : ℝ) * (a + 2 * π - b)) : Circle) : ℂ)) :=
  exists_theta_top (f := fun w : Circle => (w : ℂ)) continuous_subtype_val Subtype.val_injective

/-- Non-vacuity: a θ configuration exists at any point off the circle, for instance the origin. -/
example : ∃ T : Theta, T.Ω = 0 :=
  have h0 : (0 : ℂ) ∉ range (fun w : Circle => (w : ℂ)) := by
    rintro ⟨w, hw⟩
    have := Circle.norm_coe w
    simp only [hw, norm_zero] at this
    exact zero_ne_one this
  let ⟨T, h, _⟩ := exists_theta_at (f := fun w : Circle => (w : ℂ)) continuous_subtype_val
    Subtype.val_injective h0
  ⟨T, h⟩

/-- Wrong model: for collinear `Ω = 0`, `P = 1`, `Q = 2` the cross product is zero, so the hypothesis `hA` of
`loopIndex_omega1` fails. -/
example : (((2 : ℂ) - 0) * (starRingEnd ℂ) ((1 : ℂ) - 0)).im = 0 := by simp

end Lightlike.PL
