import Lightlike.PL.JordanCurve

/-!
# Checks of the Jordan curve theorem

Non-vacuity: the unit circle in the plane, `w ↦ (re w, im w)`, is a continuous injective map from the circle, so the
theorem applies and gives a bounded and an unbounded component. Wrong-model check: a constant map from the circle is not injective, so the hypothesis of the theorem excludes it (its
complement is the plane minus a point, which has one component).
-/

open Set

namespace Lightlike.PL

/-- Non-vacuity: the unit circle in `ℝ × ℝ`. -/
example : ∃ U V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
    U ∪ V = (range (fun w : Circle => (((w : ℂ)).re, ((w : ℂ)).im))) ᶜ ∧ Bornology.IsBounded U ∧
    ¬ Bornology.IsBounded V ∧ frontier U = range (fun w : Circle => (((w : ℂ)).re, ((w : ℂ)).im)) ∧
    frontier V = range (fun w : Circle => (((w : ℂ)).re, ((w : ℂ)).im)) := by
  refine jordan_curve_theorem (f := fun w : Circle => (((w : ℂ)).re, ((w : ℂ)).im)) ?_ ?_
  · fun_prop
  · intro w w' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Subtype.ext (Complex.ext h1 h2)

/-- Wrong model: a constant map from the circle is not injective, so `jordan_curve_theorem` does not apply. -/
example : ¬ Function.Injective (fun _ : Circle => ((0 : ℝ), (0 : ℝ))) := by
  intro h
  have := @h 1 (-1) rfl
  have h2 := congrArg (fun w : Circle => (w : ℂ)) this
  norm_num at h2

end Lightlike.PL
