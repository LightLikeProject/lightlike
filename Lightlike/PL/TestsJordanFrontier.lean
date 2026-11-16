import Lightlike.PL.JordanFrontier
import Lightlike.PL.TestsJordan

/-!
# Checks of the frontier of the components of the complement of a Jordan curve

Non-vacuity of `jordan_frontier`: the unit circle satisfies its hypotheses, and the origin is a point of its
complement. Wrong-model check: a constant map is not injective, so the hypotheses fail for it.
-/

open Set

namespace Lightlike.PL

/-- Non-vacuity: the frontier of the component of the origin in the complement of the unit circle is the
circle. -/
example : frontier (connectedComponentIn (range unitCircle)ᶜ ((0 : ℝ), (0 : ℝ))) = range unitCircle := by
  refine jordan_frontier unitCircle_continuous unitCircle_injective ?_
  rintro ⟨z, hz⟩
  have h1 : ((z : ℂ).re) = 0 := congrArg Prod.fst hz
  have h2 : ((z : ℂ).im) = 0 := congrArg Prod.snd hz
  have : ((z : ℂ)) = 0 := Complex.ext h1 h2
  exact z.coe_ne_zero this

/-- Wrong model: the constant map is not injective, so `jordan_frontier` does not apply to it. -/
example : ¬ Function.Injective (fun _ : Circle => ((0 : ℝ), (0 : ℝ))) := by
  intro h
  have h1 := h (a₁ := 1) (a₂ := -1) rfl
  have h2 := congrArg (fun z : Circle => (z : ℂ)) h1
  norm_num at h2

end Lightlike.PL
