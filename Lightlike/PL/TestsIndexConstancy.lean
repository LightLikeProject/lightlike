import Lightlike.PL.IndexConstancy
import Lightlike.PL.TestsIndex

/-!
# Checks of the constancy of the index and of the half plane lemma

Non-vacuity of `loopIndex_eq_of_joinedIn`: the points `0` and `1/2`, both inside the unit circle, are joined by a
segment that avoids the circle, so they have the same index (`1`). Non-vacuity of `loopIndex_eq_zero_of_halfplane`: a
constant loop lies in a half plane and has index `0`. Wrong-model check: the unit circle about the origin has index `1`,
so it lies in no half plane seen from the origin.
-/

open Complex unitInterval Real

namespace Lightlike.PL

/-- The points `0` and `1/2` are joined by a path off the unit circle. -/
lemma joined_zero_half : JoinedIn (Set.range circleLoop)ᶜ (0 : ℂ) (1 / 2) := by
  refine JoinedIn.of_segment_subset ?_
  intro z hz ⟨t, ht⟩
  have hn : ‖circleLoop t‖ = 1 := by simp [circleLoop, Complex.norm_exp]
  rw [ht] at hn
  have hz' : ‖z‖ ≤ 1 / 2 := by
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hz
    simp only [smul_zero, zero_add, norm_smul, norm_div, norm_one, Complex.norm_ofNat]
    rw [Real.norm_of_nonneg hy]
    nlinarith
  linarith

/-- Non-vacuity of Lemma 9.13: the index about `1/2` is the index about `0`, that is `1`. -/
example : loopIndex circleLoop (1 / 2) = 1 := by
  rw [← loopIndex_eq_of_joinedIn circleLoop joined_zero_half]
  exact circleLoop_ind_zero

/-- Non-vacuity of Lemma 9.12: a constant loop lies in the half plane `re w > 0` and has index `0`. -/
example : loopIndex (Path.refl (1 : ℂ)) 0 = 0 :=
  loopIndex_eq_zero_of_halfplane (u := 1) _ (fun _ => by simp)

/-- Wrong model: the unit circle about the origin lies in no half plane seen from the origin, because its index is
`1`, not `0`. -/
example : ¬ ∃ u : ℂ, ∀ t, 0 < ((starRingEnd ℂ) u * (circleLoop t - 0)).re := by
  rintro ⟨u, hu⟩
  have := loopIndex_eq_zero_of_halfplane circleLoop hu
  rw [circleLoop_ind_zero] at this
  exact one_ne_zero this

end Lightlike.PL
