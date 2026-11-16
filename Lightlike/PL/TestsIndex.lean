import Lightlike.PL.Index

/-!
# Checks of the index of a loop about a point

The unit circle `t ↦ exp (2πi t)` has index `1` about the origin, and index `0` about the point `-3` outside it,
so the index detects whether the point is inside the loop. Wrong-model check: the index about the origin is not `0`
for the circle, so the two cases differ.
-/

open Complex unitInterval Real

namespace Lightlike.PL

/-- The unit circle as a loop based at `1`. -/
noncomputable def circleLoop : Path (1 : ℂ) 1 where
  toFun t := exp (2 * π * Complex.I * (t : ℝ))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop

lemma circleLoop_ne_origin : ∀ t, circleLoop t ≠ 0 := fun _ => exp_ne_zero _

private lemma two_pi_I_ne : (2 * π * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The unit circle has index `1` about the origin. -/
theorem circleLoop_ind_zero : loopIndex circleLoop 0 = 1 := by
  have h := loopIndex_spec circleLoop (Ω := 0) circleLoop_ne_origin
  let ℓ : C(I, ℂ) := ⟨fun t => 2 * π * Complex.I * (t : ℝ), by fun_prop⟩
  have hℓ : IsLog (circleLoop : C(I, ℂ)) 0 ℓ := by
    intro t
    show exp (2 * π * Complex.I * (t : ℝ)) = circleLoop t - 0
    simp [circleLoop]
  rw [logInc_eq circleLoop circleLoop_ne_origin hℓ] at h
  have h1 : ((loopIndex circleLoop 0 : ℤ) : ℂ) = 1 := by
    apply mul_right_cancel₀ two_pi_I_ne
    rw [← h, one_mul]
    show 2 * π * Complex.I * ((1 : I) : ℝ) - 2 * π * Complex.I * ((0 : I) : ℝ) = _
    simp
  exact_mod_cast h1

/-- The unit circle has index `0` about the point `-3`, which lies outside it. -/
theorem circleLoop_ind_neg_three : loopIndex circleLoop (-3) = 0 := by
  have hne : ∀ t, circleLoop t ≠ -3 := by
    intro t h
    have h1 := congrArg Complex.re h
    have h2 := Complex.abs_re_le_norm (circleLoop t)
    have hn : ‖circleLoop t‖ = 1 := by
      simp [circleLoop, Complex.norm_exp]
    obtain ⟨hl, hr⟩ := abs_le.1 (h2.trans_eq hn)
    norm_num at h1
    linarith
  have h := loopIndex_spec circleLoop (Ω := -3) hne
  have hslit : ∀ t, circleLoop t - (-3) ∈ Complex.slitPlane := by
    intro t
    left
    have h2 : -1 ≤ (circleLoop t).re := by
      have := Complex.abs_re_le_norm (circleLoop t)
      have hn : ‖circleLoop t‖ = 1 := by simp [circleLoop, Complex.norm_exp]
      linarith [abs_le.1 (this.trans_eq hn)]
    simp
    linarith
  let ℓ : C(I, ℂ) := ⟨fun t => Complex.log (circleLoop t - (-3)), by
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact ((circleLoop.continuous.sub continuous_const).continuousAt).clog (hslit t)⟩
  have hℓ : IsLog (circleLoop : C(I, ℂ)) (-3) ℓ := fun t => Complex.exp_log (by
    exact Complex.slitPlane_ne_zero (hslit t))
  rw [logInc_eq circleLoop hne hℓ] at h
  have h0 : ℓ 1 - ℓ 0 = 0 := by
    show Complex.log (circleLoop 1 - (-3)) - Complex.log (circleLoop 0 - (-3)) = 0
    simp
  rw [h0] at h
  have h1 : ((loopIndex circleLoop (-3) : ℤ) : ℂ) = 0 := by
    have := h.symm
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exact absurd h' two_pi_I_ne
  exact_mod_cast h1

/-- Wrong model: the indices about the origin and about `-3` differ, so the index is not constant in the
point. -/
example : loopIndex circleLoop 0 ≠ loopIndex circleLoop (-3) := by
  rw [circleLoop_ind_zero, circleLoop_ind_neg_three]
  decide

end Lightlike.PL
