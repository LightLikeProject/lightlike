import Mathlib

/-!
# A second-order Taylor bound for a `C³` function of one variable

If `f` is `C³` at `0` with `f 0 = 0` and `f' 0 = 0`, then `f ε = (f'' 0 / 2) ε² + O(ε³)`
near `0` (`taylor2_cubic`). It is the one-variable step of the second-order expansion of the
Regge action along a family of lengths (`SecondOrder.lean`).

## Main results

* `taylor2_cubic`: the bound, with explicit use of the third derivative on a ball.
-/

open Filter Topology Set

namespace Lightlike.Regge.Linear3

/-- **Second-order Taylor bound.** If `f` is `C³` at `0` with `f 0 = 0` and `f' 0 = 0`, then
`f ε = (f'' 0 / 2) ε² + O(ε³)` near `0`. -/
theorem taylor2_cubic {f : ℝ → ℝ} (hf : ContDiffAt ℝ 3 f 0) (h0 : f 0 = 0) (h1 : deriv f 0 = 0) :
    ∃ M r : ℝ, 0 < r ∧ ∀ ε : ℝ, |ε| ≤ r → |f ε - deriv (deriv f) 0 / 2 * ε ^ 2| ≤ M * |ε| ^ 3 := by
  obtain ⟨r0, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hf.eventually (by simp))
  have hO : IsOpen (Metric.ball (0 : ℝ) r0) := Metric.isOpen_ball
  have hfU : ContDiffOn ℝ 3 f (Metric.ball 0 r0) := fun y hy => (hball y hy).contDiffWithinAt
  have h1U : ContDiffOn ℝ 2 (deriv f) (Metric.ball 0 r0) := hfU.deriv_of_isOpen hO (by norm_num)
  have h2U : ContDiffOn ℝ 1 (deriv (deriv f)) (Metric.ball 0 r0) := h1U.deriv_of_isOpen hO (by norm_num)
  have h3U : ContinuousOn (deriv (deriv (deriv f))) (Metric.ball 0 r0) :=
    (h2U.deriv_of_isOpen hO (by norm_num) : ContDiffOn ℝ 0 _ _).continuousOn
  set r := r0 / 2 with hr
  have hrpos : 0 < r := by positivity
  have hsub : Metric.closedBall (0 : ℝ) r ⊆ Metric.ball 0 r0 := Metric.closedBall_subset_ball (by linarith)
  obtain ⟨K3, hK3⟩ := (isCompact_closedBall (0 : ℝ) r).exists_bound_of_continuousOn (h3U.mono hsub)
  have hK3' : ∀ x, |x| ≤ r → |deriv (deriv (deriv f)) x| ≤ |K3| := fun x hx => by
    have := hK3 x (by simpa [Metric.mem_closedBall, Real.dist_eq] using hx)
    exact this.trans (le_abs_self _)
  have hconv : ∀ ρ, 0 ≤ ρ → ρ ≤ r → Convex ℝ (Metric.closedBall (0 : ℝ) ρ) := fun _ _ _ => convex_closedBall _ _
  have hin : ∀ ρ, ρ ≤ r → Metric.closedBall (0 : ℝ) ρ ⊆ Metric.ball 0 r0 := fun ρ hρ =>
    (Metric.closedBall_subset_closedBall hρ).trans hsub
  have hd2 : ∀ x ∈ Metric.ball (0 : ℝ) r0, HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x :=
    fun x hx => ((h2U.differentiableOn (by norm_num) x hx).differentiableAt (hO.mem_nhds hx)).hasDerivAt
  have hd1 : ∀ x ∈ Metric.ball (0 : ℝ) r0, HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    fun x hx => ((h1U.differentiableOn (by norm_num) x hx).differentiableAt (hO.mem_nhds hx)).hasDerivAt
  have hd0 : ∀ x ∈ Metric.ball (0 : ℝ) r0, HasDerivAt f (deriv f x) x :=
    fun x hx => ((hfU.differentiableOn (by norm_num) x hx).differentiableAt (hO.mem_nhds hx)).hasDerivAt
  refine ⟨|K3|, r, hrpos, fun ε hε => ?_⟩
  set c := deriv (deriv f) 0
  have hmem : ∀ x, x ∈ Metric.closedBall (0 : ℝ) |ε| ↔ |x| ≤ |ε| := fun x => by
    simp [Metric.mem_closedBall, Real.dist_eq]
  have hA : ∀ x, |x| ≤ |ε| → |deriv (deriv f) x - c| ≤ |K3| * |ε| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := deriv (deriv f))
      (f' := deriv (deriv (deriv f))) (s := Metric.closedBall 0 |ε|) (C := |K3|)
      (fun y hy => (hd2 y (hin _ hε hy)).hasDerivWithinAt)
      (fun y hy => by
        have := hK3' y (((hmem y).1 hy).trans hε)
        simpa using this)
      (hconv _ (abs_nonneg _) hε) (Metric.mem_closedBall_self (abs_nonneg _)) ((hmem x).2 hx)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
  have hB : ∀ x, |x| ≤ |ε| → |deriv f x - c * x| ≤ |K3| * |ε| * |ε| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun y => deriv f y - c * y)
      (f' := fun y => deriv (deriv f) y - c) (s := Metric.closedBall 0 |ε|) (C := |K3| * |ε|)
      (fun y hy => ((hd1 y (hin _ hε hy)).sub ((hasDerivAt_id y).const_mul c)).hasDerivWithinAt.congr_deriv (by simp))
      (fun y hy => by rw [Real.norm_eq_abs]; exact hA y ((hmem y).1 hy))
      (hconv _ (abs_nonneg _) hε) (Metric.mem_closedBall_self (abs_nonneg _)) ((hmem x).2 hx)
    simp only [h1, mul_zero, sub_zero, zero_sub, norm_neg, Real.norm_eq_abs] at this
    have := this
    calc |deriv f x - c * x| ≤ |K3| * |ε| * |x| := by simpa [h1] using this
      _ ≤ |K3| * |ε| * |ε| := mul_le_mul_of_nonneg_left hx (by positivity)
  have hC := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun y => f y - c / 2 * y ^ 2)
    (f' := fun y => deriv f y - c * y) (s := Metric.closedBall 0 |ε|) (C := |K3| * |ε| * |ε|)
    (fun y hy => ((hd0 y (hin _ hε hy)).sub (((hasDerivAt_pow 2 y).const_mul (c / 2)))).hasDerivWithinAt.congr_deriv
      (by simp; ring))
    (fun y hy => by rw [Real.norm_eq_abs]; exact hB y ((hmem y).1 hy))
    (hconv _ (abs_nonneg _) hε) (Metric.mem_closedBall_self (abs_nonneg _))
    ((hmem ε).2 le_rfl)
  simp only [h0, zero_sub, sub_zero, norm_neg, Real.norm_eq_abs] at hC
  have e : ∀ y : ℝ, (f y - c / 2 * y ^ 2) = f y - c / 2 * y ^ 2 := fun _ => rfl
  simp at hC
  calc |f ε - c / 2 * ε ^ 2| ≤ |K3| * |ε| * |ε| * |ε - 0| := by simpa [h0] using hC
    _ = |K3| * |ε| ^ 3 := by rw [sub_zero]; ring

end Lightlike.Regge.Linear3
