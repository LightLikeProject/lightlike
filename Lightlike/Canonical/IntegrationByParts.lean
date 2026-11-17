import Mathlib
import Lightlike.Spacetime.Curvature

/-!
# The integral of a coordinate derivative of a compactly supported function vanishes
-/

open MeasureTheory Metric Set
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **The integral of `∂_k F` vanishes** for a compactly supported `C¹` function `F` on `ℝᵈ`. -/
theorem integral_pd_eq_zero {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (k : Fin d) : ∫ x, Lightlike.pd k F x = 0 := by
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_closedBall (0 : Fin d → ℝ)
  set f : ContDiffBump (0 : Fin d → ℝ) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩ with hf
  have hfsm : ContDiff ℝ ∞ f := f.contDiff
  have hfc : HasCompactSupport f := f.hasCompactSupport
  have hone : ∀ x ∈ closedBall (0 : Fin d → ℝ) (|R| + 1), f x = 1 := fun x hx => f.one_of_mem_closedBall hx
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hsupp : ∀ x, x ∉ tsupport F → fderiv ℝ F x = 0 := fun x hx => by
    have : fderiv ℝ F x = fderiv ℝ (fun _ => (0 : ℝ)) x := by
      refine Filter.EventuallyEq.fderiv_eq ?_
      exact (notMem_tsupport_iff_eventuallyEq.mp hx)
    simpa using this
  have hbd : ∀ x ∈ tsupport F, x ∈ closedBall (0 : Fin d → ℝ) (|R|) := fun x hx => by
    have := hR hx
    exact closedBall_subset_closedBall (le_abs_self R) this
  have hv : (Pi.single k (1 : ℝ) : Fin d → ℝ) = Pi.single k 1 := rfl
  have hcontF' : Continuous (fun x => fderiv ℝ F x (Pi.single k 1)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontf' : Continuous (fun x => fderiv ℝ f x (Pi.single k 1)) :=
    (hfsm.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint1 : Integrable (fun x => fderiv ℝ f x (Pi.single k 1) * F x) volume :=
    (hcontf'.mul hF.continuous).integrable_of_hasCompactSupport hFc.mul_left
  have hint2 : Integrable (fun x => f x * fderiv ℝ F x (Pi.single k 1)) volume := by
    refine (hfsm.continuous.mul hcontF').integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hFc.isCompact fun x hx => ?_
    simp [hsupp x hx]
  have hint3 : Integrable (fun x => f x * F x) volume :=
    (hfsm.continuous.mul hF.continuous).integrable_of_hasCompactSupport hFc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := (Pi.single k (1 : ℝ) : Fin d → ℝ))
    hint1 hint2 hint3 (fun x _ => (hfsm.differentiable (by simp)) x) (fun x _ => hFd x)
  have h1 : ∫ x, f x * fderiv ℝ F x (Pi.single k 1) = ∫ x, Lightlike.pd k F x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ tsupport F
    · rw [hone x (closedBall_subset_closedBall (by linarith) (hbd x hx))]; simp [Lightlike.pd]
    · simp [Lightlike.pd, hsupp x hx]
  have h2 : ∫ x, fderiv ℝ f x (Pi.single k 1) * F x = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport F
    · have hxb : x ∈ ball (0 : Fin d → ℝ) (|R| + 1) :=
        mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp (hbd x hx)) (by linarith))
      have : fderiv ℝ f x = 0 := by
        have hev : f =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
          Filter.eventually_of_mem (isOpen_ball.mem_nhds hxb) fun y hy => hone y (ball_subset_closedBall hy)
        simpa using hev.fderiv_eq
      simp [this]
    · have : F x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  rw [h1, h2] at key
  simpa using key

/-- A coordinate derivative of a smooth compactly supported function is integrable. -/
lemma integrable_pd {F : (Fin d → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (k : Fin d) :
    Integrable (Lightlike.pd k F) volume := by
  have hc : Continuous (Lightlike.pd k F) := by
    have := (hF.fderiv_right (m := 0) (by simp)).continuous.clm_apply (continuous_const (y := (Pi.single k (1 : ℝ) : Fin d → ℝ)))
    exact this
  refine hc.integrable_of_hasCompactSupport ?_
  exact hFc.fderiv_apply (𝕜 := ℝ) (Pi.single k 1)

/-- **The integral of a sum of coordinate derivatives vanishes.** -/
theorem integral_sum_pd_eq_zero {F : Fin d → (Fin d → ℝ) → ℝ} (hF : ∀ k, ContDiff ℝ ∞ (F k))
    (hFc : ∀ k, HasCompactSupport (F k)) :
    Integrable (fun x => ∑ k, Lightlike.pd k (F k) x) volume ∧ ∫ x, ∑ k, Lightlike.pd k (F k) x = 0 := by
  refine ⟨integrable_finsetSum _ fun k _ => integrable_pd (hF k) (hFc k) k, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_pd (hF k) (hFc k) k]
  exact Finset.sum_eq_zero fun k _ => integral_pd_eq_zero ((hF k).of_le (by simp)) (hFc k) k

end Lightlike.Canonical

end
