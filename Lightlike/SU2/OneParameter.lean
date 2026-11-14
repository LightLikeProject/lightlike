module

public import Mathlib

/-!
# Continuous one-parameter subgroups are exponentials

Stage A of the group-level completeness proof (`Completeness.lean`). In a complete normed
`ℝ`-algebra, a continuous `φ : ℝ → 𝔸` with `φ 0 = 1` and `φ (s + t) = φ s * φ t` equals
`t ↦ exp(t • A)`.
Here `A = φ'(0)`.

Proof (the integral trick):
1. With `F t = ∫₀ᵗ φ`, `δ⁻¹ F δ → φ 0 = 1`, so `B = F δ` is invertible for small `δ > 0`.
2. `φ t · B = ∫₀^δ φ(t + s) ds = F(t + δ) - F t`, so `φ t = (F(t + δ) - F t) B⁻¹` is
   differentiable, with `φ' = φ · A` where `A = (φ δ - 1) B⁻¹`.
3. `t ↦ φ t · exp(t • (-A))` has zero derivative, so it is constant, equal to `1`.

Mathlib has the matrix exponential and its derivative, but not this theorem.

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 2 (one-parameter subgroups and the matrix exponential).
-/

@[expose] public section

open Filter Topology intervalIntegral

namespace Lightlike.SU2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- **Uniqueness**: a curve with `c 0 = 1` and `c' = c · A` is `t ↦ exp(t • A)`. -/
theorem eq_exp_of_hasDerivAt (c : ℝ → 𝔸) (A : 𝔸) (h0 : c 0 = 1)
    (hd : ∀ t, HasDerivAt c (c t * A) t) (t : ℝ) : c t = NormedSpace.exp (t • A) := by
  have hψd : ∀ t, HasDerivAt (fun t => c t * NormedSpace.exp (t • (-A))) 0 t := by
    intro t
    have := (hd t).mul (hasDerivAt_exp_smul_const (-A) t)
    convert this using 1
    have hcomm : Commute A (NormedSpace.exp (t • (-A))) :=
      Commute.exp_right ((Commute.refl A).neg_right.smul_right t)
    rw [mul_assoc, hcomm.eq, mul_neg, mul_neg, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (f := fun t => c t * NormedSpace.exp (t • (-A)))
    (fun t => (hψd t).differentiableAt) (fun t => (hψd t).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hconst
  have hexp : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left t |>.smul_right t),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  calc c t = c t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hexp, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]

/-- **Continuous one-parameter subgroups are exponentials.** -/
theorem oneParam_eq_exp (φ : ℝ → 𝔸) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hadd : ∀ s t, φ (s + t) = φ s * φ t) :
    ∃ A : 𝔸, ∀ t : ℝ, φ t = NormedSpace.exp (t • A) := by
  set F : ℝ → 𝔸 := fun u => ∫ s in (0 : ℝ)..u, φ s with hF
  have hFd : ∀ t, HasDerivAt F (φ t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hF0 : F 0 = 0 := by simp [hF]
  -- a small `δ > 0` with `‖1 - δ⁻¹ F δ‖ < 1`
  have hslope := (hFd 0).tendsto_slope_zero_right
  rw [h0] at hslope
  obtain ⟨δ, hδ, hball⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖1 - δ⁻¹ • (F (0 + δ) - F 0)‖ < 1 := by
    have hev := (hslope.eventually (Metric.ball_mem_nhds (1 : 𝔸) one_pos)).and
      self_mem_nhdsWithin
    obtain ⟨δ, h1, h2⟩ := hev.exists
    refine ⟨δ, h2, ?_⟩
    rw [dist_comm, dist_eq_norm] at h1
    exact h1
  rw [zero_add, hF0, sub_zero] at hball
  set u := Units.oneSub _ hball with hu
  have hu' : (u : 𝔸) = δ⁻¹ • F δ := by rw [hu, Units.val_oneSub]; abel
  set Binv : 𝔸 := δ⁻¹ • (↑u⁻¹ : 𝔸) with hBinv
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hB : F δ * Binv = 1 := by
    have : F δ = δ • (u : 𝔸) := by rw [hu', smul_smul, mul_inv_cancel₀ hδ0, one_smul]
    rw [hBinv, this, smul_mul_smul_comm, mul_inv_cancel₀ hδ0, one_smul, Units.mul_inv]
  -- `φ t · F δ = F (t + δ) - F t`
  have hshift : ∀ t, φ t * F δ = F (t + δ) - F t := by
    intro t
    have h1 : φ t * F δ = ∫ s in (0 : ℝ)..δ, φ t * φ s :=
      ((ContinuousLinearMap.mul ℝ 𝔸 (φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable 0 δ)).symm
    rw [h1]
    simp only [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t, add_zero, hF]
    exact (integral_interval_sub_left (hc.intervalIntegrable 0 (t + δ))
      (hc.intervalIntegrable 0 t)).symm
  -- `φ` is differentiable with `φ' = φ · A`
  set A : 𝔸 := (φ δ - 1) * Binv with hA
  have hφ : ∀ t, φ t = (F (t + δ) - F t) * Binv := by
    intro t; rw [← hshift, mul_assoc, hB, mul_one]
  have hφd : ∀ t, HasDerivAt φ (φ t * A) t := by
    intro t
    have hd : HasDerivAt (fun t => (F (t + δ) - F t) * Binv) ((φ (t + δ) - φ t) * Binv) t :=
      (((hFd (t + δ)).comp_add_const t δ).sub (hFd t)).mul_const Binv
    have heq : (fun t => (F (t + δ) - F t) * Binv) = φ := funext fun t => (hφ t).symm
    rw [heq] at hd
    convert hd using 1
    rw [hA, hadd, ← mul_assoc, mul_sub, mul_one]
  exact ⟨A, eq_exp_of_hasDerivAt φ A h0 hφd⟩

end Lightlike.SU2
