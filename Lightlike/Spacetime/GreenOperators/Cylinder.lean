import Mathlib
import Lightlike.Spacetime.GreenOperators.Uniqueness

/-!
# Failure of uniqueness with closed timelike curves: the time-periodic cylinder

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`), trust check
"a spacetime with closed timelike curves where uniqueness fails".

Take the quotient of `1+1` Minkowski space by the time translation `(t, x) ↦ (t + 1, x)`: a flat
Lorentzian cylinder whose integral curves of `∂ₜ` are closed timelike curves.  Functions on it are
functions on `ℝ × ℝ` that are `1`-periodic in `t`, and `kgOp m` is the local expression of the
Klein–Gordon operator.  For `m = 2π` the function `sin (2π t)` is a nonzero periodic solution of the
homogeneous equation (`cylinder_nonuniqueness`), so the Cauchy-type uniqueness of `retarded_unique`
fails: the only thing that survives is that a periodic function vanishing for `t < T` is zero
(`periodic_eq_zero_of_eq_zero_before`), so the retarded condition has no content on the cylinder.

This is a supporting result; no catalogue entry.
-/

open Set Real

namespace Lightlike.GreenOperators

/-- The time-periodic solution `sin (2π t)` of the Klein–Gordon equation of mass `2π`. -/
noncomputable def periodicSol : ℝ × ℝ → ℝ := fun p => Real.sin (2 * π * p.1)

lemma periodicSol_contDiff : ContDiff ℝ 2 periodicSol := by
  unfold periodicSol
  fun_prop

lemma periodicSol_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt periodicSol ((2 * π * Real.cos (2 * π * p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => 2 * π * q.1) ((2 * π) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.const_mul (2 * π)
  have := h1.sin
  have e : (2 * π * Real.cos (2 * π * p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ =
      Real.cos (2 * π * p.1) • (2 * π) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [smul_smul, mul_comm]
  rw [e]
  exact this

lemma fderiv_periodicSol :
    fderiv ℝ periodicSol =
      fun p => (2 * π * Real.cos (2 * π * p.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
  funext p
  exact (periodicSol_hasFDerivAt p).fderiv

lemma fderiv_fderiv_periodicSol (p v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ periodicSol) p v w =
      -(2 * π) ^ 2 * Real.sin (2 * π * p.1) * v.1 * w.1 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => 2 * π * q.1) ((2 * π) • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.const_mul (2 * π)
  have h2 := (h1.cos.const_mul (2 * π)).smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)
  rw [fderiv_periodicSol]
  rw [h2.fderiv]
  simp
  left
  ring

/-- `sin (2π t)` solves the Klein–Gordon equation of mass `2π`. -/
lemma kgOp_periodicSol : kgOp (2 * π) periodicSol = 0 := by
  funext p
  unfold kgOp
  rw [fderiv_fderiv_periodicSol, fderiv_fderiv_periodicSol]
  simp only [periodicSol, Pi.zero_apply]
  ring

/-- **Uniqueness fails with closed timelike curves.**  On the time-periodic cylinder
(`1`-periodic functions of `(t, x)`), the homogeneous Klein–Gordon equation of mass `2π` has the
nonzero `C²` solution `sin (2π t)` besides `0`. -/
theorem cylinder_nonuniqueness :
    ∃ u : ℝ × ℝ → ℝ, ContDiff ℝ 2 u ∧ (∀ p : ℝ × ℝ, u (p.1 + 1, p.2) = u p) ∧
      kgOp (2 * π) u = kgOp (2 * π) 0 ∧ u ≠ 0 := by
  refine ⟨periodicSol, periodicSol_contDiff, ?_, ?_, ?_⟩
  · intro p
    simp only [periodicSol]
    rw [mul_add, mul_one, Real.sin_add_two_pi]
  · rw [kgOp_periodicSol]
    funext p
    simp [kgOp]
  · intro h
    have := congrFun h (1 / 4, 0)
    simp [periodicSol] at this
    have h2 : 2 * π * 4⁻¹ = π / 2 := by ring
    rw [h2] at this
    simp at this

/-- A time-periodic function that vanishes for `t < T` vanishes identically. -/
lemma periodic_eq_zero_of_eq_zero_before {u : ℝ × ℝ → ℝ} (hper : ∀ p : ℝ × ℝ, u (p.1 + 1, p.2) = u p)
    {T : ℝ} (h0 : ∀ p : ℝ × ℝ, p.1 < T → u p = 0) : u = 0 := by
  have hn : ∀ n : ℕ, ∀ p : ℝ × ℝ, u (p.1 - n, p.2) = u p := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ k ih =>
      intro p
      have h := hper (p.1 - ((k + 1 : ℕ) : ℝ), p.2)
      have e : p.1 - ((k + 1 : ℕ) : ℝ) + 1 = p.1 - k := by push_cast; ring
      simp only [e] at h
      rw [← h]
      exact ih p
  funext p
  obtain ⟨n, hn'⟩ := exists_nat_gt (p.1 - T)
  rw [← hn n p]
  exact h0 _ (by simp only; linarith)

end Lightlike.GreenOperators
