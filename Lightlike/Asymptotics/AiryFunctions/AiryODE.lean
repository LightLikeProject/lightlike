import Lightlike.Asymptotics.AiryFunctions.AiryDef

/-!
# The Airy power series solve `y'' = x y` (row G2-019)

For `y = evalSeries (airyCoeff a₀ a₁)` we prove `y' = evalSeries (dcoef c)` and
`y'' = x · y` (`airySeries_hasDerivAt`, `airySeries_hasDerivAt'`), and the value
`y(0) = a₀`, `y'(0) = a₁`.
-/

noncomputable section

namespace Lightlike.Airy

/-- An entire series converges at every point. -/
theorem Entire.summable {c : ℕ → ℝ} (hc : Entire c) (x : ℝ) : Summable fun n => c n * x ^ n := by
  refine Summable.of_norm ?_
  refine (hc.summable_abs (abs_nonneg x)).congr fun n => ?_
  simp [Real.norm_eq_abs]

/-- The second-derivative coefficients of the Airy series: `0` at `0`, and `c_m` at `m+1`. -/
theorem dcoef_dcoef_airyCoeff_zero (a0 a1 : ℝ) :
    dcoef (dcoef (airyCoeff a0 a1)) 0 = 0 := by
  simp [dcoef]

theorem dcoef_dcoef_airyCoeff_succ (a0 a1 : ℝ) (m : ℕ) :
    dcoef (dcoef (airyCoeff a0 a1)) (m + 1) = airyCoeff a0 a1 m := by
  have h := airyCoeff_succ_succ_succ a0 a1 m
  have hne : (((m : ℝ) + 3) * ((m : ℝ) + 2)) ≠ 0 := by positivity
  simp only [dcoef]
  push_cast
  rw [show m + 1 + 1 + 1 = m + 3 from rfl, h]
  field_simp
  ring

/-- The second derivative series equals `x` times the series. -/
theorem evalSeries_dcoef_dcoef (a0 a1 x : ℝ) :
    evalSeries (dcoef (dcoef (airyCoeff a0 a1))) x = x * evalSeries (airyCoeff a0 a1) x := by
  have hs := ((airyCoeff_entire a0 a1).deriv.deriv).summable x
  unfold evalSeries
  rw [hs.tsum_eq_zero_add, dcoef_dcoef_airyCoeff_zero, zero_mul, zero_add, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [dcoef_dcoef_airyCoeff_succ]
  ring

/-- First derivative of the Airy series. -/
theorem airySeries_hasDerivAt (a0 a1 x : ℝ) :
    HasDerivAt (evalSeries (airyCoeff a0 a1)) (evalSeries (dcoef (airyCoeff a0 a1)) x) x :=
  (airyCoeff_entire a0 a1).hasDerivAt_eval x

/-- Second derivative of the Airy series: `y'' = x y`. -/
theorem airySeries_hasDerivAt' (a0 a1 x : ℝ) :
    HasDerivAt (evalSeries (dcoef (airyCoeff a0 a1))) (x * evalSeries (airyCoeff a0 a1) x) x := by
  rw [← evalSeries_dcoef_dcoef]
  exact (airyCoeff_entire a0 a1).deriv.hasDerivAt_eval x

/-- Initial value of the series. -/
theorem evalSeries_zero (c : ℕ → ℝ) : evalSeries c 0 = c 0 := by
  unfold evalSeries
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

theorem airySeries_zero (a0 a1 : ℝ) : evalSeries (airyCoeff a0 a1) 0 = a0 := by
  rw [evalSeries_zero]; rfl

theorem airySeries_deriv_zero (a0 a1 : ℝ) : evalSeries (dcoef (airyCoeff a0 a1)) 0 = a1 := by
  rw [evalSeries_zero]
  simp [dcoef]

end Lightlike.Airy
