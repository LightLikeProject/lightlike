import Lightlike.Canonical.BlackHoleEntropyCounting.Counting

/-!
# Numerical tools for the counting root (row G2-016, milestone CA6)

Generic term-by-term bounds used to localise the root `γ_M` of `countSum (fun _ => 2) γ = 1`
(`Lightlike.Canonical.BlackHoleEntropyCounting.countSum`). With `m = n + 2` the area label is
`areaLabel n = √(m² - 1) = m - δ` for a small `δ`, so that
`exp(-π γ areaLabel n) = exp(-π γ)^m · exp(π γ δ)`; one only needs bounds for `q = exp(-π γ)` and
a polynomial bound for `exp` on `[0, 1]`.
-/

open Real

namespace Lightlike.Canonical.BlackHoleEntropyCounting

/-- Upper degree-6 Taylor bound for `exp` on `[0,1]` (with Lagrange-type remainder). -/
noncomputable def polyUp (y : ℝ) : ℝ :=
  1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 * 7 / 4320

/-- Lower degree-5 Taylor bound for `exp` on `[0,∞)`. -/
noncomputable def polyLo (y : ℝ) : ℝ :=
  1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120

/-- `exp y ≤ polyUp y0` for `0 ≤ y ≤ y0 ≤ 1`. -/
theorem exp_le_polyUp {y y0 : ℝ} (h0 : 0 ≤ y) (hy : y ≤ y0) (h1 : y0 ≤ 1) :
    Real.exp y ≤ polyUp y0 := by
  have h := Real.exp_bound' (le_trans h0 hy) h1 (n := 6) (by norm_num)
  have h2 : Real.exp y ≤ Real.exp y0 := Real.exp_le_exp.2 hy
  refine h2.trans (h.trans (le_of_eq ?_))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, polyUp]
  push_cast
  ring

/-- `polyLo y1 ≤ exp y` for `0 ≤ y1 ≤ y`. -/
theorem polyLo_le_exp {y y1 : ℝ} (h0 : 0 ≤ y1) (hy : y1 ≤ y) :
    polyLo y1 ≤ Real.exp y := by
  have h := Real.sum_le_exp_of_nonneg h0 6
  have h2 : Real.exp y1 ≤ Real.exp y := Real.exp_le_exp.2 hy
  refine le_trans (le_of_eq ?_) (h.trans h2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, polyLo]
  push_cast
  ring

/-- `areaLabel n ≥ m - 1/m` with `m = n + 2`. -/
theorem areaLabel_ge_sub (n : ℕ) : (n : ℝ) + 2 - 1 / ((n : ℝ) + 2) ≤ areaLabel n := by
  unfold areaLabel
  have hm : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  apply Real.le_sqrt_of_sq_le
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1 : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have : ((n : ℝ) + 2 - 1 / ((n : ℝ) + 2)) ^ 2 =
      ((n : ℝ) + 1) * ((n : ℝ) + 3) + (1 / ((n : ℝ) + 2) ^ 2 - 1) := by
    field_simp
    ring
  linarith

/-- **Upper bound for one term.** If `exp(-πγ) ≤ q`, `s ≤ areaLabel n`, `s ≤ n+2` and
`πγ(n+2-s) ≤ y0 ≤ 1`, then `exp(-πγ areaLabel n) ≤ q^(n+2) · polyUp y0`. -/
theorem term_up {γ q y0 s : ℝ} (hγ : 0 ≤ γ) (hq : Real.exp (-(π * γ)) ≤ q) (n : ℕ)
    (hs : s ≤ areaLabel n) (hsm : s ≤ (n : ℝ) + 2) (hy : π * γ * (((n : ℝ) + 2) - s) ≤ y0)
    (hy1 : y0 ≤ 1) :
    Real.exp (-(π * γ * areaLabel n)) ≤ q ^ (n + 2) * polyUp y0 := by
  have hp : 0 ≤ π * γ := mul_nonneg Real.pi_pos.le hγ
  have e1 : Real.exp (-(π * γ * areaLabel n)) ≤ Real.exp (-(π * γ * s)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hs hp
    linarith
  have e2 : Real.exp (-(π * γ * s)) =
      Real.exp (-(π * γ)) ^ (n + 2) * Real.exp (π * γ * (((n : ℝ) + 2) - s)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have e3 : Real.exp (-(π * γ)) ^ (n + 2) ≤ q ^ (n + 2) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hq _
  have e4 : 0 ≤ π * γ * (((n : ℝ) + 2) - s) := mul_nonneg hp (by linarith)
  have e5 := exp_le_polyUp e4 hy hy1
  rw [e2] at e1
  refine e1.trans (mul_le_mul e3 e5 (Real.exp_pos _).le (pow_nonneg ((Real.exp_pos _).le.trans hq) _))

/-- **Lower bound for one term.** If `0 ≤ q ≤ exp(-πγ)`, `areaLabel n ≤ t` and
`0 ≤ y1 ≤ πγ(n+2-t)`, then `q^(n+2) · polyLo y1 ≤ exp(-πγ areaLabel n)`. -/
theorem term_low {γ q y1 t : ℝ} (hγ : 0 ≤ γ) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(π * γ))) (n : ℕ)
    (ht : areaLabel n ≤ t) (hy0 : 0 ≤ y1)
    (hy : y1 ≤ π * γ * (((n : ℝ) + 2) - t)) :
    q ^ (n + 2) * polyLo y1 ≤ Real.exp (-(π * γ * areaLabel n)) := by
  have hp : 0 ≤ π * γ := mul_nonneg Real.pi_pos.le hγ
  have e1 : Real.exp (-(π * γ * t)) ≤ Real.exp (-(π * γ * areaLabel n)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left ht hp
    linarith
  have e2 : Real.exp (-(π * γ * t)) =
      Real.exp (-(π * γ)) ^ (n + 2) * Real.exp (π * γ * (((n : ℝ) + 2) - t)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have e3 : q ^ (n + 2) ≤ Real.exp (-(π * γ)) ^ (n + 2) := pow_le_pow_left₀ hq0 hq _
  have e5 := polyLo_le_exp hy0 hy
  have e6 : 0 ≤ polyLo y1 := by
    unfold polyLo
    positivity
  rw [e2] at e1
  exact (mul_le_mul e3 e5 e6 (pow_nonneg (Real.exp_pos _).le _)).trans e1

end Lightlike.Canonical.BlackHoleEntropyCounting

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.areaLabel_ge_sub := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.areaLabel_ge_sub
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.exp_le_polyUp := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.exp_le_polyUp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.polyLo := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.polyLo
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.polyLo_le_exp := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.polyLo_le_exp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.polyUp := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.polyUp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.term_low := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.term_low
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.term_up := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.term_up
