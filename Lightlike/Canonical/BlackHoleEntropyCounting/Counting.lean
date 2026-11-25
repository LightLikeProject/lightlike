import Mathlib

/-!
# The puncture-counting equation (row G2-016, milestone CA6)

Black-hole entropy from puncture counting (Domagala–Lewandowski 2004, Meissner 2004): a puncture of
spin `j = (n+1)/2` (`n : ℕ`) carries the area `8πγ ℓ_P² √(j(j+1))`, so that `A/4ℓ_P²` per puncture is
`2πγ √(j(j+1)) = (π γ) √((n+1)(n+3))`. If a puncture of label `n` has `w n` states, the number of
states of area `≤ A` grows like `exp(λ A/4)` where `λ = γ_M/γ` and `γ_M` is the root of
`∑ₙ w n · exp(-π γ_M √((n+1)(n+3))) = 1`.

This file proves the analytic skeleton, for any weight with `0 ≤ w n ≤ n + 2` and `w 0 > 0`:

* `countSum w γ` is summable for `γ > 0`, continuous and strictly decreasing on `(0, ∞)`
  (`summable_term`, `continuousOn_countSum`, `strictAntiOn_countSum`);
* a root of `countSum w γ = 1` is unique, and exists as soon as the sum is `> 1` at one point and
  `< 1` at a larger one (`root_unique`, `exists_root_of_lt_gt`).

The numerical value `γ_M ≈ 0.2375` is in later files of this folder.
-/

open Real

namespace Lightlike.Rows.G2_016

/-- The label `n ↦ √((n+1)(n+3)) = 2√(j(j+1))` with `j = (n+1)/2`: the area of a spin-`j`
puncture, in units of `4πγ ℓ_P²`. -/
noncomputable def areaLabel (n : ℕ) : ℝ := √(((n : ℝ) + 1) * ((n : ℝ) + 3))

/-- The counting sum `∑ₙ w n · exp(-π γ √((n+1)(n+3)))` for a puncture degeneracy `w`. -/
noncomputable def countSum (w : ℕ → ℝ) (γ : ℝ) : ℝ :=
  ∑' n : ℕ, w n * Real.exp (-(π * γ * areaLabel n))

/-- `areaLabel n ≥ n + 1`. -/
theorem areaLabel_ge (n : ℕ) : (n : ℝ) + 1 ≤ areaLabel n := by
  unfold areaLabel
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- `areaLabel n > 0`. -/
theorem areaLabel_pos (n : ℕ) : 0 < areaLabel n := by
  have := areaLabel_ge n
  have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The geometric-type majorant `(n+2) rⁿ` is summable for `0 ≤ r < 1`. -/
theorem summable_majorant {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) * r ^ n) := by
  have h : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have h1' := summable_pow_mul_geometric_of_norm_lt_one 1 h
  have h2 := (summable_geometric_of_lt_one h0 h1).mul_left 2
  refine (h1'.add h2).congr ?_
  intro n
  simp only [pow_one]
  ring

/-- For `γ ≥ a > 0` the term is bounded by `(n+2) exp(-π a)ⁿ`. -/
theorem term_le {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2) {a γ : ℝ} (ha : 0 < a)
    (hγ : a ≤ γ) (n : ℕ) :
    ‖w n * Real.exp (-(π * γ * areaLabel n))‖ ≤ ((n : ℝ) + 2) * (Real.exp (-(π * a))) ^ n := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 n) (Real.exp_pos _).le), ← Real.exp_nat_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply mul_le_mul (hw n) _ (Real.exp_pos _).le (by linarith)
  apply Real.exp_le_exp.2
  have h1 := areaLabel_ge n
  have hp := Real.pi_pos
  have : π * a * n ≤ π * γ * areaLabel n := by
    have : π * a * n ≤ π * γ * n := by
      apply mul_le_mul_of_nonneg_right _ hn
      exact mul_le_mul_of_nonneg_left hγ hp.le
    have h2 : π * γ * n ≤ π * γ * areaLabel n := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.le (by linarith))
      linarith
    linarith
  linarith

/-- The counting series is summable for `γ > 0`. -/
theorem summable_term {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2) {γ : ℝ}
    (hγ : 0 < γ) : Summable (fun n : ℕ => w n * Real.exp (-(π * γ * areaLabel n))) := by
  have hr : Real.exp (-(π * γ)) < 1 := by
    rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
  refine Summable.of_norm_bounded (summable_majorant (Real.exp_pos _).le hr) ?_
  exact fun n => term_le h0 hw hγ le_rfl n

/-- The counting sum is continuous on `(0, ∞)`. -/
theorem continuousOn_countSum {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2) :
    ContinuousOn (countSum w) (Set.Ioi 0) := by
  intro γ hγ
  have hγ' : 0 < γ := hγ
  have hmem : Set.Ici (γ / 2) ∈ nhds γ := Ici_mem_nhds (by linarith)
  have hcont : ContinuousOn (countSum w) (Set.Ici (γ / 2)) := by
    have hr : Real.exp (-(π * (γ / 2))) < 1 := by
      rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
    refine continuousOn_tsum (u := fun n : ℕ => ((n : ℝ) + 2) * (Real.exp (-(π * (γ / 2)))) ^ n)
      (fun n => ?_) (summable_majorant (Real.exp_pos _).le hr)
      (fun n x hx => term_le h0 hw (by linarith) hx n)
    fun_prop
  exact (hcont.continuousAt hmem).continuousWithinAt

/-- The counting sum is strictly decreasing on `(0, ∞)` when `w 0 > 0`. -/
theorem strictAntiOn_countSum {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2)
    (hpos : 0 < w 0) : StrictAntiOn (countSum w) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  unfold countSum
  refine Summable.tsum_lt_tsum (i := 0) (fun n => ?_) ?_ (summable_term h0 hw hb')
    (summable_term h0 hw ha')
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
      have := areaLabel_pos n
      have := Real.pi_pos
      nlinarith [mul_pos Real.pi_pos (areaLabel_pos n)])) (h0 n)
  · refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hpos
    have := areaLabel_pos 0
    have := Real.pi_pos
    nlinarith [mul_pos Real.pi_pos (areaLabel_pos 0)]

/-- A root of `countSum w γ = 1` on `(0, ∞)` is unique. -/
theorem root_unique {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2) (hpos : 0 < w 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hfa : countSum w a = 1) (hfb : countSum w b = 1) :
    a = b :=
  (strictAntiOn_countSum h0 hw hpos).injOn ha hb (hfa.trans hfb.symm)

/-- **Existence of the root.** If the counting sum is `> 1` at `a > 0` and `< 1` at `b ≥ a`,
there is a root of `countSum w γ = 1` in `[a, b]`. -/
theorem exists_root_of_lt_gt {w : ℕ → ℝ} (h0 : ∀ n, 0 ≤ w n) (hw : ∀ n, w n ≤ n + 2) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hfa : 1 < countSum w a) (hfb : countSum w b < 1) :
    ∃ γ ∈ Set.Icc a b, countSum w γ = 1 := by
  have hc : ContinuousOn (countSum w) (Set.Icc a b) :=
    (continuousOn_countSum h0 hw).mono (fun x hx => lt_of_lt_of_le ha hx.1)
  have := intermediate_value_Icc' hab hc
  exact this ⟨hfb.le, hfa.le⟩

end Lightlike.Rows.G2_016
