import Lightlike.Rows.G2_019.Airy
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Positivity of `Bi` on `[0,∞)` and monotonicity of `Ai/Bi` (row G2-019)

The Taylor coefficients of `Bi` (initial data `Bi(0) > 0`, `Bi'(0) > 0`) are all nonnegative, so
`Bi ≥ Bi(0) > 0` and `Bi' ≥ 0` on `[0,∞)` (`airyBi_pos`, `airyBiDeriv_nonneg`).  Together with the
Wronskian `W(Ai,Bi) = 1/π` this gives `(Ai/Bi)' = -1/(π Bi²) < 0`, so `Ai/Bi` is strictly decreasing
on `[0,∞)` (`airy_ratio_strictAntiOn`).  This is the first step towards the recessiveness of `Ai`
(`Ai/Bi → 0`), which is *not* proved here.
-/

noncomputable section

namespace Lightlike.Airy

theorem airyAi0_pos : 0 < airyAi0 := by
  unfold airyAi0
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.Gamma_pos_of_pos (by norm_num))

theorem airyAiDeriv0_neg : airyAiDeriv0 < 0 := by
  unfold airyAiDeriv0
  have : 0 < (3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.Gamma_pos_of_pos (by norm_num))
  linarith

/-- Nonnegative initial data give nonnegative Airy coefficients. -/
theorem airyCoeff_nonneg {a0 a1 : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (n : ℕ) :
    0 ≤ airyCoeff a0 a1 n := by
  have key : ∀ n : ℕ, 0 ≤ airyCoeff a0 a1 n ∧ 0 ≤ airyCoeff a0 a1 (n + 1) ∧
      0 ≤ airyCoeff a0 a1 (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, by simp⟩
    | succ k ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      rw [show k + 1 + 2 = k + 3 from rfl, airyCoeff_succ_succ_succ]
      exact div_nonneg ih.1 (by positivity)
  exact (key n).1

/-- The sum of a power series with nonnegative coefficients is `≥` its constant term for `x ≥ 0`. -/
theorem evalSeries_ge_const {c : ℕ → ℝ} (hc : Entire c) (hnn : ∀ n, 0 ≤ c n) {x : ℝ}
    (hx : 0 ≤ x) : c 0 ≤ evalSeries c x := by
  unfold evalSeries
  have := (hc.summable x).le_tsum 0 (fun j _ => mul_nonneg (hnn j) (pow_nonneg hx j))
  simpa using this

theorem evalSeries_nonneg {c : ℕ → ℝ} (hnn : ∀ n, 0 ≤ c n) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ evalSeries c x :=
  tsum_nonneg fun n => mul_nonneg (hnn n) (pow_nonneg hx n)

theorem airyBi0_pos : 0 < √3 * airyAi0 := mul_pos (by positivity) airyAi0_pos

theorem airyBiDeriv0_pos : 0 < -(√3 * airyAiDeriv0) := by
  have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < √3) airyAiDeriv0_neg
  linarith

/-- `Bi(x) ≥ Bi(0) > 0` for `x ≥ 0`. -/
theorem airyBi_ge {x : ℝ} (hx : 0 ≤ x) : √3 * airyAi0 ≤ airyBi x := by
  have h := evalSeries_ge_const (airyCoeff_entire (√3 * airyAi0) (-(√3 * airyAiDeriv0)))
    (airyCoeff_nonneg airyBi0_pos.le airyBiDeriv0_pos.le) hx
  simp only [airyCoeff_zero] at h
  exact h

theorem airyBi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyBi x :=
  lt_of_lt_of_le airyBi0_pos (airyBi_ge hx)

/-- `Bi'(x) ≥ 0` for `x ≥ 0`. -/
theorem airyBiDeriv_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ airyBiDeriv x := by
  have hnn : ∀ n, 0 ≤ airyCoeff (√3 * airyAi0) (-(√3 * airyAiDeriv0)) n :=
    airyCoeff_nonneg airyBi0_pos.le airyBiDeriv0_pos.le
  exact evalSeries_nonneg (fun n => mul_nonneg (by positivity) (hnn (n + 1))) hx

/-- `Ai/Bi` is strictly decreasing on `[0,∞)`, with derivative `-1/(π Bi²)`. -/
theorem airy_ratio_strictAntiOn :
    StrictAntiOn (fun x => airyAi x / airyBi x) (Set.Ici 0) := by
  have hd : ∀ x : ℝ, 0 ≤ x → HasDerivAt (fun x => airyAi x / airyBi x)
      ((airyAiDeriv x * airyBi x - airyAi x * airyBiDeriv x) / (airyBi x) ^ 2) x := by
    intro x hx
    exact (airyAi_hasDerivAt x).div (airyBi_hasDerivAt x) (airyBi_pos hx).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 ≤ x := le_of_lt hx
    rw [(hd x hx').deriv]
    have hw := airy_wronskian x
    have hB := airyBi_pos hx'
    have : airyAiDeriv x * airyBi x - airyAi x * airyBiDeriv x = -(1 / Real.pi) := by linarith
    rw [this]
    exact div_neg_of_neg_of_pos (by have := Real.pi_pos; simp; positivity) (by positivity)

end Lightlike.Airy
