import Lightlike.Asymptotics.KernelBound

/-!
# Trust checks for the bound on Racah's kernel

* **Known value.** The half-shift inequality `Re(u log u) ≤ Re((u + ½) log(u + ½)) + log 2` is an
  equality at `u = −¼`: `Re((−¼) log(−¼)) = ½ log 2` and `Re(¼ log ¼) = −½ log 2`
  (`re_xlog_half_shift_sharp`). So the constant `log 2` cannot be lowered. The bound on the
  kernel is checked numerically for the spins `λ(1, …, 1)`, `λ = 1, 5, 20, 50`, in each of the
  three regions: the largest ratio of `|f(z)|` to `exp(kernelExp)` is `0.19` to `0.20` and to
  `exp(Re phaseC)` is `1.50` to `1.58`, flat in `λ`, so the constants are uniform under rescaling
  of the spins (`scripts/asymptotics/kernel_bound_check.py`).
* **Wrong input fails.** Without the term `log 2` the half-shift inequality is false at `u = −¼`
  (`re_xlog_half_shift_wrong`). The script also shows that the kernel bound fails in the gap
  between the face sums and the quadrilateral sums close to the real axis: there
  `|f(n + iε)|` grows like `1/ε` at integers `n`, so the three regions of the statement are
  needed.
* **Non-vacuity.** For the spins `J = (1, …, 1)`, with face sums `3` and quadrilateral sums `4`,
  each of the three regions contains a point: `z = i` (with `c = 1`), `z = 1 + i/10` (left of a
  face sum) and `z = 5 + i/10` (right of a quadrilateral sum), so the bound applies at all three
  (`racahKernel_bound_ones`).
* **Junk values.** Lean's `x/0 = 0` makes `racahKernel a b n = 0` at every integer `n`, where
  `sin(π n) = 0` (`racahKernel_intCast`, in the trust checks of the contour identity). Every
  bound here assumes `Im z > 0`, where `sin(π z) ≠ 0`, so this value never enters. Lean's `log 0 = 0` gives `Re(0 log 0) = 0`, which
  is the limit of `u log u` at `0`, so the half-shift inequality holds at `u = 0` and `u = −½` for
  the right reason.
-/

open Complex
open scoped Real

namespace Lightlike.Asymptotics

/-- `Re((−¼) log(−¼)) = ½ log 2`. -/
lemma re_xlog_neg_quarter : (xlog (-1 / 4)).re = 1 / 2 * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [re_xlog]
  have hn : ‖(-1 / 4 : ℂ)‖ = 1 / 4 := by
    rw [norm_div, norm_neg, norm_one]
    simp
  rw [hn, one_div, Real.log_inv, h4]
  simp
  ring

/-- `Re(¼ log ¼) = −½ log 2`. -/
lemma re_xlog_quarter : (xlog (1 / 4)).re = -(1 / 2 * Real.log 2) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [re_xlog]
  have hn : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by
    rw [norm_div, norm_one]
    simp
  have hl : Real.log (1 / 4) = -Real.log 4 := by rw [one_div, Real.log_inv]
  rw [hn, hl, h4]
  simp
  ring

/-- **Known value**: the half-shift inequality `re_xlog_le_re_xlog_add_half` is an equality at
`u = −¼`, so its constant `log 2` is sharp. -/
theorem re_xlog_half_shift_sharp :
    (xlog (-1 / 4)).re = (xlog (-1 / 4 + 1 / 2)).re + Real.log 2 := by
  rw [show (-1 / 4 + 1 / 2 : ℂ) = 1 / 4 by norm_num, re_xlog_neg_quarter, re_xlog_quarter]
  ring

/-- **Wrong input fails**: without the constant `log 2`, the half-shift inequality is false at
`u = −¼`. -/
theorem re_xlog_half_shift_wrong : ¬ (xlog (-1 / 4)).re ≤ (xlog (-1 / 4 + 1 / 2)).re := by
  rw [show (-1 / 4 + 1 / 2 : ℂ) = 1 / 4 by norm_num, re_xlog_neg_quarter, re_xlog_quarter]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  intro h
  linarith

/-- **Non-vacuity** of `exists_norm_racahKernel_le`: for the spins `J = (1, …, 1)` the three
regions contain the points `z = i`, `1 + i/10` and `5 + i/10`, so with `c = 1` the bound holds
at each of them. -/
theorem racahKernel_bound_ones :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ ({I, 1 + I / 10, 5 + I / 10} : Set ℂ),
      ‖racahKernel (faceN fun _ => 1) (quadN fun _ => 1) z‖ ≤
        C * Real.exp (phaseC (faceSum fun e => ((fun _ => 1 : Fin 6 → ℕ) e : ℝ) + 1 / 2)
          (quadSum fun e => ((fun _ => 1 : Fin 6 → ℕ) e : ℝ) + 1 / 2) (z + 3 / 2)).re := by
  obtain ⟨C, hC, h⟩ := exists_norm_racahKernel_le (c := 1) one_pos
  refine ⟨C, hC, fun z hz => ?_⟩
  have hf : faceN (fun _ => 1) 0 = 3 := by simp [faceN]
  have hq : quadN (fun _ => 1) 0 = 4 := by simp [quadN]
  rcases hz with rfl | rfl | rfl
  · exact h _ I (by simp) (Or.inl (by simp))
  · refine h _ _ (by simp) (Or.inr (Or.inl ⟨by simp; norm_num, 0, ?_⟩))
    rw [hf]
    simp
    norm_num
  · refine h _ _ (by simp) (Or.inr (Or.inr ⟨0, ?_⟩))
    rw [hq]
    simp
    norm_num

/-- **Junk value**: Lean's `log 0 = 0` gives `Re(0 log 0) = 0`, the limit of `u log u` at `0`. -/
theorem re_xlog_zero : (xlog 0).re = 0 := by
  simp [xlog]

end Lightlike.Asymptotics
