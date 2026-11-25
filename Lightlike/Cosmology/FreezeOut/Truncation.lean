module

public import Mathlib
public import Lightlike.Cosmology.FreezeOut.Basic
public import Lightlike.Cosmology.FreezeOut.Bounds
public import Lightlike.Cosmology.FreezeOut.Limit
public import Lightlike.Cosmology.FreezeOut.Existence

/-!
# Existence of a global solution of the freeze-out equation

Row G1-034 (milestone CO7).  The right-hand side is only locally Lipschitz in `y`, so we truncate
`y` to `[0, K]` with `K = Y₀ + λM²/x₀ + 1`.  The truncated field is bounded and globally
Lipschitz, so `exists_global_forward` gives a global solution; the sign and upper bounds show that
it stays in `[0, K)`, hence solves the original equation.

* `trunc K y = max 0 (min K y)`.
* `exists_isSol`: a nonnegative global solution exists (for `e` continuous and bounded by `M`).
-/

@[expose] public section

namespace Lightlike.Cosmology.FreezeOut

open Set Metric
open scoped NNReal

/-- Truncation of `y` to `[0, K]`. -/
def trunc (K y : ℝ) : ℝ := max 0 (min K y)

lemma trunc_lipschitz (K : ℝ) : LipschitzWith 1 (trunc K) :=
  (LipschitzWith.id.const_min K).const_max 0

lemma trunc_nonneg (K y : ℝ) : 0 ≤ trunc K y := le_max_left _ _

lemma trunc_le {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : trunc K y ≤ K :=
  max_le hK (min_le_left _ _)

lemma trunc_of_neg {K y : ℝ} (hy : y < 0) : trunc K y = 0 :=
  max_eq_left ((min_le_right _ _).trans hy.le)

lemma trunc_of_mem {K y : ℝ} (h0 : 0 ≤ y) (hK : y ≤ K) : trunc K y = y := by
  simp [trunc, min_eq_right hK, max_eq_right h0]

/-- **Existence** of a nonnegative global solution of the freeze-out equation, for `Y_eq` continuous
and bounded by `M` on `[x₀, ∞)`. -/
theorem exists_isSol {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ M : ℝ} (hx₀ : 0 < x₀)
    (hY₀ : 0 ≤ Y₀) (he : ContinuousOn e (Ici x₀)) (hM : ∀ x, x₀ ≤ x → |e x| ≤ M) :
    ∃ Y, IsSol lam e x₀ Y₀ Y ∧ ∀ x, x₀ ≤ x → 0 ≤ Y x := by
  set K : ℝ := Y₀ + lam * M ^ 2 / x₀ + 1 with hKdef
  have hc0 : 0 ≤ lam * M ^ 2 / x₀ := by positivity
  have hK1 : 0 ≤ K := by rw [hKdef]; linarith
  set f : ℝ → ℝ → ℝ := fun t y => rhs lam e t (trunc K y) with hf
  have hlip : ∀ t, x₀ ≤ t →
      LipschitzWith ⟨lam / x₀ ^ 2 * (2 * K), by positivity⟩ (f t) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    have h1 := (lip_rhs hlam e hx₀ K hK1 ht).dist_le_mul (trunc K y)
      (by simpa [mem_closedBall, abs_of_nonneg (trunc_nonneg K y)] using trunc_le hK1 y)
      (trunc K z)
      (by simpa [mem_closedBall, abs_of_nonneg (trunc_nonneg K z)] using trunc_le hK1 z)
    have h2 : dist (trunc K y) (trunc K z) ≤ dist y z := by
      simpa using (trunc_lipschitz K).dist_le_mul y z
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg _)
  have hcont : ∀ y, ContinuousOn (fun t => f t y) (Ici x₀) := by
    intro y
    simp only [hf, rhs]
    refine ContinuousOn.mul ?_ (continuousOn_const.sub (he.pow 2))
    refine ContinuousOn.neg (continuousOn_const.div (continuousOn_id.pow 2) fun t ht => ?_)
    have : 0 < t := lt_of_lt_of_le hx₀ ht
    positivity
  have hb : ∀ t, x₀ ≤ t → ∀ y, ‖f t y‖ ≤
      (⟨lam / x₀ ^ 2 * (K ^ 2 + M ^ 2), by positivity⟩ : ℝ≥0) := by
    intro t ht y
    have ht0 : 0 < t := lt_of_lt_of_le hx₀ ht
    have h1 : lam / t ^ 2 ≤ lam / x₀ ^ 2 :=
      div_le_div_of_nonneg_left hlam (by positivity) (pow_le_pow_left₀ hx₀.le ht 2)
    have hc1 : 0 ≤ trunc K y := trunc_nonneg K y
    have hc2 : trunc K y ≤ K := trunc_le hK1 y
    have hc3 : trunc K y ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hc1 hc2 2
    have he2 : e t ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [abs_le.1 (hM t ht)])
      (abs_le.1 (hM t ht)).2
    have hsq : |trunc K y ^ 2 - e t ^ 2| ≤ K ^ 2 + M ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (e t), sq_nonneg (trunc K y)]
    simp only [hf, rhs, Real.norm_eq_abs]
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ lam / t ^ 2)]
    exact mul_le_mul h1 hsq (abs_nonneg _) (by positivity)
  obtain ⟨Y, hY0, hY⟩ := exists_global_forward hlip hcont hb (y₀ := Y₀)
  have hcY : ContinuousOn Y (Ici x₀) := fun t ht => (hY t ht).continuousWithinAt
  -- nonnegativity
  have hnn : ∀ x, x₀ ≤ x → 0 ≤ Y x := by
    refine nonneg_of_deriv hcY (by rw [hY0]; exact hY₀) hY fun x hx hneg => ?_
    simp only [hf, rhs, trunc_of_neg hneg]
    have : 0 ≤ lam / x ^ 2 := by positivity
    nlinarith [sq_nonneg (e x)]
  -- upper bound
  have hanti : AntitoneOn (fun x => Y x + (lam * M ^ 2) / x) (Ici x₀) := by
    refine antitoneOn_add_div hx₀ hcY hY fun x hx => ?_
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have he2 : e x ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [abs_le.1 (hM x hx)])
      (abs_le.1 (hM x hx)).2
    simp only [hf, rhs]
    have h1 : -(lam / x ^ 2) * (trunc K (Y x) ^ 2 - e x ^ 2)
        = lam / x ^ 2 * (e x ^ 2 - trunc K (Y x) ^ 2) := by ring
    rw [h1]
    calc lam / x ^ 2 * (e x ^ 2 - trunc K (Y x) ^ 2) ≤ lam / x ^ 2 * M ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (trunc K (Y x))]) (by positivity)
      _ = lam * M ^ 2 / x ^ 2 := by ring
  have hup : ∀ x, x₀ ≤ x → Y x ≤ Y₀ + lam * M ^ 2 / x₀ := by
    intro x hx
    have hA := hanti (show x₀ ∈ Ici x₀ from le_rfl) (show x ∈ Ici x₀ from hx) hx
    simp only [hY0] at hA
    have : 0 ≤ lam * M ^ 2 / x := by
      have : 0 < x := lt_of_lt_of_le hx₀ hx
      positivity
    linarith
  refine ⟨Y, ⟨hY0, fun x hx => ?_⟩, hnn⟩
  have hx1 : Y x ≤ K := by have := hup x hx; rw [hKdef]; linarith
  have := hY x hx
  simpa only [hf, trunc_of_mem (hnn x hx) hx1] using this

end Lightlike.Cosmology.FreezeOut

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.exists_isSol := _root_.Lightlike.Cosmology.FreezeOut.exists_isSol
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc := _root_.Lightlike.Cosmology.FreezeOut.trunc
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc_le := _root_.Lightlike.Cosmology.FreezeOut.trunc_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc_lipschitz := _root_.Lightlike.Cosmology.FreezeOut.trunc_lipschitz
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc_nonneg := _root_.Lightlike.Cosmology.FreezeOut.trunc_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc_of_mem := _root_.Lightlike.Cosmology.FreezeOut.trunc_of_mem
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.trunc_of_neg := _root_.Lightlike.Cosmology.FreezeOut.trunc_of_neg
