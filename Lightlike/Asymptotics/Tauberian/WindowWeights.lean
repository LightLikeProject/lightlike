import Lightlike.Asymptotics.Tauberian.Compare
import Mathlib.Analysis.PSeries
/-!
# Summing the per-window error weights

`sum_Aw_le`: `∑_{j<2n} A_{n-j} ≤ 4 A₀ + 2 n C β² + 4 C (β + 1)`; the only term growing with `n` is
`2 n C β²`, which at `n ≈ Δ/2`, `β² = a/Δ` is the constant `C a`.
-/

open Finset

namespace Lightlike.Tauberian

/-- The tail weight `r s = 1/(s-1)²` for `s ≥ 2`, else `0`. -/
def rInv (s : ℕ) : ℝ := if 2 ≤ s then (((s : ℝ) - 1) ^ 2)⁻¹ else 0

/-- Nonnegativity of `rInv`. -/
lemma rInv_nonneg (s : ℕ) : 0 ≤ rInv s := by unfold rInv; split_ifs <;> positivity

/-- The shifted sum of `rInv` is the sum of `1/i²`. -/
lemma sum_rInv_eq (n : ℕ) : ∑ s ∈ range (n + 1), rInv s = ∑ i ∈ Ioo 0 n, ((i : ℝ) ^ 2)⁻¹ := by
  induction n with
  | zero => simp [rInv]
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have e : Ioo 0 1 = (∅ : Finset ℕ) := by decide
      simp [rInv, e]
    · have e : Ioo 0 (n + 1) = Ioo 0 n ∪ {n} := by
        ext i; simp only [mem_Ioo, mem_union, mem_singleton]; omega
      rw [e, sum_union (by simp)]
      simp only [sum_singleton]
      unfold rInv
      rw [if_pos (by omega)]
      push_cast
      ring_nf

/-- `∑ rInv ≤ 2`. -/
lemma sum_rInv_le (n : ℕ) : ∑ s ∈ range n, rInv s ≤ 2 := by
  calc ∑ s ∈ range n, rInv s ≤ ∑ s ∈ range (n + 1), rInv s :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ n)) fun s _ _ => rInv_nonneg s
    _ = ∑ i ∈ Ioo 0 n, ((i : ℝ) ^ 2)⁻¹ := sum_rInv_eq n
    _ ≤ 2 := by simpa using sum_Ioo_inv_sq_le (α := ℝ) 0 n

/-- Indicator of `s ≤ 1`. -/
def indLe1 (s : ℕ) : ℝ := if s ≤ 1 then 1 else 0

/-- At most two indices have `s ≤ 1`. -/
lemma sum_indLe1 (m : ℕ) : ∑ s ∈ range m, indLe1 s ≤ 2 := by
  have : ∀ m : ℕ, ∑ s ∈ range m, indLe1 s ≤ (min m 2 : ℕ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      by_cases hm : m < 2
      · have : indLe1 m = 1 := by unfold indLe1; rw [if_pos (by omega)]
        rw [this]
        have e : min (m + 1) 2 = m + 1 := by omega
        have e2 : min m 2 = m := by omega
        rw [e2] at ih; rw [e]; push_cast; linarith
      · have : indLe1 m = 0 := by unfold indLe1; rw [if_neg (by omega)]
        rw [this]
        have e : min (m + 1) 2 = min m 2 := by omega
        rw [e]; linarith
  calc ∑ s ∈ range m, indLe1 s ≤ (min m 2 : ℕ) := this m
    _ ≤ 2 := by exact_mod_cast Nat.min_le_right m 2

/-- `Aw` depends on `|t|` only. -/
lemma Aw_eq_natAbs (b β : ℝ) (t : ℤ) : Aw b β t = Aw b β (t.natAbs : ℤ) := by
  unfold Aw
  have h1 : |(t.natAbs : ℤ)| = |t| := by rw [Int.natCast_natAbs, abs_abs]
  have h2 : |((t.natAbs : ℤ) : ℝ)| = |(t : ℝ)| := by
    rw [← Int.cast_abs, Int.natCast_natAbs, abs_abs, Int.cast_abs]
  rw [h1, h2]

/-- Bound of the weight by a constant, the crude indicator and the tail. -/
lemma Aw_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (s : ℕ) :
    Aw b β (s : ℤ) ≤ (1 + Real.exp β) * Real.exp β * indLe1 s + farC b * β ^ 2 +
      farC b * (β + 1) * rInv s := by
  have hN := kapN_pos hb
  have hM := kapM2_nonneg b
  have hC : 0 ≤ farC b := by unfold farC; positivity
  have hA : 0 ≤ (1 + Real.exp β) * Real.exp β := by positivity
  have hr := rInv_nonneg s
  unfold Aw
  by_cases hs : s ≤ 1
  · rw [if_pos (by simpa using hs)]
    have : indLe1 s = 1 := by unfold indLe1; rw [if_pos hs]
    rw [this]
    have : 0 ≤ farC b * β ^ 2 := by positivity
    have : 0 ≤ farC b * (β + 1) * rInv s := by positivity
    linarith
  · rw [if_neg (by simpa using hs)]
    have : indLe1 s = 0 := by unfold indLe1; rw [if_neg hs]
    have hr' : rInv s = (((s : ℝ) - 1) ^ 2)⁻¹ := by unfold rInv; rw [if_pos (by omega)]
    rw [this, hr']
    have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast (by omega : 2 ≤ s)
    have habs : |((s : ℤ) : ℝ)| = s := by simp
    rw [habs]
    have h1 : (1 : ℝ) ≤ (s : ℝ) - 1 := by linarith
    have h3 : 1 / ((s : ℝ) - 1) ^ 3 ≤ 1 / ((s : ℝ) - 1) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have : β / ((s : ℝ) - 1) ^ 2 + 1 / ((s : ℝ) - 1) ^ 3 ≤ (β + 1) * (((s : ℝ) - 1) ^ 2)⁻¹ := by
      have : (β + 1) * (((s : ℝ) - 1) ^ 2)⁻¹ = β / ((s : ℝ) - 1) ^ 2 + 1 / ((s : ℝ) - 1) ^ 2 := by
        field_simp
      rw [this]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hC]

/-- **The sum of the window weights.** -/
lemma sum_Aw_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (n : ℕ) :
    ∑ j ∈ range (2 * n), Aw b β ((n : ℤ) - j) ≤
      4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (farC b * β ^ 2) + 4 * (farC b * (β + 1)) := by
  have hN := kapN_pos hb
  have hM := kapM2_nonneg b
  have hC : 0 ≤ farC b := by unfold farC; positivity
  set A0 : ℝ := (1 + Real.exp β) * Real.exp β with hA0
  have hA : 0 ≤ A0 := by positivity
  set g : ℕ → ℝ := fun s => Aw b β (s : ℤ) with hg
  have hle : ∀ s, g s ≤ A0 * indLe1 s + farC b * β ^ 2 + farC b * (β + 1) * rInv s := fun s =>
    Aw_le hb hβ s
  have hsplit : ∑ j ∈ range (2 * n), Aw b β ((n : ℤ) - j) =
      ∑ j ∈ range n, g (j + 1) + ∑ i ∈ range n, g i := by
    rw [two_mul, sum_range_add]
    congr 1
    · rw [← sum_range_reflect (fun j => g (j + 1)) n]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.1 hj
      rw [Aw_eq_natAbs]
      simp only [hg]
      congr 2
      omega
    · refine sum_congr rfl fun i hi => ?_
      rw [Aw_eq_natAbs]
      simp only [hg]
      congr 2
      omega
  rw [hsplit]
  have e1 : ∑ j ∈ range n, g (j + 1) ≤ 2 * A0 + n * (farC b * β ^ 2) + 2 * (farC b * (β + 1)) := by
    calc ∑ j ∈ range n, g (j + 1) ≤ ∑ j ∈ range n, (A0 * indLe1 (j + 1) + farC b * β ^ 2 +
          farC b * (β + 1) * rInv (j + 1)) := sum_le_sum fun j _ => hle _
      _ = A0 * ∑ j ∈ range n, indLe1 (j + 1) + n * (farC b * β ^ 2) +
          farC b * (β + 1) * ∑ j ∈ range n, rInv (j + 1) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have h1 : ∑ j ∈ range n, indLe1 (j + 1) ≤ 2 := by
          refine le_trans ?_ (sum_indLe1 (n + 1))
          rw [sum_range_succ']
          have : 0 ≤ indLe1 0 := by unfold indLe1; simp
          linarith
        have h2 : ∑ j ∈ range n, rInv (j + 1) ≤ 2 := by
          refine le_trans ?_ (sum_rInv_le (n + 1))
          rw [sum_range_succ']
          have : 0 ≤ rInv 0 := rInv_nonneg 0
          linarith
        have := mul_le_mul_of_nonneg_left h1 hA
        have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ farC b * (β + 1))
        linarith
  have e2 : ∑ i ∈ range n, g i ≤ 2 * A0 + n * (farC b * β ^ 2) + 2 * (farC b * (β + 1)) := by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, (A0 * indLe1 i + farC b * β ^ 2 +
          farC b * (β + 1) * rInv i) := sum_le_sum fun j _ => hle _
      _ = A0 * ∑ i ∈ range n, indLe1 i + n * (farC b * β ^ 2) +
          farC b * (β + 1) * ∑ i ∈ range n, rInv i := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left (sum_indLe1 n) hA
        have := mul_le_mul_of_nonneg_left (sum_rInv_le n) (by positivity : 0 ≤ farC b * (β + 1))
        linarith
  linarith

end Lightlike.Tauberian
