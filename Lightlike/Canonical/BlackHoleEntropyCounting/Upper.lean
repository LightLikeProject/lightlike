import Lightlike.Canonical.BlackHoleEntropyCounting.Bounds

/-!
# Upper bound for the counting sum at `γ = 0.2376` (row G2-016, milestone CA6)

`countSum_two_lt : countSum (fun _ => 2) (2376/10000) < 1`: ten head terms are bounded by
`term_up` with the lower square-root bound `sLab`, the tail `n ≥ 10` by a geometric series
(`areaLabel n ≥ m - 1/m`, `m = n + 2`).
-/

open Real

namespace Lightlike.Canonical.BlackHoleEntropyCounting

/-- Upper rational bound for `exp(-π · 0.2376)`. -/
theorem exp_le_qHi : Real.exp (-(π * (2376 / 10000))) ≤ 474055 / 1000000 := by
  have hx0 : 0 ≤ (3141592 / 1000000 : ℝ) * (2376 / 10000) := by norm_num
  have hb := Real.sum_le_exp_of_nonneg hx0 12
  have hpi : (3141592 / 1000000 : ℝ) * (2376 / 10000) ≤ π * (2376 / 10000) := by
    have := Real.pi_gt_d6
    norm_num at this ⊢
    nlinarith
  have h1 : Real.exp ((3141592 / 1000000 : ℝ) * (2376 / 10000)) ≤ Real.exp (π * (2376 / 10000)) :=
    Real.exp_le_exp.2 hpi
  have h2 : 1 ≤ (∑ i ∈ Finset.range 12, ((3141592 / 1000000 : ℝ) * (2376 / 10000)) ^ i /
      (i.factorial : ℝ)) * (474055 / 1000000) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h3 : 1 ≤ Real.exp (π * (2376 / 10000)) * (474055 / 1000000) :=
    h2.trans (mul_le_mul_of_nonneg_right (hb.trans h1) (by norm_num))
  have h4 : Real.exp (π * (2376 / 10000)) * Real.exp (-(π * (2376 / 10000))) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (π * (2376 / 10000))
  refine le_of_mul_le_mul_left ?_ hpos
  rw [h4]
  linarith

/-- `m - sLab m ≤ 1` for `m = n + 2`. -/
theorem self_sub_sLab_le (n : ℕ) : ((n : ℝ) + 2) - sLab ((n : ℝ) + 2) ≤ 1 := by
  have hm : (2 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hm0 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hv0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  have hv1 : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hmv : ((n : ℝ) + 2) * (1 / ((n : ℝ) + 2) ^ 2) ≤ 1 / 2 := by
    have : ((n : ℝ) + 2) * (1 / ((n : ℝ) + 2) ^ 2) = 1 / ((n : ℝ) + 2) := by
      field_simp
    rw [this, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have e : ((n : ℝ) + 2) - sLab ((n : ℝ) + 2) = ((n : ℝ) + 2) *
      (1 / ((n : ℝ) + 2) ^ 2 / 2 + (1 / ((n : ℝ) + 2) ^ 2) ^ 2 / 8 +
        (1 / ((n : ℝ) + 2) ^ 2) ^ 3 / 16 + (1 / ((n : ℝ) + 2) ^ 2) ^ 4 / 16) := by
    unfold sLab Pp; ring
  rw [e]
  generalize 1 / ((n : ℝ) + 2) ^ 2 = v at hv0 hv1 hmv ⊢
  generalize (n : ℝ) + 2 = m at hm hm0 hmv ⊢
  have hin : v / 2 + v ^ 2 / 8 + v ^ 3 / 16 + v ^ 4 / 16 ≤ v := by
    have h2 : v ^ 2 ≤ v / 4 := by nlinarith
    have h3 : v ^ 3 ≤ v / 16 := by nlinarith [sq_nonneg v]
    have h4 : v ^ 4 ≤ v / 64 := by nlinarith [sq_nonneg v, pow_nonneg hv0 3]
    linarith
  have := mul_le_mul_of_nonneg_left hin hm0.le
  linarith

/-- The `n`-th head upper term at `γ = 0.2376`. -/
noncomputable def upTerm (n : ℕ) : ℝ :=
  2 * (474055 / 1000000 : ℝ) ^ (n + 2) *
    polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) * (((n : ℝ) + 2) - sLab ((n : ℝ) + 2)))

theorem upTerm_ge (n : ℕ) :
    2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel n)) ≤ upTerm n := by
  have hd := sLab_le_self n
  have hpi : π ≤ (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6
    norm_num at this ⊢
    linarith
  have h := term_up (γ := 2376 / 10000) (q := 474055 / 1000000)
    (y0 := (3141593 / 1000000 : ℝ) * (2376 / 10000) * (((n : ℝ) + 2) - sLab ((n : ℝ) + 2)))
    (s := sLab ((n : ℝ) + 2)) (by norm_num) exp_le_qHi n (sLab_le_areaLabel n) hd
    (by
      have : 0 ≤ ((n : ℝ) + 2) - sLab ((n : ℝ) + 2) := by linarith
      have h2 : π * (2376 / 10000) ≤ (3141593 / 1000000 : ℝ) * (2376 / 10000) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 this)
    (by
      have h1 := self_sub_sLab_le n
      have h0 : 0 ≤ ((n : ℝ) + 2) - sLab ((n : ℝ) + 2) := by linarith
      have : (3141593 / 1000000 : ℝ) * (2376 / 10000) *
          (((n : ℝ) + 2) - sLab ((n : ℝ) + 2)) ≤ (3141593 / 1000000 : ℝ) * (2376 / 10000) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      norm_num at this ⊢
      linarith)
  have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
  unfold upTerm
  linarith

/-- Tail term bound for `n = i + 10`. -/
theorem tail_term_le (i : ℕ) :
    2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel (i + 10))) ≤
      (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (474055 / 1000000 : ℝ) ^ i := by
  have hpi : π ≤ (3141593 / 1000000 : ℝ) := by
    have := Real.pi_lt_d6
    norm_num at this ⊢
    linarith
  have hm : (12 : ℝ) ≤ ((i + 10 : ℕ) : ℝ) + 2 := by push_cast; have := Nat.cast_nonneg (α := ℝ) i; linarith
  have hm0 : (0 : ℝ) < ((i + 10 : ℕ) : ℝ) + 2 := by linarith
  have hinv : 1 / (((i + 10 : ℕ) : ℝ) + 2) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have h := term_up (γ := 2376 / 10000) (q := 474055 / 1000000)
    (y0 := (3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)
    (s := ((i + 10 : ℕ) : ℝ) + 2 - 1 / (((i + 10 : ℕ) : ℝ) + 2)) (by norm_num) exp_le_qHi (i + 10)
    (areaLabel_ge_sub _) (by have : 0 < 1 / (((i + 10 : ℕ) : ℝ) + 2) := by positivity
                             linarith)
    (by
      have e : ((i + 10 : ℕ) : ℝ) + 2 - (((i + 10 : ℕ) : ℝ) + 2 - 1 / (((i + 10 : ℕ) : ℝ) + 2)) =
          1 / (((i + 10 : ℕ) : ℝ) + 2) := by ring
      rw [e]
      have h1 : π * (2376 / 10000) ≤ (3141593 / 1000000 : ℝ) * (2376 / 10000) := by nlinarith
      calc π * (2376 / 10000) * (1 / (((i + 10 : ℕ) : ℝ) + 2))
          ≤ (3141593 / 1000000 : ℝ) * (2376 / 10000) * (1 / 12) :=
            mul_le_mul h1 hinv (by positivity) (by norm_num)
        _ = _ := by ring)
    (by norm_num)
  have e2 : (i + 10) + 2 = 12 + i := by ring
  rw [e2, pow_add] at h
  calc 2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel (i + 10)))
      ≤ 2 * ((474055 / 1000000 : ℝ) ^ 12 * (474055 / 1000000 : ℝ) ^ i *
          polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- **Upper bound at `γ = 0.2376`.** `∑ₙ 2 exp(-π γ √((n+1)(n+3))) < 1` for `γ = 0.2376`. -/
theorem countSum_two_lt : countSum (fun _ => (2 : ℝ)) (2376 / 10000) < 1 := by
  have hs := summable_term (w := fun _ => (2 : ℝ)) (fun _ => by norm_num)
    (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith) (γ := 2376 / 10000) (by norm_num)
  have hs' : Summable (fun n : ℕ => 2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel n))) := hs
  have hsum := hs'.sum_add_tsum_nat_add 10
  have hgeo : Summable (fun i : ℕ => (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (474055 / 1000000 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have h1 : ∑ n ∈ Finset.range 10, 2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel n)) ≤
      ∑ n ∈ Finset.range 10, upTerm n :=
    Finset.sum_le_sum (fun n _ => upTerm_ge n)
  have h2 : ∑' i : ℕ, 2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel (i + 10))) ≤
      ∑' i : ℕ, (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (474055 / 1000000 : ℝ) ^ i :=
    Summable.tsum_le_tsum tail_term_le ((summable_nat_add_iff 10).2 hs') hgeo
  have h2' : ∑' i : ℕ, (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (474055 / 1000000 : ℝ) ^ i =
      (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (1 - 474055 / 1000000 : ℝ)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have h3 : ∑ n ∈ Finset.range 10, upTerm n +
      (2 * (474055 / 1000000 : ℝ) ^ 12 *
        polyUp ((3141593 / 1000000 : ℝ) * (2376 / 10000) / 12)) * (1 - 474055 / 1000000 : ℝ)⁻¹
      < 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, upTerm, sLab, Pp, polyUp]
    norm_num
  have e : countSum (fun _ => (2 : ℝ)) (2376 / 10000) =
      ∑' n : ℕ, 2 * Real.exp (-(π * (2376 / 10000 : ℝ) * areaLabel n)) := rfl
  rw [e, ← hsum]
  linarith

end Lightlike.Canonical.BlackHoleEntropyCounting

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.countSum_two_lt := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.countSum_two_lt
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.exp_le_qHi := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.exp_le_qHi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.self_sub_sLab_le := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.self_sub_sLab_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.tail_term_le := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.tail_term_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.upTerm := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.upTerm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_016.upTerm_ge := _root_.Lightlike.Canonical.BlackHoleEntropyCounting.upTerm_ge
