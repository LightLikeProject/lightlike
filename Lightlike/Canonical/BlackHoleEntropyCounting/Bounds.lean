import Lightlike.Canonical.BlackHoleEntropyCounting.Num

/-!
# Square-root and `exp(-π γ)` bounds (row G2-016, milestone CA6)

* `tLab m`, `sLab m`: explicit upper / lower bounds for `√(m² - 1)` (`m ≥ 2`), from the series
  `m √(1 - v)`, `v = 1/m²` (`areaLabel_le_tLab`, `sLab_le_areaLabel`);
* `qLo_le_exp`, `exp_le_qHi`: rational bounds for `exp(-π γ)` at `γ = 0.2374` and `γ = 0.2376`.
-/

open Real

namespace Lightlike.Rows.G2_016

/-- Truncated series `1 - v/2 - v²/8 - v³/16` of `√(1-v)`. -/
noncomputable def Pp (v : ℝ) : ℝ := 1 - v / 2 - v ^ 2 / 8 - v ^ 3 / 16

/-- Upper bound `m (1 - v/2 - v²/8 - v³/16)`, `v = 1/m²`, for `√(m²-1)`. -/
noncomputable def tLab (m : ℝ) : ℝ := m * Pp (1 / m ^ 2)

/-- Lower bound `m (1 - v/2 - v²/8 - v³/16 - v⁴/16)`, `v = 1/m²`, for `√(m²-1)`. -/
noncomputable def sLab (m : ℝ) : ℝ := m * (Pp (1 / m ^ 2) - (1 / m ^ 2) ^ 4 / 16)

theorem Pp_sq_ge {v : ℝ} (h0 : 0 ≤ v) : 1 - v ≤ Pp v ^ 2 := by
  have : Pp v ^ 2 - (1 - v) = 5 * v ^ 4 / 64 + v ^ 5 / 64 + v ^ 6 / 256 := by
    unfold Pp; ring
  have : 0 ≤ 5 * v ^ 4 / 64 + v ^ 5 / 64 + v ^ 6 / 256 := by positivity
  linarith

theorem Pp_sq_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 4) :
    (Pp v - v ^ 4 / 16) ^ 2 ≤ 1 - v := by
  have hv2 : v ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hv3 : v ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ h0 h1 3
  have hv4 : v ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ h0 h1 4
  have key : 0 ≤ -(5 / 64) - v / 64 - v ^ 2 / 256 + Pp v / 8 - v ^ 4 / 256 := by
    unfold Pp; norm_num at hv2 hv3 hv4 ⊢; linarith
  have : 1 - v - (Pp v - v ^ 4 / 16) ^ 2 =
      v ^ 4 * (-(5 / 64) - v / 64 - v ^ 2 / 256 + Pp v / 8 - v ^ 4 / 256) := by
    unfold Pp; ring
  have : 0 ≤ v ^ 4 * (-(5 / 64) - v / 64 - v ^ 2 / 256 + Pp v / 8 - v ^ 4 / 256) :=
    mul_nonneg (by positivity) key
  linarith

theorem Pp_le_one {v : ℝ} (h0 : 0 ≤ v) : Pp v ≤ 1 := by
  unfold Pp; nlinarith [sq_nonneg v, pow_nonneg h0 3]

theorem areaLabel_eq (n : ℕ) : ((n : ℝ) + 1) * ((n : ℝ) + 3) = ((n : ℝ) + 2) ^ 2 - 1 := by ring

theorem areaLabel_le_tLab (n : ℕ) : areaLabel n ≤ tLab ((n : ℝ) + 2) := by
  have hm : (2 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hm0 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hv0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  have hv1 : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hP : 0 ≤ Pp (1 / ((n : ℝ) + 2) ^ 2) := by
    unfold Pp
    have := pow_le_pow_left₀ hv0 hv1 2
    have := pow_le_pow_left₀ hv0 hv1 3
    norm_num at *; linarith
  unfold areaLabel tLab
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg hm0.le hP, ?_⟩
  have h := Pp_sq_ge hv0
  rw [areaLabel_eq, mul_pow]
  have e : ((n : ℝ) + 2) ^ 2 * (1 - 1 / ((n : ℝ) + 2) ^ 2) = ((n : ℝ) + 2) ^ 2 - 1 := by
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem sLab_le_areaLabel (n : ℕ) : sLab ((n : ℝ) + 2) ≤ areaLabel n := by
  have hm : (2 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hm0 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hv0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  have hv1 : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  unfold areaLabel sLab
  apply Real.le_sqrt_of_sq_le
  have h := Pp_sq_le hv0 hv1
  rw [areaLabel_eq, mul_pow]
  have e : ((n : ℝ) + 2) ^ 2 * (1 - 1 / ((n : ℝ) + 2) ^ 2) = ((n : ℝ) + 2) ^ 2 - 1 := by
    field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem sLab_le_self (n : ℕ) : sLab ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
  have hm0 : (0 : ℝ) < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hv0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  unfold sLab
  have := Pp_le_one hv0
  have : 0 ≤ (1 / ((n : ℝ) + 2) ^ 2) ^ 4 / 16 := by positivity
  nlinarith

/-- Lower rational bound for `exp(-π · 0.2374)`. -/
theorem qLo_le_exp : (47434 / 100000 : ℝ) ≤ Real.exp (-(π * (2374 / 10000))) := by
  have hx0 : 0 ≤ (3141593 / 1000000 : ℝ) * (2374 / 10000) := by norm_num
  have hx1 : (3141593 / 1000000 : ℝ) * (2374 / 10000) ≤ 1 := by norm_num
  have hb := Real.exp_bound' hx0 hx1 (n := 12) (by norm_num)
  have hpi : π * (2374 / 10000) ≤ (3141593 / 1000000 : ℝ) * (2374 / 10000) := by
    have := Real.pi_lt_d6
    nlinarith
  have h1 : Real.exp (π * (2374 / 10000)) ≤ Real.exp ((3141593 / 1000000 : ℝ) * (2374 / 10000)) :=
    Real.exp_le_exp.2 hpi
  have h2 : Real.exp ((3141593 / 1000000 : ℝ) * (2374 / 10000)) * (47434 / 100000) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_right hb (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h3 : Real.exp (π * (2374 / 10000)) * (47434 / 100000) ≤ 1 :=
    (mul_le_mul_of_nonneg_right h1 (by norm_num)).trans h2
  have h4 : Real.exp (π * (2374 / 10000)) * Real.exp (-(π * (2374 / 10000))) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (π * (2374 / 10000))
  refine le_of_mul_le_mul_left ?_ hpos
  rw [h4]
  linarith

theorem tLab_le_self (n : ℕ) : tLab ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
  have hm0 : (0 : ℝ) < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hv0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  unfold tLab
  have := Pp_le_one hv0
  nlinarith

/-- The `n`-th lower term at `γ = 0.2374`. -/
noncomputable def lowTerm (n : ℕ) : ℝ :=
  2 * (47434 / 100000 : ℝ) ^ (n + 2) *
    polyLo ((3141592 / 1000000 : ℝ) * (2374 / 10000) * (((n : ℝ) + 2) - tLab ((n : ℝ) + 2)))

theorem lowTerm_le (n : ℕ) :
    lowTerm n ≤ 2 * Real.exp (-(π * (2374 / 10000 : ℝ) * areaLabel n)) := by
  have hd := tLab_le_self n
  have hpi : (3141592 / 1000000 : ℝ) ≤ π := by
    have := Real.pi_gt_d6
    norm_num at this ⊢
    linarith
  have h := term_low (γ := 2374 / 10000) (q := 47434 / 100000)
    (y1 := (3141592 / 1000000 : ℝ) * (2374 / 10000) * (((n : ℝ) + 2) - tLab ((n : ℝ) + 2)))
    (t := tLab ((n : ℝ) + 2)) (by norm_num) (by norm_num) qLo_le_exp n (areaLabel_le_tLab n)
    (by have : 0 ≤ ((n : ℝ) + 2) - tLab ((n : ℝ) + 2) := by linarith
        positivity)
    (by
      have : 0 ≤ ((n : ℝ) + 2) - tLab ((n : ℝ) + 2) := by linarith
      have h2 : (3141592 / 1000000 : ℝ) * (2374 / 10000) ≤ π * (2374 / 10000) := by
        nlinarith
      exact mul_le_mul_of_nonneg_right h2 this)
  unfold lowTerm
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **Lower bound at `γ = 0.2374`.** `∑ₙ 2 exp(-π γ √((n+1)(n+3))) > 1` for `γ = 0.2374`. -/
theorem countSum_two_gt : 1 < countSum (fun _ => (2 : ℝ)) (2374 / 10000) := by
  have hs := summable_term (w := fun _ => (2 : ℝ)) (fun _ => by norm_num)
    (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith) (γ := 2374 / 10000) (by norm_num)
  have h1 := hs.sum_le_tsum (Finset.range 12) (fun n _ => by positivity)
  have h2 : ∑ n ∈ Finset.range 12, lowTerm n ≤
      ∑ n ∈ Finset.range 12, 2 * Real.exp (-(π * (2374 / 10000 : ℝ) * areaLabel n)) :=
    Finset.sum_le_sum (fun n _ => lowTerm_le n)
  have h3 : 1 < ∑ n ∈ Finset.range 12, lowTerm n := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, lowTerm, tLab, Pp, polyLo]
    norm_num
  unfold countSum
  linarith

end Lightlike.Rows.G2_016
