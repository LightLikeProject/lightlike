module

public import Lightlike.SU2.OneParameter

/-!
# The Lie product formula

Stage B of group-level completeness (`Completeness.lean`). In a complete normed `ℝ`-algebra with
`‖1‖ = 1`:

  `(exp(X/n) · exp(Y/n))ⁿ → exp(X + Y)`  (`lie_product`).

Ingredients, none of them in Mathlib:
* `norm_exp_le'`: `‖exp x‖ ≤ e^{‖x‖}`;
* `norm_exp_sub_one_sub_le`: `‖exp x − 1 − x‖ ≤ ‖x‖²` for `‖x‖ ≤ 1`.

Both compare the exponential series with the real one.

Then:
* `norm_exp_mul_exp_sub_exp_le`: `‖exp a exp b − exp(a + b)‖ ≤ 7 (‖a‖ + ‖b‖)²` near `0`;
* `norm_pow_sub_pow_le`: the telescoping bound `‖Sⁿ − Tⁿ‖ ≤ n Mⁿ ‖S − T‖`.

Together these give an error `≤ 7 s² eˢ / n`, with `s = ‖X‖ + ‖Y‖`.

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 2 (the matrix exponential and the Lie product formula).
-/

@[expose] public section

open Filter Topology

namespace Lightlike.SU2

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
  [NormOneClass 𝔸]

omit [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
lemma norm_expTerm_le (x : 𝔸) (n : ℕ) :
    ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ ≤ ((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n := by
  rw [norm_smul, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)

lemma hasSum_real_exp (t : ℝ) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • t ^ n) (Real.exp t) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) t

omit [NormedAlgebra ℚ 𝔸] in
/-- `‖exp x‖ ≤ e^{‖x‖}`. -/
lemma norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [← (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).tsum_eq]
  exact tsum_of_norm_bounded (hasSum_real_exp ‖x‖) (norm_expTerm_le x)

omit [NormedAlgebra ℚ 𝔸] in
/-- `‖exp x − 1 − x‖ ≤ e^{‖x‖} − 1 − ‖x‖`. -/
lemma norm_exp_sub_one_sub_le' (x : 𝔸) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have hx : HasSum (fun n => (((n + 2).factorial : ℝ)⁻¹) • x ^ (n + 2))
      (NormedSpace.exp x - (1 + x)) := by
    have := (hasSum_nat_add_iff' 2).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
    convert this using 2
    simp [Finset.sum_range_succ]
  have ht : HasSum (fun n => (((n + 2).factorial : ℝ)⁻¹) • ‖x‖ ^ (n + 2))
      (Real.exp ‖x‖ - (1 + ‖x‖)) := by
    have := (hasSum_nat_add_iff' 2).mpr (hasSum_real_exp ‖x‖)
    convert this using 2
    simp [Finset.sum_range_succ]
  rw [show NormedSpace.exp x - 1 - x = NormedSpace.exp x - (1 + x) by abel, ← hx.tsum_eq,
    show Real.exp ‖x‖ - 1 - ‖x‖ = Real.exp ‖x‖ - (1 + ‖x‖) by ring]
  exact tsum_of_norm_bounded ht fun n => norm_expTerm_le x (n + 2)

omit [NormedAlgebra ℚ 𝔸] in
/-- `‖exp x − 1 − x‖ ≤ ‖x‖²` for `‖x‖ ≤ 1`. -/
lemma norm_exp_sub_one_sub_le {x : 𝔸} (hx : ‖x‖ ≤ 1) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 := by
  refine (norm_exp_sub_one_sub_le' x).trans ?_
  have := Real.abs_exp_sub_one_sub_id_le (x := ‖x‖) (by rwa [abs_of_nonneg (norm_nonneg x)])
  exact (le_abs_self _).trans this

omit [NormedAlgebra ℚ 𝔸] in
/-- `‖exp a exp b − exp(a + b)‖ ≤ 7 (‖a‖ + ‖b‖)²` when `‖a‖ + ‖b‖ ≤ 1`. -/
lemma norm_exp_mul_exp_sub_exp_le {a b : 𝔸} (hs : ‖a‖ + ‖b‖ ≤ 1) :
    ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ ≤ 7 * (‖a‖ + ‖b‖) ^ 2 := by
  set Ra := NormedSpace.exp a - 1 - a with hRa
  set Rb := NormedSpace.exp b - 1 - b with hRb
  set Rab := NormedSpace.exp (a + b) - 1 - (a + b) with hRab
  have hid : NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b) =
      Rb + a * b + a * Rb + Ra + Ra * b + Ra * Rb - Rab := by
    rw [hRa, hRb, hRab]; noncomm_ring
  have ha : ‖a‖ ≤ 1 := by linarith [norm_nonneg b]
  have hb : ‖b‖ ≤ 1 := by linarith [norm_nonneg a]
  have hab : ‖a + b‖ ≤ 1 := (norm_add_le a b).trans hs
  have hA := norm_exp_sub_one_sub_le ha
  have hB := norm_exp_sub_one_sub_le hb
  have hAB := norm_exp_sub_one_sub_le hab
  have hAB' : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  rw [hid]
  have tri : ‖Rb + a * b + a * Rb + Ra + Ra * b + Ra * Rb - Rab‖ ≤
      ‖Rb‖ + ‖a‖ * ‖b‖ + ‖a‖ * ‖Rb‖ + ‖Ra‖ + ‖Ra‖ * ‖b‖ + ‖Ra‖ * ‖Rb‖ + ‖Rab‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_mul_le _ _))
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
  refine tri.trans ?_
  set t := ‖a‖ + ‖b‖ with ht
  have n1 := norm_nonneg a
  have n2 := norm_nonneg b
  have n3 := norm_nonneg Ra
  have n4 := norm_nonneg Rb
  have hat : ‖a‖ ≤ t := by linarith
  have hbt : ‖b‖ ≤ t := by linarith
  have ht1 : t ^ 2 ≤ 1 := by nlinarith
  have ea : ‖a‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ n1 hat 2
  have eb : ‖b‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ n2 hbt 2
  have e1 : ‖Rb‖ ≤ t ^ 2 := hB.trans eb
  have e4 : ‖Ra‖ ≤ t ^ 2 := hA.trans ea
  have e7 : ‖Rab‖ ≤ t ^ 2 := hAB.trans hAB'
  have e2 : ‖a‖ * ‖b‖ ≤ t ^ 2 := by nlinarith
  have e3 : ‖a‖ * ‖Rb‖ ≤ t ^ 2 := by nlinarith
  have e5 : ‖Ra‖ * ‖b‖ ≤ t ^ 2 := by nlinarith
  have e6 : ‖Ra‖ * ‖Rb‖ ≤ t ^ 2 := by nlinarith
  linarith

omit [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] in
/-- Telescoping: `‖Sⁿ − Tⁿ‖ ≤ n Mⁿ ‖S − T‖` for `‖S‖, ‖T‖ ≤ M`, `1 ≤ M`. -/
lemma norm_pow_sub_pow_le {S T : 𝔸} {M : ℝ} (hM : 1 ≤ M) (hS : ‖S‖ ≤ M) (hT : ‖T‖ ≤ M)
    (n : ℕ) : ‖S ^ n - T ^ n‖ ≤ n * M ^ n * ‖S - T‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : S ^ (n + 1) - T ^ (n + 1) = S * (S ^ n - T ^ n) + (S - T) * T ^ n := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have hTn : ‖T ^ n‖ ≤ M ^ n :=
      (norm_pow_le T n).trans (pow_le_pow_left₀ (norm_nonneg T) hT n)
    have hM0 : 0 ≤ M := by linarith
    have hMn : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM (Nat.le_succ n)
    rw [hid]
    calc ‖S * (S ^ n - T ^ n) + (S - T) * T ^ n‖
        ≤ ‖S‖ * ‖S ^ n - T ^ n‖ + ‖S - T‖ * ‖T ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (n * M ^ n * ‖S - T‖) + ‖S - T‖ * M ^ (n + 1) := by
          gcongr
          exact hTn.trans hMn
      _ = (n + 1 : ℕ) * M ^ (n + 1) * ‖S - T‖ := by push_cast; ring

/-- **The Lie product formula**: `(exp(X/n) exp(Y/n))ⁿ → exp(X + Y)`. -/
theorem lie_product (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((n : ℝ)⁻¹ • X) * NormedSpace.exp ((n : ℝ)⁻¹ • Y)) ^ n)
      atTop (𝓝 (NormedSpace.exp (X + Y))) := by
  set s := ‖X‖ + ‖Y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (7 * s ^ 2 * Real.exp s))
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈s⌉₊] with n hn1 hns
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsn : s ≤ n := (Nat.le_ceil s).trans (by exact_mod_cast hns)
  set a := (n : ℝ)⁻¹ • X
  set b := (n : ℝ)⁻¹ • Y
  have hna : ‖a‖ = ‖X‖ / n := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  have hnb : ‖b‖ = ‖Y‖ / n := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  have habs : ‖a‖ + ‖b‖ = s / n := by rw [hna, hnb, hs]; ring
  have hTn : NormedSpace.exp (a + b) ^ n = NormedSpace.exp (X + Y) := by
    rw [← NormedSpace.exp_nsmul, ← smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      mul_inv_cancel₀ hn.ne', one_smul]
  set M := Real.exp (s / n)
  have hM : 1 ≤ M := Real.one_le_exp (by positivity)
  have hS : ‖NormedSpace.exp a * NormedSpace.exp b‖ ≤ M := by
    refine (norm_mul_le _ _).trans ?_
    rw [show M = Real.exp ‖a‖ * Real.exp ‖b‖ by rw [← Real.exp_add, habs]]
    exact mul_le_mul (norm_exp_le' a) (norm_exp_le' b) (norm_nonneg _) (Real.exp_pos _).le
  have hT : ‖NormedSpace.exp (a + b)‖ ≤ M :=
    (norm_exp_le' _).trans (Real.exp_le_exp.mpr ((norm_add_le a b).trans habs.le))
  have hdiff := norm_exp_mul_exp_sub_exp_le (a := a) (b := b)
    (by rw [habs]; exact (div_le_one hn).mpr hsn)
  rw [habs] at hdiff
  have hMn : M ^ n = Real.exp s := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [← hTn]
  calc ‖(NormedSpace.exp a * NormedSpace.exp b) ^ n - NormedSpace.exp (a + b) ^ n‖
      ≤ n * M ^ n * ‖NormedSpace.exp a * NormedSpace.exp b - NormedSpace.exp (a + b)‖ :=
        norm_pow_sub_pow_le hM hS hT n
    _ ≤ n * M ^ n * (7 * (s / n) ^ 2) := by gcongr
    _ = 7 * s ^ 2 * Real.exp s / n := by rw [hMn]; field_simp

end Lightlike.SU2
