import Lightlike.Asymptotics.Tauberian.Crossing
import Mathlib.Data.Nat.Choose.Central

/-!
# An upper bound for the crossing density

`crossingDensity a x ≤ C x^{-3/4} e^{2 √(a x)}` for `x ≥ 1` (MZ (2.6), upper side, without the exact
constant): from the central binomial bound `(n+1) C(2n, n)² ≤ 16ⁿ` and Cauchy–Schwarz for the
exponential series.
-/

open Nat

noncomputable section

namespace Lightlike.Tauberian

/-- `(n + 1) · centralBinom(n)² ≤ 16ⁿ`. -/
lemma succ_mul_centralBinom_sq_le (n : ℕ) :
    ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast h
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hc : ((n + 1).centralBinom : ℝ) = 2 * (2 * n + 1) * (n.centralBinom : ℝ) / ((n : ℝ) + 1) := by
      field_simp; linarith
    rw [hc]
    push_cast
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have key : ((n : ℝ) + 1 + 1) * (2 * (2 * n + 1) * (n.centralBinom : ℝ) / ((n : ℝ) + 1)) ^ 2 =
        4 * (2 * n + 1) ^ 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * (n.centralBinom : ℝ) ^ 2 := by
      field_simp; ring
    rw [key, pow_succ]
    have h2 : 4 * (2 * (n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 ≤ 16 * ((n : ℝ) + 1) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (n : ℝ)]
    calc 4 * (2 * (n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * (n.centralBinom : ℝ) ^ 2
        ≤ 16 * ((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 16 * (((n : ℝ) + 1) * (n.centralBinom : ℝ) ^ 2) := by ring
      _ ≤ 16 * 16 ^ n := by linarith
      _ = 16 ^ n * 16 := by ring

lemma hasSum_exp_div {z : ℝ} : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
  have := NormedSpace.expSeries_div_hasSum_exp z
  rwa [← Real.exp_eq_exp_ℝ] at this

lemma hasSum_exp_div_succ {z : ℝ} (hz : 0 < z) :
    HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ) / ((n : ℝ) + 1)) ((Real.exp z - 1) / z) := by
  have h := hasSum_exp_div (z := z)
  rw [← hasSum_nat_add_iff' 1] at h
  have h2 := h.div_const z
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h2
  convert h2 using 1
  · ext n
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp

/-- `∑ zⁿ/n! (n+1)^{-1/2} ≤ eᶻ z^{-1/2}`. -/
lemma tsum_exp_div_inv_sqrt_le {z : ℝ} (hz : 0 < z) :
    ∑' n : ℕ, z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤ Real.exp z / Real.sqrt z := by
  have hw := hasSum_exp_div (z := z)
  have hw1 := hasSum_exp_div_succ hz
  set lam : ℝ := 1 / Real.sqrt z with hlam
  have hlpos : 0 < lam := by positivity
  have hpt : ∀ n : ℕ, z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤
      (lam / 2) * (z ^ n / (n.factorial : ℝ)) + (1 / (2 * lam)) * (z ^ n / (n.factorial : ℝ) / ((n : ℝ) + 1)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hr := Real.sqrt_pos.2 hn
    have hw0 : 0 ≤ z ^ n / (n.factorial : ℝ) := by positivity
    have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hn.le
    set r := Real.sqrt ((n : ℝ) + 1)
    set w := z ^ n / (n.factorial : ℝ)
    rw [← hsq]
    have : w / r ≤ (lam / 2) * w + (1 / (2 * lam)) * (w / r ^ 2) := by
      have h3 : 0 ≤ w * (lam * r - 1) ^ 2 / (2 * lam * r ^ 2) := by positivity
      have : w * (lam * r - 1) ^ 2 / (2 * lam * r ^ 2) =
          (lam / 2) * w + (1 / (2 * lam)) * (w / r ^ 2) - w / r := by
        field_simp; ring
      linarith
    exact this
  have hsumm : Summable fun n : ℕ => (lam / 2) * (z ^ n / (n.factorial : ℝ)) +
      (1 / (2 * lam)) * (z ^ n / (n.factorial : ℝ) / ((n : ℝ) + 1)) :=
    (hw.summable.mul_left _).add (hw1.summable.mul_left _)
  have hnn : ∀ n : ℕ, 0 ≤ z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1) := fun n => by positivity
  have hsm : Summable fun n : ℕ => z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1) :=
    Summable.of_nonneg_of_le hnn hpt hsumm
  calc ∑' n : ℕ, z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1)
      ≤ ∑' n : ℕ, ((lam / 2) * (z ^ n / (n.factorial : ℝ)) +
        (1 / (2 * lam)) * (z ^ n / (n.factorial : ℝ) / ((n : ℝ) + 1))) :=
        Summable.tsum_le_tsum hpt hsm hsumm
    _ = (lam / 2) * Real.exp z + (1 / (2 * lam)) * ((Real.exp z - 1) / z) := by
        rw [(hw.mul_left _).add (hw1.mul_left _) |>.tsum_eq]
    _ ≤ Real.exp z / Real.sqrt z := by
        have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
        have hsq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
        have hE : 1 ≤ Real.exp z := Real.one_le_exp hz.le
        rw [hlam]
        have : (1 / (2 * (1 / Real.sqrt z))) * ((Real.exp z - 1) / z) =
            (Real.sqrt z / 2) * ((Real.exp z - 1) / z) := by field_simp
        rw [this]
        have hzz : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
        have h4 : (Real.sqrt z / 2) * ((Real.exp z - 1) / z) ≤ Real.exp z / (2 * Real.sqrt z) := by
          have e : (Real.sqrt z / 2) * ((Real.exp z - 1) / z) = (Real.exp z - 1) / (2 * Real.sqrt z) := by
            field_simp
            nlinarith [hzz]
          rw [e]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
        have h5 : (1 / Real.sqrt z / 2) * Real.exp z = Real.exp z / (2 * Real.sqrt z) := by
          field_simp
        rw [h5]
        calc Real.exp z / (2 * Real.sqrt z) + (Real.sqrt z / 2) * ((Real.exp z - 1) / z)
            ≤ Real.exp z / (2 * Real.sqrt z) + Real.exp z / (2 * Real.sqrt z) := by linarith
          _ = Real.exp z / Real.sqrt z := by ring

lemma centralBinom_succ_mul_factorials (k : ℕ) :
    ((k + 1).centralBinom : ℝ) * (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) =
      2 * ((2 * k + 1).factorial : ℝ) := by
  have h1 : (k + 1).centralBinom * ((k + 1).factorial * (k + 1).factorial) = (2 * (k + 1)).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 2 * (k + 1)) (k := k + 1) (by omega)
    rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega] at this
    rw [Nat.centralBinom_eq_two_mul_choose, ← mul_assoc]; exact this
  have h2 : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ]
  have h3 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  have h4 : ((k : ℝ) + 1) * (((k + 1).centralBinom : ℝ) * (((k + 1).factorial : ℝ) * (k.factorial : ℝ))) =
      ((k : ℝ) + 1) * (2 * ((2 * k + 1).factorial : ℝ)) := by
    have e1 : (((k + 1).centralBinom * ((k + 1).factorial * (k + 1).factorial) : ℕ) : ℝ) =
        (((2 * k + 2) * (2 * k + 1).factorial : ℕ) : ℝ) := by rw [h1, h2]
    push_cast at e1
    have e2 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by exact_mod_cast h3
    linear_combination e1 - (((k + 1).centralBinom : ℝ) * ((k + 1).factorial : ℝ)) * e2
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hk h4

lemma centralBinom_succ_le (k : ℕ) :
    ((k + 1).centralBinom : ℝ) ≤ 4 ^ (k + 1) / Real.sqrt ((k : ℝ) + 2) := by
  have h := succ_mul_centralBinom_sq_le (k + 1)
  push_cast at h
  have hpos : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  rw [le_div_iff₀ hpos]
  have hsq : Real.sqrt ((k : ℝ) + 2) ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have h16 : (16 : ℝ) ^ (k + 1) = (4 ^ (k + 1)) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h16] at h
  have hc0 : 0 ≤ ((k + 1).centralBinom : ℝ) := Nat.cast_nonneg _
  by_contra hcon
  push Not at hcon
  have : (4 ^ (k + 1) : ℝ) ^ 2 < (((k + 1).centralBinom : ℝ) * Real.sqrt ((k : ℝ) + 2)) ^ 2 := by
    exact pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [mul_pow, hsq] at this
  nlinarith [this, h]

/-- Termwise bound by the odd terms of the exponential series. -/
lemma crossingTerm_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (k : ℕ) :
    crossingTerm a k x ≤ (2 * Real.sqrt 2 * a / (2 * Real.sqrt (a * x))) *
      ((2 * Real.sqrt (a * x)) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) /
        Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1)) := by
  set z := 2 * Real.sqrt (a * x) with hz
  have hzpos : 0 < z := by positivity
  have hz2 : z ^ 2 = 4 * (a * x) := by
    rw [hz, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hH := centralBinom_succ_mul_factorials k
  have hB := centralBinom_succ_le k
  have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) * (k.factorial : ℝ) := by positivity
  have hG : (0 : ℝ) < ((2 * k + 1).factorial : ℝ) := by positivity
  have hk2 : 0 < Real.sqrt ((k : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
  have hn1 : 0 < Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  -- 1 / ((k+1)! k!) = centralBinom / (2 (2k+1)!)
  have hinv : 1 / (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) =
      ((k + 1).centralBinom : ℝ) / (2 * ((2 * k + 1).factorial : ℝ)) := by
    rw [div_eq_div_iff hF.ne' (by positivity)]
    linarith [hH]
  have hsq : Real.sqrt 2 / Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1) ≥ 1 / Real.sqrt ((k : ℝ) + 2) := by
    rw [ge_iff_le, div_le_div_iff₀ hk2 hn1, one_mul, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    push_cast; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hterm : crossingTerm a k x = a * (a * x) ^ k * (1 / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))) := by
    unfold crossingTerm; rw [mul_pow, pow_succ]; field_simp
  rw [hterm, hinv]
  have hax : (a * x) ^ k * 4 ^ k = z ^ (2 * k) := by
    rw [pow_mul, hz2, mul_pow]; ring
  have h1 : a * (a * x) ^ k * (((k + 1).centralBinom : ℝ) / (2 * ((2 * k + 1).factorial : ℝ))) ≤
      a * (a * x) ^ k * ((4 ^ (k + 1) / Real.sqrt ((k : ℝ) + 2)) / (2 * ((2 * k + 1).factorial : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_right hB (by positivity)
  refine h1.trans ?_
  have e : a * (a * x) ^ k * ((4 ^ (k + 1) / Real.sqrt ((k : ℝ) + 2)) / (2 * ((2 * k + 1).factorial : ℝ))) =
      (2 * a / z) * (z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) * (1 / Real.sqrt ((k : ℝ) + 2)) := by
    have : z ^ (2 * k + 1) = z ^ (2 * k) * z := pow_succ _ _
    rw [this, ← hax]
    field_simp
    ring
  rw [e]
  have hnn : 0 ≤ (2 * a / z) * (z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by positivity
  calc (2 * a / z) * (z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) * (1 / Real.sqrt ((k : ℝ) + 2))
      ≤ (2 * a / z) * (z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) *
        (Real.sqrt 2 / Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left hsq hnn
    _ = (2 * Real.sqrt 2 * a / z) * (z ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) /
        Real.sqrt (((2 * k + 1 : ℕ) : ℝ) + 1)) := by ring

/-- **D2 (upper bound).** `crossingDensity a x ≤ (2√2 a / z) · e^z / √z` with `z = 2 √(a x)`,
that is `O(x^{-3/4} e^{2√(a x)})`: the upper side of MZ (2.6). -/
theorem crossingDensity_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    crossingDensity a x ≤ (2 * Real.sqrt 2 * a / (2 * Real.sqrt (a * x))) *
      (Real.exp (2 * Real.sqrt (a * x)) / Real.sqrt (2 * Real.sqrt (a * x))) := by
  set z := 2 * Real.sqrt (a * x) with hz
  have hzpos : 0 < z := by positivity
  set C := 2 * Real.sqrt 2 * a / z with hC
  have hCpos : 0 ≤ C := by positivity
  set sn : ℕ → ℝ := fun n => z ^ n / (n.factorial : ℝ) / Real.sqrt ((n : ℝ) + 1) with hsn
  have hsn0 : ∀ n, 0 ≤ sn n := fun n => by simp only [hsn]; positivity
  have hsum : Summable sn := by
    have hw := hasSum_exp_div (z := z)
    refine Summable.of_nonneg_of_le hsn0 (fun n => ?_) hw.summable
    simp only [hsn]
    have h1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
      exact Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact div_le_self (by positivity) h1
  have hts := tsum_exp_div_inv_sqrt_le hzpos
  unfold crossingDensity
  refine Real.tsum_le_of_sum_range_le (fun k => crossingTerm_nonneg ha k hx.le) (fun N => ?_)
  have h1 : ∑ k ∈ Finset.range N, crossingTerm a k x ≤ ∑ k ∈ Finset.range N, C * sn (2 * k + 1) :=
    Finset.sum_le_sum fun k _ => by simpa [hC, hz, hsn] using crossingTerm_le ha hx k
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have h2 : ∑ k ∈ Finset.range N, sn (2 * k + 1) ≤ ∑' n, sn n := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun p q h => by simpa using h
    rw [← Finset.sum_image (f := sn) (g := fun k : ℕ => 2 * k + 1) (s := Finset.range N)
      (fun p _ q _ h => hinj h)]
    exact hsum.sum_le_tsum _ (fun n _ => hsn0 n)
  calc C * ∑ k ∈ Finset.range N, sn (2 * k + 1) ≤ C * ∑' n, sn n :=
        mul_le_mul_of_nonneg_left h2 hCpos
    _ ≤ C * (Real.exp z / Real.sqrt z) := mul_le_mul_of_nonneg_left hts hCpos

end Lightlike.Tauberian
