import Mathlib
import Lightlike.Asymptotics.FreeBosonGrowth.FreeBoson

/-!
# The free boson spectrum: `∑ p(n) q^n = exp (∑_k -log (1 - q^k))`

With `p(n)` the number of partitions of `n` (`pcount n`) and `0 ≤ q < 1`, the series `∑ p(n) q^n`
converges and equals `exp (∑_{k ≥ 1} -log (1 - q^k))` (`tsum_pcount_mul_pow`), i.e. the Euler product.
The proof compares with the restricted counts of `FreeBoson.lean`: `#(restricted n (· ≤ N)) ≤ p(n)`,
with equality when `n ≤ N`.
No catalogue entry: supporting lemmas.
-/

open PowerSeries Finset Filter Topology

noncomputable section

namespace Lightlike.SP3Row

/-- The number of partitions of `n`, as a real number. -/
def pcount (n : ℕ) : ℝ := (Fintype.card (Nat.Partition n) : ℝ)

lemma pcount_nonneg (n : ℕ) : 0 ≤ pcount n := Nat.cast_nonneg _

lemma card_restricted_le (N n : ℕ) :
    (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) ≤ pcount n := by
  unfold pcount
  exact_mod_cast Finset.card_le_univ _

lemma card_restricted_eq {N n : ℕ} (h : n ≤ N) :
    (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) = pcount n := by
  unfold pcount
  have : Nat.Partition.restricted n (· ≤ N) = Finset.univ := by
    unfold Nat.Partition.restricted
    refine Finset.filter_true_of_mem fun x _ i hi => ?_
    exact (Nat.Partition.le_of_mem_parts hi).trans h
  rw [this]; simp

lemma prod_inv_eq_exp {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∏ i ∈ range N, (1 - q ^ (i + 1))⁻¹ = Real.exp (∑ i ∈ range N, -Real.log (1 - q ^ (i + 1))) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : 0 < 1 - q ^ (i + 1) := by
    have := pow_lt_one₀ hq0 hq1 (show i + 1 ≠ 0 by omega); linarith
  rw [Real.exp_neg, Real.exp_log this]

lemma summable_neglog {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℕ => -Real.log (1 - q ^ (k + 1)) := by
  have hg : Summable fun k : ℕ => q ^ (k + 1) / (1 - q) :=
    (((summable_geometric_of_lt_one hq0 hq1).mul_left q).congr (fun k => by ring)).div_const _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
  · have hx0 : q ^ (k + 1) ≤ q := pow_le_of_le_one hq0 hq1.le (Nat.succ_ne_zero k)
    have hx : 0 < 1 - q ^ (k + 1) := by linarith
    have : Real.log (1 - q ^ (k + 1)) ≤ 0 :=
      Real.log_nonpos hx.le (by have := pow_nonneg hq0 (k + 1); linarith)
    linarith
  · have hx0 : q ^ (k + 1) ≤ q := pow_le_of_le_one hq0 hq1.le (Nat.succ_ne_zero k)
    have hx : 0 < 1 - q ^ (k + 1) := by linarith
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
    rw [Real.log_inv] at h1
    have h2 : (1 - q ^ (k + 1))⁻¹ - 1 = q ^ (k + 1) / (1 - q ^ (k + 1)) := by
      field_simp; ring
    have h3 : q ^ (k + 1) / (1 - q ^ (k + 1)) ≤ q ^ (k + 1) / (1 - q) :=
      div_le_div_of_nonneg_left (pow_nonneg hq0 _) (by linarith) (by linarith)
    linarith

/-- **Euler product for the partition numbers** at real `q ∈ [0,1)`: `∑ p(n) q^n` converges and
equals `exp (∑_{k ≥ 1} -log (1 - q^k))`. -/
theorem tsum_pcount_mul_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n => pcount n * q ^ n) ∧
      ∑' n, pcount n * q ^ n = Real.exp (∑' k : ℕ, -Real.log (1 - q ^ (k + 1))) := by
  set T := ∑' k : ℕ, -Real.log (1 - q ^ (k + 1)) with hT
  have hsT := summable_neglog hq0 hq1
  have hnn : ∀ k : ℕ, 0 ≤ -Real.log (1 - q ^ (k + 1)) := by
    intro k
    have hx0 : q ^ (k + 1) ≤ q := pow_le_of_le_one hq0 hq1.le (Nat.succ_ne_zero k)
    have hx : 0 < 1 - q ^ (k + 1) := by linarith
    have : Real.log (1 - q ^ (k + 1)) ≤ 0 :=
      Real.log_nonpos hx.le (by have := pow_nonneg hq0 (k + 1); linarith)
    linarith
  have hP : ∀ N, ∑' n, (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) * q ^ n =
      Real.exp (∑ i ∈ range N, -Real.log (1 - q ^ (i + 1))) := by
    intro N
    have := (prodGeom_ev hq0 hq1 N).2
    simp_rw [coeff_prodGeom] at this
    rw [this, prod_inv_eq_exp hq0 hq1]
  have hPs : ∀ N, Summable fun n => (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) * q ^ n := by
    intro N
    have := (prodGeom_ev hq0 hq1 N).1
    simp_rw [coeff_prodGeom] at this
    refine this.of_norm.congr fun n => rfl
  have hnnc : ∀ N n, 0 ≤ (#(Nat.Partition.restricted n (· ≤ N)) : ℝ) * q ^ n :=
    fun N n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _)
  have hbound : ∀ M, ∑ n ∈ range M, pcount n * q ^ n ≤ Real.exp T := by
    intro M
    calc ∑ n ∈ range M, pcount n * q ^ n
        = ∑ n ∈ range M, (#(Nat.Partition.restricted n (· ≤ M)) : ℝ) * q ^ n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [card_restricted_eq (Finset.mem_range.1 hn).le]
      _ ≤ ∑' n, (#(Nat.Partition.restricted n (· ≤ M)) : ℝ) * q ^ n :=
          (hPs M).sum_le_tsum _ (fun n _ => hnnc M n)
      _ = Real.exp (∑ i ∈ range M, -Real.log (1 - q ^ (i + 1))) := hP M
      _ ≤ Real.exp T := Real.exp_le_exp.2 (hsT.sum_le_tsum _ (fun k _ => hnn k))
  have hnp : ∀ n, 0 ≤ pcount n * q ^ n := fun n => mul_nonneg (pcount_nonneg n) (pow_nonneg hq0 _)
  have hsum : Summable (fun n => pcount n * q ^ n) :=
    summable_of_sum_range_le hnp hbound
  refine ⟨hsum, le_antisymm ?_ ?_⟩
  · exact Real.tsum_le_of_sum_range_le hnp hbound
  · have hPle : ∀ N, Real.exp (∑ i ∈ range N, -Real.log (1 - q ^ (i + 1))) ≤
        ∑' n, pcount n * q ^ n := by
      intro N
      rw [← hP N]
      exact (hPs N).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (card_restricted_le N n)
        (pow_nonneg hq0 _)) hsum
    have hLpos : 0 < ∑' n, pcount n * q ^ n :=
      lt_of_lt_of_le (Real.exp_pos _) (hPle 0)
    have : T ≤ Real.log (∑' n, pcount n * q ^ n) := by
      refine Real.tsum_le_of_sum_range_le hnn fun N => ?_
      rw [← Real.exp_le_exp, Real.exp_log hLpos]
      exact hPle N
    calc Real.exp T ≤ Real.exp (Real.log (∑' n, pcount n * q ^ n)) := Real.exp_le_exp.2 this
      _ = _ := Real.exp_log hLpos

end Lightlike.SP3Row
