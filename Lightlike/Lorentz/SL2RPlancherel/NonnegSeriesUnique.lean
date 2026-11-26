module

public import Mathlib

/-!
# Uniqueness of the coefficients of a power series with non-negative coefficients

If `Σ a_k x^k = Σ b_k x^k` for all `x ∈ [0, 1)` with `a_k, b_k ≥ 0` and both series summable there, then `a = b`
(`coeff_eq_of_hasSum`). It compares the coefficients of the two sides of the identities
`Σ β_k² N_k x^k = N_0 Σ β_k x^k` obtained from the coherent states of the discrete series.
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **First vanishing coefficient**: a real series `Σ c_k x^k` with `c_k = 0` for `k < m`, absolutely summable at `1/2`
and zero on `(0, 1/2]`, has `c_m = 0`. -/
lemma coeff_zero_of_hasSum_zero {c : ℕ → ℝ} (hc : Summable fun k => |c k| * (1 / 2 : ℝ) ^ k)
    (hz : ∀ x ∈ Ioc (0 : ℝ) (1 / 2), HasSum (fun k => c k * x ^ k) 0) (m : ℕ) (hlow : ∀ k < m, c k = 0) :
    c m = 0 := by
  -- the tail `M = Σ_{k > m} |c k| (1/2)^(k - m - 1)`
  set M : ℝ := ∑' k : ℕ, |c (k + (m + 1))| * (1 / 2 : ℝ) ^ k with hM
  have hsum : Summable fun k : ℕ => |c (k + (m + 1))| * (1 / 2 : ℝ) ^ k := by
    have h1 := (summable_nat_add_iff (m + 1)).2 hc
    have h2 : (fun k : ℕ => |c (k + (m + 1))| * (1 / 2 : ℝ) ^ (k + (m + 1))) =
        fun k => (1 / 2 : ℝ) ^ (m + 1) * (|c (k + (m + 1))| * (1 / 2 : ℝ) ^ k) := by
      funext k; rw [pow_add]; ring
    rw [h2] at h1
    exact (summable_mul_left_iff (by positivity)).1 h1
  have hMnn : 0 ≤ M := tsum_nonneg fun k => by positivity
  -- for every `x ∈ (0, 1/2]`, `|c m| ≤ x * M`
  have key : ∀ x ∈ Ioc (0 : ℝ) (1 / 2), |c m| ≤ x * M := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h0 := hz x hx
    -- split the sum at `m`
    have hsplit : ∑' k, c k * x ^ k = 0 := h0.tsum_eq
    have hsumx : Summable fun k => c k * x ^ k := h0.summable
    have hfin : ∑' k, c k * x ^ k = ∑ k ∈ Finset.range (m + 1), c k * x ^ k +
        ∑' k : ℕ, c (k + (m + 1)) * x ^ (k + (m + 1)) := (hsumx.sum_add_tsum_nat_add (m + 1)).symm
    have hlowsum : ∑ k ∈ Finset.range (m + 1), c k * x ^ k = c m * x ^ m := by
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun k hk => by rw [hlow k (Finset.mem_range.1 hk), zero_mul]),
        zero_add]
    have htail : |∑' k : ℕ, c (k + (m + 1)) * x ^ (k + (m + 1))| ≤ x ^ (m + 1) * M := by
      have hb : ∀ k : ℕ, |c (k + (m + 1)) * x ^ (k + (m + 1))| ≤
          x ^ (m + 1) * (|c (k + (m + 1))| * (1 / 2 : ℝ) ^ k) := by
        intro k
        rw [abs_mul, abs_of_pos (pow_pos hx0 _), pow_add]
        have : x ^ k ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hx0.le hx.2 k
        calc |c (k + (m + 1))| * (x ^ k * x ^ (m + 1)) = x ^ (m + 1) * (|c (k + (m + 1))| * x ^ k) := by ring
          _ ≤ x ^ (m + 1) * (|c (k + (m + 1))| * (1 / 2 : ℝ) ^ k) := by gcongr
      have hsb : Summable fun k : ℕ => x ^ (m + 1) * (|c (k + (m + 1))| * (1 / 2 : ℝ) ^ k) := hsum.mul_left _
      have hH := tsum_of_norm_bounded (f := fun k : ℕ => c (k + (m + 1)) * x ^ (k + (m + 1))) hsb.hasSum
        (fun k => by simpa only [Real.norm_eq_abs] using hb k)
      rw [tsum_mul_left] at hH
      simpa only [Real.norm_eq_abs] using hH
    have : c m * x ^ m = -∑' k : ℕ, c (k + (m + 1)) * x ^ (k + (m + 1)) := by
      linarith [hsplit, hfin, hlowsum]
    have hxm : 0 < x ^ m := pow_pos hx0 m
    have : |c m| * x ^ m ≤ x ^ (m + 1) * M := by
      rw [← abs_of_pos hxm, ← abs_mul, this, abs_neg]; exact htail
    rw [pow_succ] at this
    nlinarith [this, hxm]
  -- let `x → 0`
  by_contra hne
  have hpos : 0 < |c m| := abs_pos.2 hne
  set x : ℝ := min (1 / 2) (|c m| / (2 * (M + 1))) with hx
  have hMp : 0 < M + 1 := by linarith
  have hx0 : 0 < x := lt_min (by norm_num) (div_pos hpos (by linarith))
  have hxle : x ≤ 1 / 2 := min_le_left _ _
  have h1 := key x ⟨hx0, hxle⟩
  have h2 : x ≤ |c m| / (2 * (M + 1)) := min_le_right _ _
  have h3 : x * M ≤ |c m| / 2 := by
    calc x * M ≤ x * (M + 1) := by nlinarith
      _ ≤ |c m| / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = |c m| / 2 := by field_simp
  linarith

/-- **Uniqueness of non-negative power series coefficients**: two non-negative series with the same sum on `[0, 1)`
have the same coefficients. -/
theorem coeff_eq_of_hasSum {a b : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) {S : ℝ → ℝ}
    (h1 : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun k => a k * x ^ k) (S x))
    (h2 : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun k => b k * x ^ k) (S x)) : a = b := by
  have hhalf : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set c : ℕ → ℝ := fun k => a k - b k with hc
  have hsum : Summable fun k => |c k| * (1 / 2 : ℝ) ^ k := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((h1 _ hhalf).summable.add (h2 _ hhalf).summable)
    have : |c k| ≤ a k + b k := by
      rw [hc]; simp only; rw [abs_le]; constructor <;> linarith [ha k, hb k]
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    have := mul_le_mul_of_nonneg_right this hp
    linarith
  have hz : ∀ x ∈ Ioc (0 : ℝ) (1 / 2), HasSum (fun k => c k * x ^ k) 0 := by
    intro x hx
    have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, by linarith [hx.2]⟩
    have := (h1 x hx').sub (h2 x hx')
    simpa [hc, sub_mul] using this
  have key : ∀ m, c m = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact coeff_zero_of_hasSum_zero hsum hz m (fun k hk => ih k hk)
  funext m
  have := key m
  simp only [hc] at this
  linarith

end Lightlike.Lorentz.SL2RPlancherel
