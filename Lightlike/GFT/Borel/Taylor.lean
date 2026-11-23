import Lightlike.GFT.Borel.Local

/-!
# Taylor expansion of `b_0` on the real axis (supports task T-GF7-P4)

Supports `SokalHyp.exists_continuation` (task T-GF7-P4, Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776v2, Appendix B): for `x, s > 0` with `|s - x| < ρ` the local Borel transform at `x` takes the
value `b_0(s)` at `s` (`SokalHyp.borelLocal_real`). The proof differentiates the partial Taylor sums in the base
point (they telescope, by task T-GF7-P1), bounds the derivative by task T-GF7-P2 and applies the mean value
inequality.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

/-- The terms of the local Borel transform are bounded by `(A/ρ) (m+1) (|t-x|/ρ)^m`, with
`A = K (ρ + 1/(2c)) e^{cx}`. -/
lemma SokalHyp.norm_borelLocal_term_le (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x : ℝ} (hx : 0 ≤ x)
    (m : ℕ) (t : ℂ) :
    ‖borelDeriv f a m x c * (t - x) ^ m / (m ! : ℂ)‖ ≤
      K * (ρ + 1 / (2 * c)) * Real.exp (c * x) / ρ * (((m : ℝ) + 1) * (‖t - x‖ / ρ) ^ m) := by
  have hρ := h.ρ_pos
  have hb := h.norm_borelDeriv_le hc m hx
  have hfac : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖borelDeriv f a m x c‖ * ‖t - x‖ ^ m
      ≤ K * (ρ + 1 / (2 * c)) * (m + 1) ! / ρ ^ (m + 1) * Real.exp (c * x) * ‖t - x‖ ^ m :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by
        rw [Nat.factorial_succ, div_pow, pow_succ]
        push_cast
        field_simp

/-- The series defining the local Borel transform converges for `|t - x| < ρ`. -/
lemma SokalHyp.summable_borelLocal (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x : ℝ} (hx : 0 ≤ x)
    {t : ℂ} (ht : ‖t - x‖ < ρ) :
    Summable fun m : ℕ => borelDeriv f a m x c * (t - x) ^ m / (m ! : ℂ) := by
  have hρ := h.ρ_pos
  have hq0 : 0 ≤ ‖t - x‖ / ρ := by positivity
  have hq1 : ‖t - x‖ / ρ < 1 := (div_lt_one hρ).2 ht
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1) * (‖t - x‖ / ρ) ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖t - x‖ / ρ)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
    have h2 := summable_geometric_of_lt_one hq0 hq1
    simpa [add_mul] using h1.add h2
  exact Summable.of_norm_bounded (hs.mul_left (K * (ρ + 1 / (2 * c)) * Real.exp (c * x) / ρ))
    fun m => h.norm_borelLocal_term_le hc hx m t

/-- The partial Taylor sums of `b_0` about the moving point `y`, with step `s - y`, have the telescoped derivative
`b_{n+1}(y) (s - y)^n / n!`. -/
lemma SokalHyp.hasDerivAt_partial (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) (s : ℝ) (n : ℕ) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => ∑ m ∈ range (n + 1), borelDeriv f a m y c * ((s : ℂ) - y) ^ m / (m ! : ℂ))
      (borelDeriv f a (n + 1) y c * ((s : ℂ) - y) ^ n / (n ! : ℂ)) y := by
  have hpow : ∀ m : ℕ, HasDerivAt (fun y : ℝ => ((s : ℂ) - y) ^ m)
      (m * ((s : ℂ) - y) ^ (m - 1) * (-1)) y := fun m => by
    have : HasDerivAt (fun z : ℂ => ((s : ℂ) - z) ^ m) (m * ((s : ℂ) - y) ^ (m - 1) * (-1)) (y : ℂ) :=
      ((hasDerivAt_id (y : ℂ)).const_sub (s : ℂ)).pow m
    exact this.comp_ofReal
  induction n with
  | zero =>
    have := h.hasDerivAt_borelDeriv hc 0 hy
    simpa using this
  | succ n ih =>
    have h1 := (h.hasDerivAt_borelDeriv hc (n + 1) hy).mul (hpow (n + 1))
    have h2 := (ih).add (h1.div_const (((n + 1)! : ℕ) : ℂ))
    simp only [sum_range_succ _ (n + 1)]
    refine h2.congr_deriv ?_
    have hf : ((n + 1)! : ℂ) = (n + 1) * n ! := by
      push_cast [Nat.factorial_succ]; ring
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
    have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hf]
    field_simp
    ring

/-- **Taylor expansion of `b_0` at a positive real point** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2,
Appendix B, proof of Theorem 1): for `x, s > 0` with `|s - x| < ρ`, `∑_m b_m(x) (s - x)^m/m! = b_0(s)`. -/
theorem SokalHyp.borelLocal_real (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x s : ℝ} (hx : 0 < x)
    (hs : 0 < s) (hxs : |s - x| < ρ) : borelLocal f a x c (s : ℂ) = borelDeriv f a 0 s c := by
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hR := h.R_pos
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  set d : ℝ := |s - x| with hd
  set q : ℝ := d / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := (div_lt_one hρ).2 hxs
  set N : ℝ := K * (ρ + 1 / (2 * c)) with hN
  set E : ℝ := Real.exp (c * max x s) with hE
  have hN0 : 0 ≤ N := by positivity
  -- the remainder tends to zero
  have hrem : ∀ n : ℕ, ‖borelDeriv f a 0 s c -
      ∑ m ∈ range (n + 1), borelDeriv f a m x c * ((s : ℂ) - x) ^ m / (m ! : ℂ)‖ ≤
      N * E * d / ρ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n) := by
    intro n
    set ψ : ℝ → ℂ := fun y => ∑ m ∈ range (n + 1), borelDeriv f a m y c * ((s : ℂ) - y) ^ m / (m ! : ℂ)
      with hψ
    have hpos : ∀ y ∈ uIcc x s, 0 < y := fun y hy => by
      rcases le_total x s with hle | hle
      · rw [uIcc_of_le hle] at hy; linarith [hy.1]
      · rw [uIcc_of_ge hle] at hy; linarith [hy.1]
    have hbd : ∀ y ∈ uIcc x s,
        ‖borelDeriv f a (n + 1) y c * ((s : ℂ) - y) ^ n / (n ! : ℂ)‖ ≤
          N * E / ρ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n) := by
      intro y hy
      have hy0 := hpos y hy
      have hb := h.norm_borelDeriv_le hc (n + 1) hy0.le
      have hyM : y ≤ max x s := by
        rcases le_total x s with hle | hle
        · rw [uIcc_of_le hle] at hy; exact hy.2.trans (le_max_right _ _)
        · rw [uIcc_of_ge hle] at hy; exact hy.2.trans (le_max_left _ _)
      have hsy : |s - y| ≤ d := by
        rcases le_total x s with hle | hle
        · rw [uIcc_of_le hle] at hy
          rw [hd, abs_of_nonneg (by linarith [hy.2]), abs_of_nonneg (by linarith)]; linarith [hy.1]
        · rw [uIcc_of_ge hle] at hy
          rw [hd, abs_of_nonpos (show s - y ≤ 0 by linarith [hy.1]),
            abs_of_nonpos (show s - x ≤ 0 by linarith)]
          linarith [hy.2]
      have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
      have hEy : Real.exp (c * y) ≤ E := Real.exp_le_exp.2 (by nlinarith)
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_le_iff₀ hfac]
      have hsy' : ‖(s : ℂ) - y‖ ≤ d := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hsy
      calc ‖borelDeriv f a (n + 1) y c‖ * ‖(s : ℂ) - y‖ ^ n
          ≤ N * (n + 1 + 1) ! / ρ ^ (n + 1 + 1) * Real.exp (c * y) * d ^ n :=
            mul_le_mul hb (pow_le_pow_left₀ (norm_nonneg _) hsy' n) (by positivity) (by positivity)
        _ ≤ N * (n + 1 + 1) ! / ρ ^ (n + 1 + 1) * E * d ^ n := by gcongr
        _ = _ := by
          have : ((n + 1 + 1)! : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * n ! := by
            rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
          rw [this, hq, div_pow]
          field_simp
          ring
    have hmv := (convex_uIcc x s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := ψ) (f' := fun y => borelDeriv f a (n + 1) y c * ((s : ℂ) - y) ^ n / (n ! : ℂ))
      (fun y hy => (h.hasDerivAt_partial hc s n (hpos y hy)).hasDerivWithinAt) hbd
      (left_mem_uIcc : x ∈ uIcc x s) (right_mem_uIcc : s ∈ uIcc x s)
    have hψs : ψ s = borelDeriv f a 0 s c := by
      simp only [hψ]
      rw [sum_eq_single 0]
      · simp
      · intro m _ hm0; simp [hm0]
      · intro hh; simp at hh
    rw [hψs] at hmv
    have : ‖borelDeriv f a 0 s c - ψ x‖ ≤ N * E / ρ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n) * d := by
      simpa [hd, Real.norm_eq_abs, abs_sub_comm] using hmv
    refine this.trans (le_of_eq ?_)
    ring
  have hlim0 : Tendsto (fun n : ℕ => N * E * d / ρ ^ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 2) * q ^ n)) atTop (𝓝 0) := by
    have hq' : |q| < 1 := by rwa [abs_of_nonneg hq0]
    have t2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hq'
    have t1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq'
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have := ((t2.add (t1.const_mul 3)).add (t0.const_mul 2)).const_mul (N * E * d / ρ ^ 2)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun n => ?_
    ring
  have hsum := h.summable_borelLocal hc hx.le (t := (s : ℂ)) (by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hxs)
  have hT : Tendsto (fun n : ℕ => ∑ m ∈ range (n + 1),
      borelDeriv f a m x c * ((s : ℂ) - x) ^ m / (m ! : ℂ)) atTop (𝓝 (borelDeriv f a 0 s c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hlim0
    refine Eventually.of_forall fun n => ?_
    rw [norm_norm, norm_sub_rev]
    exact hrem n
  have hT2 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hT2 hT

end Lightlike.FieldTheory.Borel
