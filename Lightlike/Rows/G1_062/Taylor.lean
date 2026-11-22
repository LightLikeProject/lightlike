import Mathlib

/-!
# A Taylor remainder bound for derivative chains

For the Euler–Maclaurin / midpoint-rule estimate of the sphere heat trace (row G1-062) we need a
Taylor bound around a *midpoint* with explicit constants.  We phrase it for a *derivative chain*
`u : ℕ → ℝ → ℝ` (`u (i+1)` is the derivative of `u i`), which avoids `iteratedDeriv`.

## Main results

* `Lightlike.Rows.G1_062.tayRem_bound`: one-sided Taylor remainder bound.
* `Lightlike.Rows.G1_062.midpoint_bound`: the symmetric difference
  `u 0 (m+r) - u 0 (m-r)` equals the odd part of the Taylor polynomial up to `2 M r^n / n!`.
-/

open Set intervalIntegral

namespace Lightlike.Rows.G1_062

/-- `u` is a derivative chain: `u (i+1)` is the derivative of `u i`. -/
def IsChain (u : ℕ → ℝ → ℝ) : Prop := ∀ i x, HasDerivAt (u i) (u (i + 1) x) x

lemma IsChain.continuous {u : ℕ → ℝ → ℝ} (hu : IsChain u) (i : ℕ) : Continuous (u i) :=
  continuous_iff_continuousAt.2 fun x => (hu i x).continuousAt

/-- The remainder of the `n`-term Taylor polynomial of `u 0` at `m`. -/
noncomputable def tayRem (u : ℕ → ℝ → ℝ) (m : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  u 0 x - ∑ k ∈ Finset.range n, u k m * (x - m) ^ k / (k.factorial : ℝ)

lemma tayRem_hasDerivAt (u : ℕ → ℝ → ℝ) (hu : IsChain u) (m : ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (tayRem u m (n + 1)) (tayRem (fun i => u (i + 1)) m n y) y := by
  have hterm : ∀ k : ℕ, HasDerivAt (fun y => u k m * (y - m) ^ k / (k.factorial : ℝ))
      (u k m * ((k : ℝ) * (y - m) ^ (k - 1)) / k.factorial) y := by
    intro k
    have h1 := ((((hasDerivAt_id y).sub_const m).pow k).const_mul (u k m)).div_const
      (k.factorial : ℝ)
    simpa using h1
  have hsum := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun k _ => hterm k)
  have h2 := (hu 0 y).sub hsum
  refine h2.congr_deriv ?_
  rw [tayRem, Finset.sum_range_succ' _ n]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **One-sided Taylor bound** for a derivative chain: if `|u n| ≤ M` on `[m, m+r]` then on that
interval the `n`-term Taylor remainder at `m` is at most `M (x-m)^n / n!`. -/
theorem tayRem_bound (m r M : ℝ) :
    ∀ (n : ℕ) (u : ℕ → ℝ → ℝ), IsChain u → (∀ y ∈ Icc m (m + r), |u n y| ≤ M) →
      ∀ x ∈ Icc m (m + r), |tayRem u m n x| ≤ M * (x - m) ^ n / n.factorial := by
  intro n
  induction n with
  | zero =>
    intro u hu hb x hx
    simpa [tayRem] using hb x hx
  | succ n ih =>
    intro u hu hb x hx
    have hu' : IsChain (fun i => u (i + 1)) := fun i y => hu (i + 1) y
    have ih' := ih (fun i => u (i + 1)) hu' (fun y hy => hb y hy)
    have hcont : Continuous (tayRem (fun i => u (i + 1)) m n) := by
      unfold tayRem
      refine (hu'.continuous 0).sub (continuous_finsetSum _ fun k _ => ?_)
      fun_prop
    have hG0 : tayRem u m (n + 1) m = 0 := by
      rw [tayRem, Finset.sum_range_succ' _ n]
      simp
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := tayRem u m (n + 1)) (f' := tayRem (fun i => u (i + 1)) m n) (a := m) (b := x)
      (fun y _ => tayRem_hasDerivAt u hu m n y) (hcont.intervalIntegrable _ _)
    rw [hG0, sub_zero] at hftc
    have hxm : m ≤ x := hx.1
    have hbd : ‖∫ y in m..x, tayRem (fun i => u (i + 1)) m n y‖
        ≤ ∫ y in m..x, M * (y - m) ^ n / (n.factorial : ℝ) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hxm ?_ ?_
      · refine Filter.Eventually.of_forall fun y hy => ?_
        rw [Real.norm_eq_abs]
        exact ih' y ⟨hy.1.le, hy.2.trans hx.2⟩
      · exact (by fun_prop : Continuous fun y : ℝ => M * (y - m) ^ n / (n.factorial : ℝ)).intervalIntegrable _ _
    have hint : ∫ y in m..x, M * (y - m) ^ n / (n.factorial : ℝ)
        = M * (x - m) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      have h1 := intervalIntegral.integral_comp_sub_right
        (fun y : ℝ => M * y ^ n / (n.factorial : ℝ)) (a := m) (b := x) m
      rw [h1]
      simp only [sub_self, mul_div_assoc]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [← hftc, ← Real.norm_eq_abs]
    rw [hint] at hbd
    exact hbd

/-- **Midpoint Taylor bound**: for a derivative chain `u` with `|u n| ≤ M` on `[m-r, m+r]`,
`u 0 (m+r) - u 0 (m-r)` agrees with `∑_{k<n} u k m (r^k - (-r)^k)/k!` up to `2 M r^n/n!`. -/
theorem midpoint_bound (u : ℕ → ℝ → ℝ) (hu : IsChain u) (m r M : ℝ) (hr : 0 ≤ r) (n : ℕ)
    (hb : ∀ y ∈ Icc (m - r) (m + r), |u n y| ≤ M) :
    |u 0 (m + r) - u 0 (m - r)
      - ∑ k ∈ Finset.range n, u k m * (r ^ k - (-r) ^ k) / (k.factorial : ℝ)|
      ≤ 2 * (M * r ^ n / n.factorial) := by
  -- right side
  have hR := tayRem_bound m r M n u hu
    (fun y hy => hb y ⟨by linarith [hy.1], hy.2⟩) (m + r) ⟨by linarith, le_refl _⟩
  -- reflected chain
  set v : ℕ → ℝ → ℝ := fun i y => (-1) ^ i * u i (2 * m - y) with hv
  have hvc : IsChain v := by
    intro i y
    have h1 : HasDerivAt (fun y : ℝ => 2 * m - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (2 * m)
    have h2 := ((hu i (2 * m - y)).scomp y h1).const_mul ((-1 : ℝ) ^ i)
    refine h2.congr_deriv ?_
    simp only [smul_eq_mul, hv, pow_succ]
    ring
  have hL := tayRem_bound m r M n v hvc
    (fun y hy => by
      simp only [hv, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hb _ ⟨by linarith [hy.2], by linarith [hy.1]⟩) (m + r) ⟨by linarith, le_refl _⟩
  simp only [tayRem, hv] at hR hL
  have e1 : (2 * m - (m + r)) = m - r := by ring
  simp only [pow_zero, one_mul, e1, add_sub_cancel_left] at hR hL
  have e2 : ∀ k : ℕ, (-1 : ℝ) ^ k * u k (2 * m - m) * r ^ k / (k.factorial : ℝ)
      = u k m * (-r) ^ k / (k.factorial : ℝ) := by
    intro k
    have : (2 * m - m) = m := by ring
    rw [this, neg_pow r k]
    ring
  simp only [e2] at hL
  have hsplit : u 0 (m + r) - u 0 (m - r)
      - ∑ k ∈ Finset.range n, u k m * (r ^ k - (-r) ^ k) / (k.factorial : ℝ)
      = (u 0 (m + r) - ∑ k ∈ Finset.range n, u k m * r ^ k / (k.factorial : ℝ))
        - (u 0 (m - r) - ∑ k ∈ Finset.range n, u k m * (-r) ^ k / (k.factorial : ℝ)) := by
    simp only [mul_sub, sub_div, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc _ ≤ |u 0 (m + r) - ∑ k ∈ Finset.range n, u k m * r ^ k / (k.factorial : ℝ)|
        + |u 0 (m - r) - ∑ k ∈ Finset.range n, u k m * (-r) ^ k / (k.factorial : ℝ)| :=
        abs_sub _ _
    _ ≤ _ := by linarith

end Lightlike.Rows.G1_062
