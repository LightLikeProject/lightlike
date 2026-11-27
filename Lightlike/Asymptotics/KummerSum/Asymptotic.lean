import Lightlike.Asymptotics.KummerSum.Assembly
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Kummer's sum: the saddle-point asymptotics against the closed form

The trust check of the saddle-point method on a sum with independently known asymptotics.

* **The method** (`tendsto_kummerSum_div_kummerLead`): `K(2n)/L(2n) → 1`, where
  `L(2n) = 2^{2n+1} (−1)^n √(π/(2(2n+1)))/π` (`kummerLead_two_mul`) is the leading term of the
  saddle-point bound `kummerSum_saddle_bound`: the contour identity, the complex Stirling formula,
  the saddle `α₀ = (1+i)/2` with `ψ''(α₀) = −4`, and Laplace's method.  It does not use the value of
  the sum.
* **The closed form** (`tendsto_centralBinom_div_kummerLead`): `(−1)^n C(2n, n)/L(2n) → 1`, from
  the real Stirling formula (`Stirling.tendsto_stirlingSeq_sqrt_pi`) alone, via
  `C(2n, n) = (s_{2n}/s_n²) 4^n/√n` with `s` Mathlib's Stirling sequence.
* `kummerSum_saddle_matches_closed_form` states both, together with Kummer's identity
  `K(2n) = (−1)^n C(2n, n)` (`kummer_alternating`): the saddle-point leading term is the known
  asymptotics `(−1)^n 4^n/√(πn)` of the closed form.
-/

open Complex Filter Topology Finset
open scoped Real Nat

namespace Lightlike.Asymptotics

lemma im_I_pow_two_mul_add_one (n : ℕ) : (I ^ (2 * n + 1)).im = (-1) ^ n := by
  rw [pow_succ, pow_mul, I_sq, show ((-1 : ℂ)) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
    mul_comm, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring

/-- `L(2n) = 2^{2n+1} (−1)^n √(π/(2(2n+1)))/π`. -/
lemma kummerLead_two_mul (n : ℕ) :
    kummerLead (2 * n) = 2 ^ (2 * n + 1) * (-1) ^ n * √(π / (2 * (2 * n + 1))) / π := by
  rw [kummerLead, im_I_pow_two_mul_add_one]; push_cast; ring

lemma kummerLead_two_mul_ne_zero (n : ℕ) : kummerLead (2 * n) ≠ 0 := by
  rw [kummerLead_two_mul]
  have hs : 0 < √(π / (2 * (2 * n + 1))) := Real.sqrt_pos.2 (by positivity)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (pow_ne_zero _ (by norm_num)))
    hs.ne') Real.pi_ne_zero

lemma abs_kummerLead_two_mul (n : ℕ) :
    |kummerLead (2 * n)| = 2 ^ (2 * n + 1) * √(π / (2 * (2 * n + 1))) / π := by
  rw [kummerLead_two_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow,
    mul_one, abs_of_pos Real.pi_pos, abs_of_nonneg (Real.sqrt_nonneg _), abs_two]

/-! ## The method's side -/

/-- `exp(1/2)/2 < 1`. -/
lemma exp_half_div_two_lt_one : Real.exp (1 / 2) / 2 < 1 := by
  rw [div_lt_one (by norm_num)]
  have h : Real.exp (1 / 2) ^ 2 < 2 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9; linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h

/-- **The saddle-point asymptotics of Kummer's sum**: `K(2n) / L(2n) → 1`, from the contour
method alone (`kummerSum_saddle_bound`). -/
theorem tendsto_kummerSum_div_kummerLead :
    Tendsto (fun n : ℕ => kummerSum (2 * n) / kummerLead (2 * n)) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := kummerSum_saddle_bound
  set r := Real.exp (1 / 2) / 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := exp_half_div_two_lt_one
  set Nn : ℕ → ℝ := fun n => ((2 * n + 1 : ℕ) : ℝ) with hNn
  have hk : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ _ by omega) tendsto_id
  have hNt : Tendsto Nn atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hq : Tendsto (fun n : ℕ => stirQ (2 * n + 1) ^ 2) atTop (𝓝 1) := by
    simpa using (tendsto_stirQ.comp hk).pow 2
  -- the bound
  set u : ℕ → ℝ := fun n => stirQ (2 * n + 1) ^ 2 *
    (|C| * (√(Nn n))⁻¹ + Real.exp (3 / 2) * (Nn n * r ^ (2 * n + 1))) with hu
  have hut : Tendsto u atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (√(Nn n))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNt)
    have h2 : Tendsto (fun n : ℕ => Nn n * r ^ (2 * n + 1)) atTop (𝓝 0) := by
      have := (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hk
      simpa [hNn, Function.comp_def] using this
    have := hq.mul ((h1.const_mul |C|).add (h2.const_mul (Real.exp (3 / 2))))
    simpa [hu] using this
  have hbound : ∀ᶠ n : ℕ in atTop,
      |kummerSum (2 * n) / kummerLead (2 * n) - stirQ (2 * n + 1) ^ 2| ≤ u n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hm : 5 ≤ 2 * n := by omega
    have hb := hC (2 * n) hm
    set N := Nn n with hN
    have hN1 : (1 : ℝ) ≤ N := by simp [hN, hNn]
    have hN0 : 0 < N := by linarith
    have hNc : ((2 * n : ℕ) : ℝ) + 1 = N := by simp [hN, hNn]
    have hNc' : (((2 * n + 1 : ℕ)) : ℝ) = N := rfl
    rw [hNc] at hb
    set q2 := stirQ (2 * n + 1) ^ 2
    have hq2 : 0 ≤ q2 := sq_nonneg _
    set L := kummerLead (2 * n)
    have hL0 := kummerLead_two_mul_ne_zero n
    set s := √(π / (2 * N)) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
    have hLabs : |L| = 2 ^ (2 * n + 1) * s / π := by
      rw [abs_kummerLead_two_mul]; congr 3; rw [hN, hNn]; push_cast; ring
    -- `1/s ≤ √N`
    have hsinv : s⁻¹ ≤ √N := by
      rw [hs, ← Real.sqrt_inv, inv_div]
      exact Real.sqrt_le_sqrt (by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three])
    have hsqN : √N ≤ N := by
      exact Real.sqrt_le_iff.2 ⟨hN0.le, by nlinarith⟩
    have hexpN : Real.exp (N / 2 + 3 / (2 * N)) ≤ Real.exp (3 / 2) * (2 ^ (2 * n + 1) * r ^ (2 * n + 1)) := by
      rw [← mul_pow, hr, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ← Real.exp_nat_mul,
        ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 3 / (2 * N) ≤ 3 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      rw [show ((2 * n + 1 : ℕ) : ℝ) = N from rfl]; linarith
    have hx : kummerSum (2 * n) / L - q2 = (kummerSum (2 * n) - q2 * L) / L := by
      rw [sub_div, mul_div_cancel_right₀ _ hL0]
    rw [hx, abs_div, div_le_iff₀ (abs_pos.2 hL0), hLabs]
    calc |kummerSum (2 * n) - q2 * L|
        ≤ q2 / π * (2 ^ (2 * n + 1) * C / N + Real.exp (N / 2 + 3 / (2 * N))) := by
          convert hb using 3
      _ ≤ q2 / π * (2 ^ (2 * n + 1) * |C| / N +
            Real.exp (3 / 2) * (2 ^ (2 * n + 1) * r ^ (2 * n + 1))) := by
          gcongr
          exact le_abs_self C
      _ ≤ u n * (2 ^ (2 * n + 1) * s / π) := by
          rw [hu]
          simp only [← hN]
          have hP : (0 : ℝ) < 2 ^ (2 * n + 1) := by positivity
          have hπ := Real.pi_pos
          -- `|C|/N ≤ |C| s /√N` and `1 ≤ N s` (from `1/s ≤ √N ≤ N`)
          have h1 : |C| / N ≤ |C| * (√N)⁻¹ * s := by
            have hsq : 0 < √N := Real.sqrt_pos.2 hN0
            rw [div_le_iff₀ hN0]
            have : 1 ≤ (√N)⁻¹ * s * N := by
              have := (inv_le_iff_one_le_mul₀' hs0).1 hsinv
              rw [show (√N)⁻¹ * s * N = s * √N * ((√N)⁻¹ * √N) * (N / (√N * √N)) by
                field_simp]
              rw [inv_mul_cancel₀ hsq.ne', Real.mul_self_sqrt hN0.le, div_self hN0.ne']
              linarith
            nlinarith [abs_nonneg C]
          have h2 : (1 : ℝ) ≤ N * s := by
            have := (inv_le_iff_one_le_mul₀' hs0).1 (hsinv.trans hsqN)
            linarith
          have hE := Real.exp_pos (3 / 2)
          have hrp : 0 ≤ r ^ (2 * n + 1) := pow_nonneg hr0 _
          rw [show q2 / π * (2 ^ (2 * n + 1) * |C| / N +
              Real.exp (3 / 2) * (2 ^ (2 * n + 1) * r ^ (2 * n + 1))) =
              q2 * 2 ^ (2 * n + 1) / π * (|C| / N + Real.exp (3 / 2) * r ^ (2 * n + 1)) by ring,
            show q2 * (|C| * (√N)⁻¹ + Real.exp (3 / 2) * (N * r ^ (2 * n + 1))) *
              (2 ^ (2 * n + 1) * s / π) =
              q2 * 2 ^ (2 * n + 1) / π * (|C| * (√N)⁻¹ * s +
                Real.exp (3 / 2) * r ^ (2 * n + 1) * (N * s)) by ring]
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (mul_nonneg hq2 hP.le) hπ.le)
          exact add_le_add h1 (le_mul_of_one_le_right (by positivity) h2)
  have hzero : Tendsto (fun n : ℕ => kummerSum (2 * n) / kummerLead (2 * n) -
      stirQ (2 * n + 1) ^ 2) atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hbound) hut
  simpa using hzero.add hq

/-! ## The closed form's side -/

/-- `n! = s_n √(2n) (n/e)^n` for `n ≥ 1`, with `s` Mathlib's Stirling sequence. -/
lemma factorial_eq_stirlingSeq {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) = Stirling.stirlingSeq n * (√(2 * n) * (n / Real.exp 1) ^ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Stirling.stirlingSeq, div_mul_cancel₀]
  positivity

/-- **The central binomial coefficient via Stirling**: `C(2n, n) = (s_{2n}/s_n²) 4^n/√n`. -/
lemma centralBinom_eq_stirlingSeq {n : ℕ} (hn : 1 ≤ n) :
    ((2 * n).choose n : ℝ) =
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 * 4 ^ n / √n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs1 : 0 < Stirling.stirlingSeq n := by
    rw [Stirling.stirlingSeq]; have := n.factorial_pos; positivity
  have hc : ((2 * n).choose n : ℝ) * n ! * n ! = (2 * n) ! := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this; exact_mod_cast this
  have h1 := factorial_eq_stirlingSeq hn
  have h2 := factorial_eq_stirlingSeq (show 1 ≤ 2 * n by omega)
  have hsq : √(2 * ((2 * n : ℕ) : ℝ)) = 2 * √n := by
    rw [show 2 * ((2 * n : ℕ) : ℝ) = 2 ^ 2 * n by push_cast; ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have hsq2 : √(2 * (n : ℝ)) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have hpow : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) = 4 ^ n * ((n : ℝ) / Real.exp 1) ^ (2 * n) := by
    rw [show (((2 * n : ℕ) : ℝ) / Real.exp 1) = 2 * ((n : ℝ) / Real.exp 1) by push_cast; ring,
      mul_pow, pow_mul]; norm_num
  have hpos : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hsqn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  rw [h1, h2, hsq, hpow] at hc
  have hsqnn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn0.le
  have hX2 : ((n : ℝ) / Real.exp 1) ^ (2 * n) = (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [hX2] at hc
  rw [eq_div_iff hsqn.ne', div_mul_eq_mul_div, eq_div_iff (by positivity)]
  have hX : 2 * √(n : ℝ) * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 ≠ 0 := by positivity
  apply mul_right_cancel₀ hX
  linear_combination hc + 2 * ((2 * n).choose n : ℝ) * Stirling.stirlingSeq n ^ 2 *
    (((n : ℝ) / Real.exp 1) ^ n) ^ 2 * hsqnn -
    ((2 * n).choose n : ℝ) * Stirling.stirlingSeq n ^ 2 * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 * hsq2

/-- **The closed form has the same asymptotics**: `(−1)^n C(2n, n) / L(2n) → 1`, from the real
Stirling formula. -/
theorem tendsto_centralBinom_div_kummerLead :
    Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) / kummerLead (2 * n)) atTop
      (𝓝 1) := by
  have hk : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ _ by omega) tendsto_id
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hratio : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2)
      atTop (𝓝 (√π / √π ^ 2)) :=
    (hs.comp hk).div (hs.pow 2) (by positivity)
  have hsqrt : Tendsto (fun n : ℕ => √(1 + 1 / (2 * (n : ℝ)))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))).congr (fun n => ?_)
      simp
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).sqrt
  have hlim := (hratio.mul_const (√π)).mul hsqrt
  have hπ : √π / √π ^ 2 * √π * 1 = 1 := by
    have : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    field_simp
  rw [hπ] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [centralBinom_eq_stirlingSeq hn, kummerLead_two_mul]
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hspi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have h1 : √(π / (2 * (2 * n + 1))) = √π / √(2 * (2 * n + 1)) := by
    rw [Real.sqrt_div' _ (by positivity)]
  have h2 : √(1 + 1 / (2 * (n : ℝ))) = √(2 * (2 * n + 1)) / (2 * √n) := by
    rw [show (1 : ℝ) + 1 / (2 * n) = (2 * (2 * n + 1)) / (2 * √n) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hn0.le]; field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [h1, h2]
  have h3 : 0 < √(2 * (2 * (n : ℝ) + 1)) := Real.sqrt_pos.2 (by positivity)
  have hpm0 : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs1 : Stirling.stirlingSeq n ≠ 0 := by
    rw [Stirling.stirlingSeq]; have := n.factorial_pos; positivity
  rw [pow_succ, show (4 : ℝ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le, pow_succ]
  ring

/-- **The saddle-point method gives the right asymptotics for Kummer's sum.**  The leading term
`L(2n)` of the contour/Stirling/Laplace argument (`kummerSum_saddle_bound`), computed without the
value of the sum, is the asymptotics of both Kummer's sum and its closed form `(−1)^n C(2n, n)`,
and the two agree exactly (`kummer_alternating`). -/
theorem kummerSum_saddle_matches_closed_form :
    Tendsto (fun n : ℕ => kummerSum (2 * n) / kummerLead (2 * n)) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) / kummerLead (2 * n)) atTop (𝓝 1) ∧
    ∀ n : ℕ, kummerSum (2 * n) = (-1 : ℝ) ^ n * ((2 * n).choose n : ℝ) := by
  refine ⟨tendsto_kummerSum_div_kummerLead, tendsto_centralBinom_div_kummerLead, fun n => ?_⟩
  have h := kummer_alternating n
  rw [kummerSum]
  have := congrArg (fun x : ℤ => (x : ℝ)) h
  push_cast at this
  exact this

end Lightlike.Asymptotics
