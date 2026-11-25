import Mathlib
import Lightlike.Dirac.ModeODE

/-!
# The regular solution of the radial mode system as a power series (stage S1)

With `a = r^m F(t)`, `b = r^{m+1} H(t)`, `t = r²`, `μ = ν/2`, the system is `(1+t) F' = μ H`,
`(1+t)(t H' + (m+1) H) = μ F`.  The Taylor coefficients `f_n`, `h_n` (normalised by `f₀ = 1`) satisfy
`(n+1) f_{n+1} + n f_n = μ h_n` and `(n+m+1) h_n + (n+m) h_{n-1} = μ f_n`.
They grow at most polynomially, so the series converge for `|t| < 1`.
-/

namespace Lightlike.Dirac

/-- The pair `(f_n, h_{n-1})` of Taylor coefficients (with `h_{-1} = 0`), `f₀ = 1`. -/
noncomputable def coefPair (μ : ℂ) (m : ℕ) : ℕ → ℂ × ℂ
  | 0 => (1, 0)
  | n + 1 =>
    let p := coefPair μ m n
    let hn := (μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)
    ((μ * hn - (n : ℂ) * p.1) / ((n : ℂ) + 1), hn)

/-- The coefficients of `F`. -/
noncomputable def coefF (μ : ℂ) (m : ℕ) (n : ℕ) : ℂ := (coefPair μ m n).1

/-- The coefficients of `H`. -/
noncomputable def coefH (μ : ℂ) (m : ℕ) (n : ℕ) : ℂ := (coefPair μ m (n + 1)).2

/-- `h_n` from the pair at stage `n`. -/
lemma coefH_eq (μ : ℂ) (m n : ℕ) :
    ((n : ℂ) + m + 1) * coefH μ m n = μ * coefF μ m n - ((n : ℂ) + m) * (coefPair μ m n).2 := by
  have hne : ((n : ℂ) + m + 1) ≠ 0 := by
    have : (0 : ℝ) < n + m + 1 := by positivity
    exact_mod_cast this.ne'
  unfold coefH coefF
  rw [coefPair]
  simp only []
  field_simp

/-- First recurrence: `(n+1) f_{n+1} + n f_n = μ h_n`. -/
lemma coefF_succ (μ : ℂ) (m n : ℕ) :
    ((n : ℂ) + 1) * coefF μ m (n + 1) + (n : ℂ) * coefF μ m n = μ * coefH μ m n := by
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold coefF coefH
  rw [coefPair]
  simp only []
  field_simp
  ring

/-- One step of the growth estimate, in real numbers. -/
lemma step_bound (ρ B x y : ℝ) (n m : ℕ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hx : x ≤ B) (hy : y ≤ B) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) :
    (ρ * x + (n + m) * y) / (n + m + 1) ≤ B * (1 + (1 + ρ * (1 + ρ)) / (n + 1)) ∧
    (ρ * ((ρ * x + (n + m) * y) / (n + m + 1)) + n * x) / (n + 1) ≤ B * (1 + (1 + ρ * (1 + ρ)) / (n + 1)) := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hnm1 : (0 : ℝ) < n + m + 1 := by positivity
  have hnm : (0 : ℝ) ≤ n + m := by positivity
  have hh : (ρ * x + (n + m) * y) / (n + m + 1) ≤ B * (1 + ρ / (n + 1)) := by
    rw [div_le_iff₀ hnm1]
    have : (n + m + 1 : ℝ) ≥ n + 1 := by have : (0 : ℝ) ≤ m := by positivity
                                         linarith
    have e : B * (1 + ρ / (n + 1)) * (n + m + 1) = B * (n + m + 1) + B * ρ * ((n + m + 1) / (n + 1)) := by
      field_simp
    have h2 : ρ * x + (n + m) * y ≤ ρ * B + (n + m) * B := by nlinarith
    have h3 : B * ρ * ((n + m + 1) / (n + 1)) ≥ B * ρ := by
      have : (n + m + 1) / (n + 1 : ℝ) ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hn1]; linarith
      nlinarith [mul_nonneg hB hρ]
    nlinarith
  have hK : ρ / (n + 1) ≤ (1 + ρ * (1 + ρ)) / (n + 1) := by
    apply div_le_div_of_nonneg_right _ hn1.le; nlinarith
  refine ⟨hh.trans (by nlinarith), ?_⟩
  rw [div_le_iff₀ hn1]
  have e1 : ρ * ((ρ * x + (n + m) * y) / (n + m + 1)) ≤ ρ * (B * (1 + ρ / (n + 1))) :=
    mul_le_mul_of_nonneg_left hh hρ
  have e2 : B * (1 + ρ / (n + 1)) ≤ B * (1 + ρ) := by
    apply mul_le_mul_of_nonneg_left _ hB
    have : ρ / (n + 1) ≤ ρ := by
      rw [div_le_iff₀ hn1]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have e3 : B * (1 + (1 + ρ * (1 + ρ)) / (n + 1)) * (n + 1) = B * (n + 1) + B * (1 + ρ * (1 + ρ)) := by
    field_simp
  rw [e3]
  have e4 : (n : ℝ) * x ≤ n * B := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg n)
  nlinarith [mul_nonneg hρ hB, mul_le_mul_of_nonneg_left e2 hρ]

/-- **Polynomial growth of the Taylor coefficients.** -/
theorem coefPair_bound (μ : ℂ) (m : ℕ) : ∀ n : ℕ,
    ‖(coefPair μ m n).1‖ ≤ ((n : ℝ) + 1) ^ (1 + ‖μ‖ * (1 + ‖μ‖)) ∧
    ‖(coefPair μ m n).2‖ ≤ ((n : ℝ) + 1) ^ (1 + ‖μ‖ * (1 + ‖μ‖)) := by
  set K : ℝ := 1 + ‖μ‖ * (1 + ‖μ‖) with hK
  have hK1 : 1 ≤ K := by rw [hK]; nlinarith [norm_nonneg μ, mul_nonneg (norm_nonneg μ) (norm_nonneg μ)]
  intro n
  induction n with
  | zero => simp [coefPair]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set p := coefPair μ m n with hp
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hnm1 : (0 : ℝ) < n + m + 1 := by positivity
    have hB : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ K := (Real.rpow_nonneg hn1.le _)
    obtain ⟨s1, s2⟩ := step_bound ‖μ‖ (((n : ℝ) + 1) ^ K) ‖p.1‖ ‖p.2‖ n m (norm_nonneg _) hB ih1 ih2
      (norm_nonneg _) (norm_nonneg _)
    -- norms of the new coefficients
    have hhn : ‖(μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)‖ ≤
        (‖μ‖ * ‖p.1‖ + (n + m) * ‖p.2‖) / (n + m + 1) := by
      rw [norm_div]
      have hd : ‖((n : ℂ) + m + 1)‖ = (n : ℝ) + m + 1 := by
        have : ((n : ℂ) + m + 1) = (((n : ℝ) + m + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg hnm1.le]
      rw [hd]
      apply div_le_div_of_nonneg_right _ hnm1.le
      calc ‖μ * p.1 - ((n : ℂ) + m) * p.2‖ ≤ ‖μ * p.1‖ + ‖((n : ℂ) + m) * p.2‖ := norm_sub_le _ _
        _ = ‖μ‖ * ‖p.1‖ + (n + m) * ‖p.2‖ := by
          rw [norm_mul, norm_mul]
          congr 2
          have : ((n : ℂ) + m) = (((n : ℝ) + m : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hfn : ‖(μ * ((μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)) - (n : ℂ) * p.1) / ((n : ℂ) + 1)‖ ≤
        (‖μ‖ * ((‖μ‖ * ‖p.1‖ + (n + m) * ‖p.2‖) / (n + m + 1)) + n * ‖p.1‖) / (n + 1) := by
      rw [norm_div]
      have hd : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
        have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg hn1.le]
      rw [hd]
      apply div_le_div_of_nonneg_right _ hn1.le
      calc _ ≤ ‖μ * ((μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1))‖ + ‖(n : ℂ) * p.1‖ := norm_sub_le _ _
        _ ≤ ‖μ‖ * ((‖μ‖ * ‖p.1‖ + (n + m) * ‖p.2‖) / (n + m + 1)) + n * ‖p.1‖ := by
          rw [norm_mul, norm_mul]
          refine add_le_add (mul_le_mul_of_nonneg_left hhn (norm_nonneg _)) ?_
          simp
    -- Bernoulli
    have hb : (((n : ℝ) + 1) ^ K) * (1 + K / (n + 1)) ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ K := by
      have hs0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      have h1 : 1 + K * (1 / ((n : ℝ) + 1)) ≤ (1 + 1 / ((n : ℝ) + 1)) ^ K :=
        one_add_mul_self_le_rpow_one_add (by linarith) hK1
      have h2 : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) * (1 + 1 / ((n : ℝ) + 1)) := by
        push_cast; field_simp
      rw [h2, Real.mul_rpow hn1.le (by positivity)]
      apply mul_le_mul_of_nonneg_left _ hB
      calc 1 + K / (n + 1) = 1 + K * (1 / ((n : ℝ) + 1)) := by ring
        _ ≤ _ := h1
    constructor
    · show ‖(μ * ((μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)) - (n : ℂ) * p.1) / ((n : ℂ) + 1)‖ ≤ _
      exact (hfn.trans s2).trans hb
    · show ‖(μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)‖ ≤ _
      exact (hhn.trans s1).trans hb

/-- `Σ (n+1)^N ρ^n` converges for `0 ≤ ρ < 1`. -/
lemma summable_succ_pow_geom (N : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * ρ ^ n := by
  rcases h0.eq_or_lt with rfl | hpos
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [this]
  have hs := (summable_pow_mul_geometric_of_norm_lt_one N (r := ρ) (by rw [Real.norm_of_nonneg h0]; exact h1))
  have hs' := (summable_nat_add_iff 1).mpr hs
  have := hs'.div_const ρ
  refine this.congr fun n => ?_
  push_cast
  field_simp
  ring

/-- A sequence with polynomial growth gives an absolutely convergent power series on the unit disc. -/
lemma summable_poly_mul_pow {K : ℝ} {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ ((n : ℝ) + 1) ^ K) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ < 1) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ ⌈K⌉₊ * ρ ^ n := summable_succ_pow_geom _ h0 h1

/-- The sum of the power series with coefficients `c`, as a function of the real variable `t`. -/
noncomputable def powerSum (c : ℕ → ℂ) (t : ℝ) : ℂ := ∑' n, c n * (t : ℂ) ^ n

/-- **Termwise differentiation** of a power series with polynomially growing coefficients on `(-1, 1)`. -/
theorem hasDerivAt_powerSum {K C : ℝ} {c : ℕ → ℂ} (hC : 0 ≤ C) (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K) {t : ℝ}
    (ht : |t| < 1) :
    HasDerivAt (powerSum c) (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * (t : ℂ) ^ n) t := by
  obtain ⟨ρ, hρ0, hρt, hρ1⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ |t| < ρ ∧ ρ < 1 :=
    ⟨(|t| + 1) / 2, by positivity, by linarith, by linarith⟩
  have hρpos : 0 < ρ := lt_of_le_of_lt (abs_nonneg t) hρt
  set N : ℕ := ⌈K⌉₊ + 1 with hN
  -- bound on the derivative terms: ‖n c_n y^{n-1}‖ ≤ (n+1)^{N} ρ^{n-1}·...
  let u : ℕ → ℝ := fun n => C * (((n : ℝ) + 1) ^ N * ρ ^ n / ρ)
  have hu : Summable u := ((summable_succ_pow_geom N hρpos.le hρ1).div_const ρ).mul_left C
  have hK : ∀ n : ℕ, ((n : ℝ) + 1) ^ K ≤ ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℝ) :=
    fun n => Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (Nat.le_ceil K)
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-ρ) ρ →
      HasDerivAt (fun y : ℝ => c n * (y : ℂ) ^ n) ((n : ℂ) * c n * (y : ℂ) ^ (n - 1)) y := by
    intro n y _
    have := ((hasDerivAt_pow n (y : ℂ)).comp_ofReal).const_mul (c n)
    convert this using 1
    ring
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-ρ) ρ → ‖(n : ℂ) * c n * (y : ℂ) ^ (n - 1)‖ ≤ u n := by
    intro n y hy
    have hy' : |y| ≤ ρ := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [u]; positivity
    · rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖(n : ℂ)‖ = n := by simp
      rw [h1]
      have h2 : |y| ^ (n - 1) ≤ ρ ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
      have h3 : ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℕ) := by
        calc ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K := hc n
          _ ≤ C * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℝ) := mul_le_mul_of_nonneg_left (hK n) hC
          _ = C * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℕ) := by rw [Real.rpow_natCast]
      have h4 : (n : ℝ) * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℕ) ≤ ((n : ℝ) + 1) ^ N := by
        rw [hN, pow_succ, mul_comm (((n : ℝ) + 1) ^ ⌈K⌉₊)]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h5 : ρ ^ (n - 1) = ρ ^ n / ρ := by
        rw [eq_div_iff hρpos.ne', ← pow_succ, Nat.sub_add_cancel hn]
      rw [mul_assoc]
      calc (n : ℝ) * (‖c n‖ * |y| ^ (n - 1)) ≤ (n : ℝ) * ((C * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℕ)) * ρ ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h3 h2 (by positivity) (by positivity)) (Nat.cast_nonneg n)
        _ = C * (((n : ℝ) * ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℕ)) * ρ ^ (n - 1)) := by ring
        _ ≤ C * (((n : ℝ) + 1) ^ N * ρ ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (by positivity)) hC
        _ = u n := by simp only [u]; rw [h5]; ring
  have hset : t ∈ Set.Ioo (-ρ) ρ := by
    constructor <;> [exact (neg_lt_of_abs_lt hρt); exact (lt_of_abs_lt hρt)]
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρpos⟩
  have hsum0 : Summable fun n : ℕ => c n * ((0 : ℝ) : ℂ) ^ n := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [this]
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n (y : ℝ) => c n * (y : ℂ) ^ n)
    (g' := fun n y => (n : ℂ) * c n * (y : ℂ) ^ (n - 1)) hu isOpen_Ioo isPreconnected_Ioo hg hg' h0 hsum0 hset
  have hshift : ∑' n : ℕ, (n : ℂ) * c n * (t : ℂ) ^ (n - 1) = ∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * (t : ℂ) ^ n := by
    have hs : Summable fun n : ℕ => (n : ℂ) * c n * (t : ℂ) ^ (n - 1) :=
      Summable.of_norm_bounded hu fun n => hg' n t hset
    rw [hs.tsum_eq_zero_add]
    simp
  rw [hshift] at key
  exact key

/-- The power-series terms converge absolutely on `(-1, 1)`. -/
theorem summable_powerTerms {K C : ℝ} {c : ℕ → ℂ} (hC : 0 ≤ C) (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K) {t : ℝ}
    (ht : |t| < 1) : Summable fun n : ℕ => c n * (t : ℂ) ^ n := by
  have hs : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ ⌈K⌉₊ * |t| ^ n) :=
    (summable_succ_pow_geom _ (abs_nonneg t) ht).mul_left C
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hK : ((n : ℝ) + 1) ^ K ≤ ((n : ℝ) + 1) ^ (⌈K⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (Nat.le_ceil K)
  rw [Real.rpow_natCast] at hK
  calc ‖c n‖ * |t| ^ n ≤ (C * ((n : ℝ) + 1) ^ K) * |t| ^ n :=
        mul_le_mul_of_nonneg_right (hc n) (by positivity)
    _ ≤ (C * ((n : ℝ) + 1) ^ ⌈K⌉₊) * |t| ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ ⌈K⌉₊ * |t| ^ n) := by ring

/-- The coefficients of the derivative series have polynomial growth too. -/
lemma deriv_coeff_bound {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) {c : ℕ → ℂ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K) (n : ℕ) :
    ‖((n : ℂ) + 1) * c (n + 1)‖ ≤ (C * 2 ^ K) * ((n : ℝ) + 1) ^ (K + 1) := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  rw [norm_mul]
  have h1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg hn1.le]
  rw [h1]
  have h2 : (((n + 1 : ℕ) : ℝ) + 1) ^ K ≤ 2 ^ K * ((n : ℝ) + 1) ^ K := by
    rw [← Real.mul_rpow (by norm_num) hn1.le]
    apply Real.rpow_le_rpow (by positivity) _ hK
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ((n : ℝ) + 1) * ‖c (n + 1)‖ ≤ ((n : ℝ) + 1) * (C * (((n + 1 : ℕ) : ℝ) + 1) ^ K) :=
        mul_le_mul_of_nonneg_left (hc (n + 1)) hn1.le
    _ ≤ ((n : ℝ) + 1) * (C * (2 ^ K * ((n : ℝ) + 1) ^ K)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) hn1.le
    _ = (C * 2 ^ K) * ((n : ℝ) + 1) ^ (K + 1) := by
        rw [Real.rpow_add hn1, Real.rpow_one]; ring

/-- The exponent of the growth bound of the Taylor coefficients. -/
noncomputable def growthK (μ : ℂ) : ℝ := 1 + ‖μ‖ * (1 + ‖μ‖)

lemma growthK_nonneg (μ : ℂ) : 0 ≤ growthK μ := by
  unfold growthK; positivity

lemma coefF_bound (μ : ℂ) (m n : ℕ) : ‖coefF μ m n‖ ≤ 1 * ((n : ℝ) + 1) ^ growthK μ := by
  rw [one_mul]; exact (coefPair_bound μ m n).1

lemma coefH_bound (μ : ℂ) (m n : ℕ) : ‖coefH μ m n‖ ≤ 2 ^ growthK μ * ((n : ℝ) + 1) ^ growthK μ := by
  have h := (coefPair_bound μ m (n + 1)).2
  unfold coefH
  refine h.trans ?_
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ (growthK_nonneg μ)
  push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **First differential equation of the series**: `(1+t) F' = μ H` on `(-1, 1)`. -/
theorem series_ode_one (μ : ℂ) (m : ℕ) {t : ℝ} (ht : |t| < 1) :
    (1 + (t : ℂ)) * (∑' n : ℕ, ((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n) =
      μ * powerSum (coefH μ m) t := by
  set K := growthK μ with hK
  have hKn := growthK_nonneg μ
  have hA : Summable fun n : ℕ => ((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n :=
    summable_powerTerms (K := K + 1) (C := 1 * 2 ^ K) (by positivity)
      (fun n => deriv_coeff_bound hKn zero_le_one (coefF_bound μ m) n) ht
  have hB : Summable fun n : ℕ => (n : ℂ) * coefF μ m n * (t : ℂ) ^ n := by
    refine summable_powerTerms (K := K + 1) (C := 1) zero_le_one (fun n => ?_) ht
    rw [norm_mul]
    have h1 : ‖(n : ℂ)‖ = n := by simp
    rw [h1, Real.rpow_add (by positivity), Real.rpow_one, one_mul]
    calc (n : ℝ) * ‖coefF μ m n‖ ≤ ((n : ℝ) + 1) * (1 * ((n : ℝ) + 1) ^ K) :=
          mul_le_mul (by linarith) (coefF_bound μ m n) (norm_nonneg _) (by positivity)
      _ = ((n : ℝ) + 1) ^ K * ((n : ℝ) + 1) := by ring
  have hH : Summable fun n : ℕ => coefH μ m n * (t : ℂ) ^ n :=
    summable_powerTerms (K := K) (C := 2 ^ K) (by positivity) (coefH_bound μ m) ht
  have hshift : ∑' n : ℕ, (n : ℂ) * coefF μ m n * (t : ℂ) ^ n =
      (t : ℂ) * ∑' n : ℕ, ((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n := by
    rw [hB.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
    refine tsum_congr fun n => ?_
    ring
  calc (1 + (t : ℂ)) * (∑' n : ℕ, ((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n)
      = (∑' n : ℕ, ((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n) +
        ∑' n : ℕ, (n : ℂ) * coefF μ m n * (t : ℂ) ^ n := by rw [hshift]; ring
    _ = ∑' n : ℕ, (((n : ℂ) + 1) * coefF μ m (n + 1) * (t : ℂ) ^ n + (n : ℂ) * coefF μ m n * (t : ℂ) ^ n) :=
        (hA.tsum_add hB).symm
    _ = ∑' n : ℕ, μ * (coefH μ m n * (t : ℂ) ^ n) := by
        refine tsum_congr fun n => ?_
        have := coefF_succ μ m n
        linear_combination (t : ℂ) ^ n * this
    _ = μ * powerSum (coefH μ m) t := by rw [tsum_mul_left]; rfl

end Lightlike.Dirac
