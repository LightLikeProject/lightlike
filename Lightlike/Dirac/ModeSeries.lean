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

end Lightlike.Dirac
