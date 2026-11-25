import Mathlib
import Lightlike.Dirac.ModeSeries
import Lightlike.Dirac.GaussSum

/-!
# The regular mode solution as a hypergeometric series

`G(x) = Σ hgTerm a (m+1) n · xⁿ` is `₂F₁(a, −a; m+1; x)`.  It is differentiable twice on `(-1, 1)` and satisfies
`x(1−x) G'' + (m+1−x) G' + a² G = 0`.
-/

namespace Lightlike.Dirac

/-- The coefficients of `₂F₁(a, −a; m+1; x)`. -/
noncomputable def hgCoef (a : ℂ) (m : ℕ) : ℕ → ℂ := hgTerm a ((m : ℂ) + 1)

/-- Recurrence of the coefficients. -/
lemma hgCoef_succ (a : ℂ) (m n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + m + 1) * hgCoef a m (n + 1) = ((n : ℂ) ^ 2 - a ^ 2) * hgCoef a m n := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : ((n : ℂ) + m + 1) ≠ 0 := by
    have : (0 : ℝ) < n + m + 1 := by positivity
    exact_mod_cast this.ne'
  unfold hgCoef
  rw [hgTerm]
  have : ((m : ℂ) + 1 + n) = ((n : ℂ) + m + 1) := by ring
  rw [this]
  field_simp
  ring

/-- The sum `G(x)`. -/
noncomputable def hgSum (a : ℂ) (m : ℕ) : ℝ → ℂ := powerSum (hgCoef a m)

/-- First derivative coefficients `(n+1) γ_{n+1}`. -/
noncomputable def hgCoef1 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef a m (n + 1)

/-- Second derivative coefficients `(n+1)(n+2) γ_{n+2}`. -/
noncomputable def hgCoef2 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef1 a m (n + 1)

lemma hgCoef_bound (a : ℂ) (m n : ℕ) : ‖hgCoef a m n‖ ≤ 1 * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1) := by
  rw [one_mul]; exact hgTerm_bound a m n

/-- `G' = Σ (n+1) γ_{n+1} xⁿ`. -/
theorem hasDerivAt_hgSum (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (hgSum a m) (powerSum (hgCoef1 a m) x) x :=
  hasDerivAt_powerSum zero_le_one (hgCoef_bound a m) hx

/-- Growth bound of the first derivative coefficients. -/
lemma hgCoef1_bound (a : ℂ) (m n : ℕ) :
    ‖hgCoef1 a m n‖ ≤ (1 * 2 ^ (2 * max ‖a‖ 1)) * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1 + 1) :=
  deriv_coeff_bound (by positivity) zero_le_one (hgCoef_bound a m) n

/-- `G'' = Σ (n+1)(n+2) γ_{n+2} xⁿ`. -/
theorem hasDerivAt_hgSum1 (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (powerSum (hgCoef1 a m)) (powerSum (hgCoef2 a m) x) x :=
  hasDerivAt_powerSum (by positivity) (hgCoef1_bound a m) hx

/-- Polynomially bounded coefficient sequences. -/
def PB (c : ℕ → ℂ) : Prop := ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ K

lemma PB.add {c d : ℕ → ℂ} (hc : PB c) (hd : PB d) : PB fun n => c n + d n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  obtain ⟨D, L, hD, hL, hdb⟩ := hd
  refine ⟨C + D, max K L, by positivity, le_max_of_le_left hK, fun n => ?_⟩
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  calc ‖c n + d n‖ ≤ ‖c n‖ + ‖d n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ K + D * ((n : ℝ) + 1) ^ L := add_le_add (hcb n) (hdb n)
    _ ≤ C * ((n : ℝ) + 1) ^ (max K L) + D * ((n : ℝ) + 1) ^ (max K L) :=
        add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)) hC)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (le_max_right _ _)) hD)
    _ = (C + D) * ((n : ℝ) + 1) ^ (max K L) := by ring

lemma PB.const_mul {c : ℕ → ℂ} (r : ℂ) (hc : PB c) : PB fun n => r * c n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨‖r‖ * C, K, by positivity, hK, fun n => ?_⟩
  rw [norm_mul]
  calc ‖r‖ * ‖c n‖ ≤ ‖r‖ * (C * ((n : ℝ) + 1) ^ K) := mul_le_mul_of_nonneg_left (hcb n) (norm_nonneg _)
    _ = ‖r‖ * C * ((n : ℝ) + 1) ^ K := by ring

lemma PB.mul_nat {c : ℕ → ℂ} (hc : PB c) : PB fun n => (n : ℂ) * c n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨C, K + 1, hC, by linarith, fun n => ?_⟩
  rw [norm_mul]
  have h1 : ‖(n : ℂ)‖ = n := by simp
  rw [h1, Real.rpow_add (by positivity), Real.rpow_one]
  calc (n : ℝ) * ‖c n‖ ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) ^ K) :=
        mul_le_mul (by linarith) (hcb n) (norm_nonneg _) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ K * ((n : ℝ) + 1)) := by ring

lemma PB.shift {c : ℕ → ℂ} (hc : PB c) : PB fun n => c (n + 1) := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  refine ⟨C * 2 ^ K, K, by positivity, hK, fun n => ?_⟩
  have h2 : (((n + 1 : ℕ) : ℝ) + 1) ^ K ≤ 2 ^ K * ((n : ℝ) + 1) ^ K := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ hK
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖c (n + 1)‖ ≤ C * (((n + 1 : ℕ) : ℝ) + 1) ^ K := hcb (n + 1)
    _ ≤ C * (2 ^ K * ((n : ℝ) + 1) ^ K) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * 2 ^ K * ((n : ℝ) + 1) ^ K := by ring

lemma PB.summable {c : ℕ → ℂ} (hc : PB c) {t : ℝ} (ht : |t| < 1) : Summable fun n : ℕ => c n * (t : ℂ) ^ n := by
  obtain ⟨C, K, hC, hK, hcb⟩ := hc
  exact summable_powerTerms hC hcb ht

end Lightlike.Dirac
