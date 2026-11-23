import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Ring.GeomSum

/-!
# The `p`-ary tree series `B = 1 + X B^p` (G2-035)

Existence of the power series `B ∈ ℚ⟦X⟧` with `B = 1 + X · B^p`, by Picard iteration:
`iter 0 = 1`, `iter (k+1) = 1 + X · (iter k)^p`.  The step `iter (k+1) - iter k` is divisible by
`X^(k+1)`, so the coefficientwise limit exists.  This series is the generating function of rooted
`p`-ary trees counted by internal nodes; its coefficients are identified with the Fuss–Catalan numbers
in `Lightlike.Rows.G2_035` (later files).
-/

open PowerSeries

namespace Lightlike.Rows.G2_035

/-- Picard iterates of `B = 1 + X B^p`. -/
noncomputable def iter (p : ℕ) : ℕ → ℚ⟦X⟧
  | 0 => 1
  | k + 1 => 1 + X * (iter p k) ^ p

theorem X_pow_dvd_iter_succ_sub (p k : ℕ) :
    (X : ℚ⟦X⟧) ^ (k + 1) ∣ iter p (k + 1) - iter p k := by
  induction k with
  | zero =>
    have : iter p 1 - iter p 0 = X := by
      have h1 : iter p 1 = 1 + X * (iter p 0) ^ p := rfl
      have h0 : iter p 0 = 1 := rfl
      rw [h1, h0]; simp
    rw [this]; simp
  | succ k ih =>
    have h2 : iter p (k + 2) = 1 + X * (iter p (k + 1)) ^ p := rfl
    have h1 : iter p (k + 1) = 1 + X * (iter p k) ^ p := rfl
    have : iter p (k + 2) - iter p (k + 1) = X * ((iter p (k + 1)) ^ p - (iter p k) ^ p) := by
      rw [h2]; rw [h1]; ring
    rw [this, pow_succ' X (k + 1)]
    exact mul_dvd_mul_left _ (ih.trans (sub_dvd_pow_sub_pow _ _ _))

theorem X_pow_dvd_iter_sub (p k m : ℕ) (h : k ≤ m) :
    (X : ℚ⟦X⟧) ^ (k + 1) ∣ iter p m - iter p k := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have : iter p (m + 1) - iter p k = (iter p (m + 1) - iter p m) + (iter p m - iter p k) := by
      ring
    rw [this]
    exact dvd_add ((pow_dvd_pow X (by omega)).trans (X_pow_dvd_iter_succ_sub p m)) ih

/-- The limit series: `coeff n (seriesB p) = coeff n (iter p n)`. -/
noncomputable def seriesB (p : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun n => coeff n (iter p n)

theorem coeff_iter_eq (p k n : ℕ) (h : n ≤ k) : coeff n (iter p k) = coeff n (seriesB p) := by
  have hd := X_pow_dvd_iter_sub p n k h
  rw [X_pow_dvd_iff] at hd
  have := hd n (by omega)
  rw [map_sub, sub_eq_zero] at this
  simp [seriesB, this]

theorem X_pow_dvd_seriesB_sub (p k : ℕ) : (X : ℚ⟦X⟧) ^ (k + 1) ∣ seriesB p - iter p k := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, coeff_iter_eq p k m (by omega), sub_self]

/-- **Existence**: `seriesB p = 1 + X · (seriesB p)^p`. -/
theorem seriesB_eq (p : ℕ) : seriesB p = 1 + X * (seriesB p) ^ p := by
  ext n
  rcases n with _ | n
  · have := coeff_iter_eq p 0 0 le_rfl
    simp [← this, iter]
  · have hd : (X : ℚ⟦X⟧) ^ (n + 1 + 1) ∣ (1 + X * (seriesB p) ^ p) - (1 + X * (iter p n) ^ p) := by
      have : (1 + X * (seriesB p) ^ p) - (1 + X * (iter p n) ^ p)
          = X * ((seriesB p) ^ p - (iter p n) ^ p) := by ring
      rw [this, pow_succ' X (n + 1)]
      exact mul_dvd_mul_left _ ((X_pow_dvd_seriesB_sub p n).trans (sub_dvd_pow_sub_pow _ _ _))
    rw [X_pow_dvd_iff] at hd
    have h0 := hd (n + 1) (by omega)
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, ← coeff_iter_eq p (n + 1) (n + 1) le_rfl]
    rfl

/-- The constant coefficient of `seriesB p` is `1`. -/
theorem constantCoeff_seriesB (p : ℕ) : constantCoeff (seriesB p) = 1 := by
  have := congrArg (constantCoeff) (seriesB_eq p)
  simpa using this

end Lightlike.Rows.G2_035
