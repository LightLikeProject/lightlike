import Lightlike.TuraevViro.SMatrix

/-!
# Orthogonality of the S matrix of SU(2) at level `r - 2` (QU3, G3-202)

The discrete sine orthogonality `Σ_{x=1}^{r-1} sin(π a x/r) sin(π b x/r) = (r/2) δ_{ab}` for `1 ≤ a, b ≤ r - 1`
(`sum_sin_mul_sin_orth`), from the closed form of the cosine sum (`sum_cos_nat_mul`, a telescoping sum, no complex
exponentials), and from it `S² = 1` for the S matrix (`sMat_mul_self`); `S` is symmetric (`sMat_comm`), so it is an
orthogonal matrix and, SU(2) being self-conjugate, `S² = 1` is the charge conjugation.
-/

open Finset Real

namespace Lightlike.TV

/-- Telescoping: `2 sin(φ/2) Σ_{x<n} cos(xφ) = sin((n - 1/2)φ) + sin(φ/2)`. -/
lemma two_sin_mul_sum_cos (φ : ℝ) (n : ℕ) :
    2 * sin (φ / 2) * ∑ x ∈ range n, cos ((x : ℝ) * φ) = sin (((n : ℝ) - 1 / 2) * φ) + sin (φ / 2) := by
  have h : ∀ x : ℕ, 2 * sin (φ / 2) * cos ((x : ℝ) * φ) =
      sin ((((x + 1 : ℕ) : ℝ) - 1 / 2) * φ) - sin (((x : ℝ) - 1 / 2) * φ) := by
    intro x
    have e1 : (((x + 1 : ℕ) : ℝ) - 1 / 2) * φ = (x : ℝ) * φ + φ / 2 := by push_cast; ring
    have e2 : ((x : ℝ) - 1 / 2) * φ = (x : ℝ) * φ - φ / 2 := by ring
    rw [e1, e2, sin_add, sin_sub]; ring
  rw [mul_sum, sum_congr rfl fun x _ => h x,
    sum_range_sub (fun x : ℕ => sin (((x : ℝ) - 1 / 2) * φ))]
  have : sin ((((0 : ℕ) : ℝ) - 1 / 2) * φ) = - sin (φ / 2) := by
    rw [show (((0 : ℕ) : ℝ) - 1 / 2) * φ = -(φ / 2) by push_cast; ring, sin_neg]
  rw [this]; ring

/-- The cosine sum over a full period: `Σ_{x<r} cos(k π x / r) = (1 - (-1)^k)/2` for `0 < k < 2r`. -/
lemma sum_cos_nat_mul {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hk2 : k < 2 * r) :
    ∑ x ∈ range r, cos ((x : ℝ) * ((k : ℝ) * π / r)) = (1 - (-1) ^ k) / 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set φ : ℝ := (k : ℝ) * π / r with hφ
  have hs : sin (φ / 2) ≠ 0 := by
    have h1 : 0 < φ / 2 := by positivity
    have h2 : φ / 2 < π := by
      rw [hφ, div_div, div_lt_iff₀ (by positivity)]
      have : (k : ℝ) < 2 * r := by exact_mod_cast hk2
      nlinarith [pi_pos]
    exact (sin_pos_of_pos_of_lt_pi h1 h2).ne'
  have key := two_sin_mul_sum_cos φ r
  have e : ((r : ℝ) - 1 / 2) * φ = (k : ℝ) * π - φ / 2 := by
    rw [hφ]; field_simp
  rw [e, sin_sub, sin_nat_mul_pi, cos_nat_mul_pi] at key
  apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hs)
  rw [key]; ring

/-- Orthogonality for `a > b`. -/
lemma sum_sin_mul_sin_gt {r a b : ℕ} (hr : 0 < r) (hb : 0 < b) (hab : b < a) (ha2 : a < r) :
    ∑ x ∈ range r, sin ((x : ℝ) * ((a : ℝ) * π / r)) * sin ((x : ℝ) * ((b : ℝ) * π / r)) = 0 := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 := sum_cos_nat_mul hr (k := a - b) (by omega) (by omega)
  have h2 := sum_cos_nat_mul hr (k := a + b) (by omega) (by omega)
  have hterm : ∀ x : ℕ, sin ((x : ℝ) * ((a : ℝ) * π / r)) * sin ((x : ℝ) * ((b : ℝ) * π / r)) =
      (cos ((x : ℝ) * (((a - b : ℕ) : ℝ) * π / r)) - cos ((x : ℝ) * (((a + b : ℕ) : ℝ) * π / r))) / 2 := by
    intro x
    rw [sin_mul_sin' ]
    congr 2
    · congr 1; rw [Nat.cast_sub hab.le]; field_simp
    · congr 1; push_cast; field_simp
  rw [sum_congr rfl fun x _ => hterm x, ← sum_div, sum_sub_distrib, h1, h2]
  have : (-1 : ℝ) ^ (a - b) = (-1) ^ (a + b) := by
    rw [show a + b = (a - b) + 2 * b by omega, pow_add, pow_mul]; simp
  rw [this]; ring

/-- **Discrete sine orthogonality**: `Σ_{x<r} sin(a π x/r) sin(b π x/r) = (r/2) δ_{ab}` for `0 < a, b < r`. -/
theorem sum_sin_mul_sin_orth {r a b : ℕ} (hr : 0 < r) (ha : 0 < a) (ha2 : a < r) (hb : 0 < b) (hb2 : b < r) :
    ∑ x ∈ range r, sin ((x : ℝ) * ((a : ℝ) * π / r)) * sin ((x : ℝ) * ((b : ℝ) * π / r)) =
      if a = b then (r : ℝ) / 2 else 0 := by
  rcases lt_trichotomy a b with h | h | h
  · rw [if_neg h.ne]
    have := sum_sin_mul_sin_gt hr ha h hb2
    rw [← this]; exact sum_congr rfl fun x _ => mul_comm _ _
  · subst h
    rw [if_pos rfl]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2 := sum_cos_nat_mul hr (k := 2 * a) (by omega) (by omega)
    have hterm : ∀ x : ℕ, sin ((x : ℝ) * ((a : ℝ) * π / r)) * sin ((x : ℝ) * ((a : ℝ) * π / r)) =
        (1 - cos ((x : ℝ) * (((2 * a : ℕ) : ℝ) * π / r))) / 2 := by
      intro x
      have e : (x : ℝ) * (((2 * a : ℕ) : ℝ) * π / r) = 2 * ((x : ℝ) * ((a : ℝ) * π / r)) := by
        push_cast; ring
      rw [← sq, sin_sq_eq_half_sub, e]; ring
    rw [sum_congr rfl fun x _ => hterm x, ← sum_div, sum_sub_distrib, h2]
    simp [pow_mul]
  · rw [if_neg h.ne']
    exact sum_sin_mul_sin_gt hr hb h ha2

/-- **`S² = 1`** for the S matrix of SU(2) at level `r - 2`: `Σ_c S_{ac} S_{cb} = δ_{ab}`. -/
theorem sMat_mul_self {r a b : ℕ} (hr : 2 ≤ r) (ha : a ≤ r - 2) (hb : b ≤ r - 2) :
    ∑ c ∈ range (r - 1), sMat r a c * sMat r c b = if a = b then 1 else 0 := by
  have hr0 : 0 < r := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have horth := sum_sin_mul_sin_orth hr0 (a := a + 1) (b := b + 1) (by omega) (by omega) (by omega) (by omega)
  have hr1 : r - 1 + 1 = r := by omega
  have hrange : range r = range (r - 1 + 1) := by rw [hr1]
  rw [hrange, sum_range_succ'] at horth
  simp only [Nat.cast_zero, zero_mul, sin_zero, mul_zero, add_zero] at horth
  have hsq : Real.sqrt (2 / r) * Real.sqrt (2 / r) = 2 / r := Real.mul_self_sqrt (by positivity)
  have hterm : ∀ c : ℕ, sMat r a c * sMat r c b =
      (2 / r) * (sin (((c + 1 : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ) * π / r)) *
        sin (((c + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ) * π / r))) := by
    intro c
    unfold sMat
    have e1 : ((a + 1 : ℕ) : ℝ) * ((c + 1 : ℕ) : ℝ) * π / r = ((c + 1 : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ) * π / r) := by ring
    have e2 : ((c + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) * π / r = ((c + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ) * π / r) := by ring
    rw [e1, e2]
    calc _ = (Real.sqrt (2 / r) * Real.sqrt (2 / r)) * (sin (((c + 1 : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ) * π / r)) *
        sin (((c + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ) * π / r))) := by ring
      _ = _ := by rw [hsq]
  rw [sum_congr rfl fun c _ => hterm c, ← mul_sum, horth]
  by_cases hab : a = b
  · subst hab; simp; omega
  · have : a + 1 ≠ b + 1 := fun h => hab (by omega)
    simp [hab, this]

end Lightlike.TV
