import Lightlike.TuraevViro.Reflect.JacksonWZ

/-!
# The partial sums of Jackson's series when a parameter equals `a q^{n+1}`

In `jackson_sum` the parameter `b` may equal `a q^{n+1}` (the case `j₁ + j₂ = j₄ + j₅` of the
q-6j boundary evaluation), where the hypotheses of the theorem fail: a numerator and a denominator
vanish together at index `n`. For `k ≤ n` the factors then cancel, and the term of the series is
`tDeg q a c k = (1 - a q^{2k})/(1 - a) · (a, c; q)_k / (q, aq/c; q)_k · c^{-k}`. Its partial sums
have the closed form `sDeg q a c n = (aq, cq; q)_n / ((q, aq/c; q)_n c^n)`, which is proved here by
induction, with no limit argument: `sDeg (n + 1) - sDeg n` is `tDeg (n + 1)` by one rational
identity (with `X = q^{n+1}`: `(1 - aX)(1 - cX) - (1 - X)(c - aX) = (1 - c)(1 - aX²)`).

The formula is the limit of Jackson's sum (DLMF §17.7(iii), equation (17.7.16)) as `b → a q^{n+1}`,
checked numerically; the proof here does not use that limit.

## Main results

* `tDeg_sum`: for `n ≤ N`, the sum of `tDeg q a c k` over `k ≤ n` is `sDeg q a c n`, when
  `1 - q · q^i` and `1 - aq/c · q^i` do not vanish for `i < N`.

## References

* DLMF §17.7(iii), equation (17.7.16).
-/

namespace Lightlike.TV.Refl
open Finset

/-- The term `(1 - a q^{2k})/(1 - a) · (a, c; q)_k / (q, aq/c; q)_k · c^{-k}` of the very-well-poised
series that remains when, in Jackson's series, `b = a q^{n+1}`: then `(b; q)_k` cancels against
`(a q^{n+1}; q)_k` and `(q^{-n}; q)_k` against `(aq/b; q)_k` for `k ≤ n`. -/
noncomputable def tDeg (q a c : ℂ) (k : ℕ) : ℂ :=
  (1 - a * q ^ (2 * k)) / (1 - a) * (pk a q k * pk c q k) / (pk q q k * pk (a * q / c) q k) *
    (c⁻¹) ^ k

/-- The closed form `(aq, cq; q)_n / ((q, aq/c; q)_n c^n)` of the partial sums of `tDeg`. -/
noncomputable def sDeg (q a c : ℂ) (n : ℕ) : ℂ :=
  pk (a * q) q n * pk (c * q) q n / (pk q q n * pk (a * q / c) q n * c ^ n)

/-- One step of the telescoping: `sDeg n + tDeg (n + 1) = sDeg (n + 1)`. -/
theorem sDeg_succ {q a c : ℂ} {n : ℕ} (hq : q ≠ 0) (hc : c ≠ 0) (ha : 1 - a ≠ 0)
    (h1 : pk q q n ≠ 0) (h2 : pk (a * q / c) q n ≠ 0)
    (e1 : 1 - q * q ^ n ≠ 0) (e2 : 1 - a * q / c * q ^ n ≠ 0) :
    sDeg q a c n + tDeg q a c (n + 1) = sDeg q a c (n + 1) := by
  have hA : pk a q (n + 1) = pk (a * q) q n * (1 - a) := by
    have := pk_mul_q a q n; rw [pk]; linear_combination (-1 : ℂ) * this
  have hC : pk c q (n + 1) = pk (c * q) q n * (1 - c) := by
    have := pk_mul_q c q n; rw [pk]; linear_combination (-1 : ℂ) * this
  have hQ : pk q q (n + 1) = pk q q n * (1 - q * q ^ n) := rfl
  have hD : pk (a * q / c) q (n + 1) = pk (a * q / c) q n * (1 - a * q / c * q ^ n) := rfl
  have hA' : pk (a * q) q (n + 1) = pk (a * q) q n * (1 - a * q * q ^ n) := rfl
  have hC' : pk (c * q) q (n + 1) = pk (c * q) q n * (1 - c * q * q ^ n) := rfl
  have h2k : q ^ (2 * (n + 1)) = q ^ n * q ^ n * q * q := by ring
  unfold sDeg tDeg
  rw [hA, hC, hQ, hD, hA', hC', h2k, inv_pow, pow_succ c n]
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  generalize c ^ n = Cn at hcn ⊢
  generalize q ^ n = X at e1 e2 ⊢
  have hE : 1 - a * q / c * X = (c - a * q * X) / c := by field_simp
  have e2' : c - a * q * X ≠ 0 := by
    intro h; apply e2; rw [hE, h, zero_div]
  rw [hE]
  generalize pk (a * q) q n = P
  generalize pk (c * q) q n = Cc
  generalize pk q q n = Q1 at h1 ⊢
  generalize pk (a * q / c) q n = D at h2 ⊢
  have hprod : -(a * X * q) + a * X ^ 2 * q ^ 2 - X * q * c + c ≠ 0 := by
    have := mul_ne_zero e1 e2'
    intro h; apply this; linear_combination h
  have e1c : 1 - X * q ≠ 0 := by rwa [mul_comm X q]
  have e2c : c - a * X * q ≠ 0 := by
    have : a * X * q = a * q * X := by ring
    rwa [this]
  field_simp
  ring

/-- The partial sums of the degenerate series: `∑_{k ≤ n} tDeg = sDeg n`, for `n ≤ N`, when the
factors `1 - q·q^i` and `1 - aq/c·q^i` do not vanish for `i < N`. -/
theorem tDeg_sum {q a c : ℂ} {N : ℕ} (hq : q ≠ 0) (hc : c ≠ 0) (ha : 1 - a ≠ 0)
    (h : ∀ i < N, 1 - q * q ^ i ≠ 0 ∧ 1 - a * q / c * q ^ i ≠ 0) :
    ∀ n ≤ N, ∑ k ∈ range (n + 1), tDeg q a c k = sDeg q a c n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [tDeg, sDeg, pk, ha]
  | succ n ih =>
    intro hn
    rw [sum_range_succ, ih (by omega)]
    exact sDeg_succ hq hc ha
      (pk_ne_zero q q n fun i hi => (h i (by omega)).1)
      (pk_ne_zero (a * q / c) q n fun i hi => (h i (by omega)).2)
      (h n (by omega)).1 (h n (by omega)).2

end Lightlike.TV.Refl
