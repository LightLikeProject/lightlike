import Lightlike.TuraevViro.Reflect.JacksonWZ
import Lightlike.TuraevViro.Reflect.RacahDc
import Lightlike.TuraevViro.Reflect.SixJNormOne

/-!
# Steps toward the boundary evaluation `QDougall` from Jackson's sum

The boundary evaluation `QDougall` is the weighted norm of the column of the lowest sixth colour of
the q-6j matrix. At that colour the q-Racah sum has one term (`Sj_single`), so the weighted terms are
products of quantum factorials, and Jackson's terminating very-well-poised sum evaluates their sum
once the terms are matched with its summand `Tj` at `Q = uC r ^ 2`. This file holds the first two
ingredients of that matching.

## Main results

* `one_sub_Q_zpow`: `1 - Q^m = - u^m (u^m - u^{-m})`, so every factor `1 - Q^m` of the series is a
  bracket `bk (uC r ^ m)` times a power of `u`, and `bk (uC r ^ m) / (u - u⁻¹)` is the quantum
  integer `qZ r m` (`bk_uC_div`).
* `Tj_succ`: the ratio of consecutive Jackson summands, when the denominators do not vanish.
* `one_sub_Q_ne`: `1 - Q^m ≠ 0` unless `r ∣ m`.
* `jhypT_of_exponents`: the sharper hypotheses `JHypT` of Jackson's sum for `Q`-powers, from
  inequalities between the exponents.
* `qd_jhyp`: they hold at the parameters of the boundary evaluation in the case `x0 = j1 - j2`,
  `q0 = j1 - j5`, `j4 + j5 < j1 + j2`, for admissible spins.

## Implementation notes

The matching itself (the terms of `QDougall` as a constant times `Tj`) is not in this file; it is
checked numerically by `scripts/qracah/qd_map_check.py`.
-/

namespace Lightlike.TV.Refl
open Finset

/-- `1 - Q^m = - u^m (u^m - u^{-m})` with `Q = u²`: the factors of Jackson's series are brackets. -/
lemma one_sub_Q_zpow (r : ℕ) (m : ℤ) :
    1 - (uC r ^ 2) ^ m = - uC r ^ m * bk (uC r ^ m) := by
  have hu : uC r ^ m ≠ 0 := zpow_ne_zero m (uC_ne_zero r)
  have h2 : (uC r ^ 2) ^ m = (uC r ^ m) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [h2, bk]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- One step of the Jackson summand, when the denominators involved do not vanish. -/
lemma Tj_succ {q a b c x : ℂ} (k : ℕ) (ha : 1 - a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h0 : 1 - a * q ^ (2 * k) ≠ 0)
    (hq : pk q q k ≠ 0) (hb' : pk (a * q / b) q k ≠ 0) (hc' : pk (a * q / c) q k ≠ 0)
    (hx : pk (a * q * x) q k ≠ 0)
    (e1 : 1 - q * q ^ k ≠ 0) (e2 : 1 - a * q / b * q ^ k ≠ 0) (e3 : 1 - a * q / c * q ^ k ≠ 0)
    (e4 : 1 - a * q * x * q ^ k ≠ 0) :
    Tj q a b c x (k + 1) = Tj q a b c x k *
      ((1 - a * q ^ (2 * (k + 1))) / (1 - a * q ^ (2 * k)) *
        ((1 - a * q ^ k) * (1 - b * q ^ k) * (1 - c * q ^ k) * (1 - x⁻¹ * q ^ k)) /
        ((1 - q * q ^ k) * (1 - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
          (1 - a * q * x * q ^ k)) * (a * q * x / (b * c))) := by
  have hP : ∀ z : ℂ, pk z q (k + 1) = pk z q k * (1 - z * q ^ k) := fun z => rfl
  have h2k : q ^ (2 * (k + 1)) = (q ^ k) ^ 2 * q ^ 2 := by ring
  have h2k' : q ^ (2 * k) = (q ^ k) ^ 2 := by ring
  rw [h2k'] at h0
  simp only [Tj, hP, pow_succ (a * q * x / (b * c)) k, h2k, h2k']
  generalize pk a q k = A
  generalize pk b q k = B
  generalize pk c q k = C
  generalize pk x⁻¹ q k = X
  generalize pk q q k = P1 at hq ⊢
  generalize pk (a * q / b) q k = P2 at hb' ⊢
  generalize pk (a * q / c) q k = P3 at hc' ⊢
  generalize pk (a * q * x) q k = P4 at hx ⊢
  generalize (a * q * x / (b * c)) ^ k = W
  generalize a * q * x / (b * c) = Z
  generalize q ^ k = m at *
  generalize a * q / b = ab at *
  generalize a * q / c = ac at *
  generalize x⁻¹ = xi at *
  generalize hD1 : 1 - a * m ^ 2 = D0 at h0 ⊢
  generalize hD2 : 1 - q * m = D1 at e1 ⊢
  generalize hD3 : 1 - ab * m = D2 at e2 ⊢
  generalize hD4 : 1 - ac * m = D3 at e3 ⊢
  generalize hD5 : 1 - a * q * x * m = D4 at e4 ⊢
  field_simp


/-- `1 - Q^m` does not vanish when `r` does not divide `m` (`Q = u²`, `u = e^{iπ/r}`). -/
lemma one_sub_Q_ne {r : ℕ} (hr : 2 ≤ r) {m : ℤ} (hm : ¬ (r : ℤ) ∣ m) :
    1 - (uC r ^ 2) ^ m ≠ 0 := by
  rw [one_sub_Q_zpow]
  exact mul_ne_zero (neg_ne_zero.2 (zpow_ne_zero m (uC_ne_zero r))) (bk_uC_ne hr hm)

/-- A shifted ratio of powers of `Q` is one power. -/
lemma Qpow_ratio (Q : ℂ) (hQ : Q ≠ 0) (p s i : ℕ) :
    Q ^ p * Q / Q ^ s * Q ^ i = Q ^ ((p : ℤ) + 1 - s + i) := by
  rw [show ((p : ℤ) + 1 - s + i) = (p : ℤ) + 1 + i - s by ring, zpow_sub₀ hQ, zpow_natCast]
  rw [show ((p : ℤ) + 1 + i) = ((p + 1 + i : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  field_simp
  ring

/-- `JHypT` for `a = Q^ea`, `b = Q^eb`, `c = Q^ec` with `Q = uC r ^ 2`, from inequalities between the
exponents: all of them keep every exponent of `Q` strictly between `-r` and `r`, away from `0`. -/
theorem jhypT_of_exponents {r : ℕ} (hr : 2 ≤ r) {ea eb ec n : ℕ}
    (h1 : n + 1 < r) (h2 : 0 < ea) (h3 : ea < r)
    (hb : ea + 1 + n < eb) (hb' : eb ≤ ea + r)
    (hc : ec ≤ ea) (hc' : ea + 1 + n - ec < r) (hc'' : ec ≤ ea + 1)
    (h5 : ea + 2 * n < r) :
    JHypT (uC r ^ 2) ((uC r ^ 2) ^ ea) ((uC r ^ 2) ^ eb) ((uC r ^ 2) ^ ec) n := by
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have ne : ∀ m : ℤ, 0 < m → m < r → 1 - (uC r ^ 2) ^ m ≠ 0 := fun m h0 h1 =>
    one_sub_Q_ne hr (fun hd => by
      obtain ⟨t, ht⟩ := hd
      rcases lt_trichotomy t 0 with h | h | h <;> nlinarith [show (0:ℤ) < r by omega])
  have neg : ∀ m : ℤ, m < 0 → -(r : ℤ) < m → 1 - (uC r ^ 2) ^ m ≠ 0 := fun m h0 h1 =>
    one_sub_Q_ne hr (fun hd => by
      obtain ⟨t, ht⟩ := hd
      rcases lt_trichotomy t 0 with h | h | h <;> nlinarith [show (0:ℤ) < r by omega])
  have e1 : ∀ i : ℕ, 1 - (uC r ^ 2) * (uC r ^ 2) ^ i = 1 - (uC r ^ 2) ^ ((1 + i : ℕ) : ℤ) := by
    intro i; rw [zpow_natCast, pow_add, pow_one]
  have hpowQ : ∀ e : ℕ, (uC r ^ 2) ^ e = (uC r ^ 2) ^ (e : ℤ) := fun e => (zpow_natCast _ e).symm
  have e4 : ∀ m i : ℕ, (uC r ^ 2) ^ ea * (uC r ^ 2) * (uC r ^ 2) ^ m * (uC r ^ 2) ^ i =
      (uC r ^ 2) ^ ((ea + 1 + m + i : ℕ) : ℤ) := by
    intro m i; rw [zpow_natCast]; ring
  have e5 : ∀ (e m : ℕ), (uC r ^ 2) ^ ea * (uC r ^ 2) * (uC r ^ 2) ^ m / (uC r ^ 2) ^ e =
      (uC r ^ 2) ^ ((ea : ℤ) + 1 - e + m) := by
    intro e m
    rw [← Qpow_ratio _ hQ ea e m]; field_simp
  unfold JHypT
  refine ⟨hQ, pow_ne_zero _ hQ, pow_ne_zero _ hQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpowQ]; exact ne ea (by exact_mod_cast h2) (by exact_mod_cast h3)
  · intro i hi; rw [e1]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro i hi; rw [Qpow_ratio _ hQ]; exact neg _ (by omega) (by omega)
  · intro i hi; rw [Qpow_ratio _ hQ]; exact ne _ (by omega) (by omega)
  · intro m hm i hi; rw [e4]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro m hm
    constructor
    · rw [e5]; exact neg _ (by omega) (by omega)
    · rw [e5]; exact ne _ (by omega) (by omega)

/-- **Step B.** In the case `x0 = j1 - j2`, `q0 = j1 - j5`, with `j4 + j5 < j1 + j2`, the sharper
nonvanishing hypotheses `JHypT` of Jackson's sum hold at the parameters of the boundary evaluation:
`Q = uC r ^ 2`, `a = Q^(x0+1)`, `b = Q^(j1+2)`, `c = Q^((x0+j4-j5)/2+1)`, `n = (j4+j5-x0)/2`. -/
theorem qd_jhyp {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hnd : j4 + j5 < j1 + j2) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    JHypT (uC r ^ 2) ((uC r ^ 2) ^ (j1 - j2 + 1))
      ((uC r ^ 2) ^ ((j1 + j2 + (j1 - j2)) / 2 + 2))
      ((uC r ^ 2) ^ ((j1 - j2 + j4 - j5) / 2 + 1)) n := by
  have A0 := hadmX 0 (by omega)
  have An := hadmX n le_rfl
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨⟨hqn, h21', h22, h23⟩, hsn⟩ := An.2
  have e : (j1 + j2 + (j1 - j2)) / 2 + 2 = j1 + 2 := by omega
  rw [e]
  exact jhypT_of_exponents hr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

end Lightlike.TV.Refl
