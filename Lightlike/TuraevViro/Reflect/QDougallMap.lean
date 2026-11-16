import Lightlike.TuraevViro.Reflect.JacksonWZ
import Lightlike.TuraevViro.Reflect.RacahDc
import Lightlike.TuraevViro.Reflect.SixJNormOne
import Lightlike.TuraevViro.Reflect.SixJSingle

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
* `Sj_val`, `Sj_val_succ`: the single term of `Sj` at the lowest sixth colour `j1 - j5`, as a signed
  product of inverse quantum factorials, and its step in the third colour.
* `wTerm`, `wTerm_succ`: the weighted term of the boundary evaluation and its step, a product of
  quantum integers (cross-multiplied).
* `one_sub_Q_qZ`, `rhoT_eq`: each factor `1 - Q^m` is `- u^m (u - u⁻¹) [m]`, and the ratio factor of
  consecutive Jackson summands at the parameters of the boundary evaluation is the ratio of quantum
  integers by which `wTerm` steps.
* `wTerm_eq_Tj` (the map): in the case `x0 = j1 - j2`, `q0 = j1 - j5`, `j4 + j5 < j1 + j2`, the
  weighted terms are the first term times the summand `Tj` of Jackson's series.
* `pk_Q_zpow`, `prod_qnum`, `prod_qZ_neg`, `jacksonRhs_val`: Jackson's right side at the parameters of
  the boundary evaluation is a ratio of quantum factorials.
* `prod_identity`: the weight of the lowest column, the first weighted term and Jackson's right side
  multiply to `1`; every quantum factorial cancels.
* `qDougall_nondeg`: **`QDougall` holds** in the case `x0 = j1 - j2`, `q0 = j1 - j5`,
  `j4 + j5 < j1 + j2`, for admissible spins, from Jackson's sum (`jackson_sumT`).
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

-- 400000 heartbeats: the default 200000 is not enough.
set_option maxHeartbeats 400000 in
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


/-- `1/[m]!` at a natural number. -/
lemma invQFact_nat (r m : ℕ) : invQFact r (m : ℤ) = (qfact r m)⁻¹ := by
  simp [invQFact]

/-- The single term of `Sj` at the lowest sixth colour `j1 - j5`, for the third colour
`j1 - j2 + 2k`, as a signed product of inverse quantum factorials. -/
lemma Sj_val (r : ℕ) {j1 j2 j4 j5 k A3 S B δ γ n : ℕ} (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hA3 : 2 * A3 = j4 + j2 + (j1 - j5)) (hS : 2 * S = j4 + j5 + (j1 - j2))
    (hB : 2 * B = j1 + j2 + j4 + j5) (hδ : 2 * δ + j4 + j5 = j1 + j2)
    (hγ : 2 * γ + j2 = (j1 - j5) + j4) (hnS : S = (j1 - j2) + n) (hk : k ≤ n)
    (hA : j4 + j2 ≤ j5 + j1) :
    Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) =
      (-1) ^ (j1 + k) * qfact r (j1 + k + 1) * (qfact r k)⁻¹ * (qfact r (j1 + k - A3))⁻¹ *
        (qfact r δ)⁻¹ * (qfact r (n - k))⁻¹ * (qfact r γ)⁻¹ := by
  unfold Sj
  have e1 : (((j1 : ℤ) + j2 + ((j1 - j2 + 2 * k : ℕ) : ℤ)) / 2) = ((j1 + k : ℕ) : ℤ) := by omega
  have e2 : (((j1 : ℤ) + j5 + ((j1 - j5 : ℕ) : ℤ)) / 2) = (j1 : ℤ) := by omega
  have e3 : (((j4 : ℤ) + j2 + ((j1 - j5 : ℕ) : ℤ)) / 2) = (A3 : ℤ) := by omega
  have e4 : (((j4 : ℤ) + j5 + ((j1 - j2 + 2 * k : ℕ) : ℤ)) / 2) = ((S + k : ℕ) : ℤ) := by omega
  have e5 : (((j1 : ℤ) + j2 + j4 + j5) / 2) = (B : ℤ) := by omega
  have e6 : ((((j1 - j2 + 2 * k : ℕ) : ℤ) + j2 + j5 + ((j1 - j5 : ℕ) : ℤ)) / 2) = ((j1 + k : ℕ) : ℤ) := by
    omega
  have e7 : ((((j1 - j2 + 2 * k : ℕ) : ℤ) + j1 + ((j1 - j5 : ℕ) : ℤ) + j4) / 2) =
      ((j1 + k + γ : ℕ) : ℤ) := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  rw [SR_single (z0 := j1 + k) (by simp) (Or.inl (by simp)) (by omega)]
  have key : ∀ (m : ℕ) (a b : ℤ), a - b = (m : ℤ) → invQFact r (a - b) = (qfact r m)⁻¹ := by
    intro m a b h; rw [h, invQFact_nat]
  have q0 : qfact r 0 = 1 := by simp [qfact]
  unfold qRacahTerm
  rw [key 0 ((j1 + k : ℕ) : ℤ) ((j1 + k : ℕ) : ℤ) (by simp),
    key k ((j1 + k : ℕ) : ℤ) (j1 : ℤ) (by push_cast; omega),
    key (j1 + k - A3) ((j1 + k : ℕ) : ℤ) (A3 : ℤ) (by push_cast; omega),
    key δ ((j1 + k : ℕ) : ℤ) ((S + k : ℕ) : ℤ) (by push_cast; omega),
    key (n - k) (B : ℤ) ((j1 + k : ℕ) : ℤ) (by push_cast; omega),
    key γ ((j1 + k + γ : ℕ) : ℤ) ((j1 + k : ℕ) : ℤ) (by push_cast; omega), q0]
  simp only [inv_one, mul_one, one_mul]
  ring

/-- The weighted term of the boundary evaluation at the third colour `j1 - j2 + 2k` and the lowest
sixth colour `j1 - j5`. -/
noncomputable def wTerm (r j1 j2 j4 j5 k : ℕ) : ℝ :=
  jOmega r j1 j2 j4 j5 (j1 - j2 + 2 * k) *
    Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2

/-- The step of `Sj` from `k` to `k + 1`, cross-multiplied. -/
lemma Sj_val_succ {r : ℕ} (hr : 2 ≤ r) {j1 j2 j4 j5 k A3 S B δ γ n : ℕ} (h21 : j2 ≤ j1)
    (h51 : j5 ≤ j1) (hA3 : 2 * A3 = j4 + j2 + (j1 - j5)) (hS : 2 * S = j4 + j5 + (j1 - j2))
    (hB : 2 * B = j1 + j2 + j4 + j5) (hδ : 2 * δ + j4 + j5 = j1 + j2)
    (hγ : 2 * γ + j2 = (j1 - j5) + j4) (hnS : S = (j1 - j2) + n) (hk : k + 1 ≤ n)
    (hA : j4 + j2 ≤ j5 + j1) (hlt : j1 + k + 2 < r) (hδr : δ < r) (hγr : γ < r) (hnr : n < r) :
    Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) *
        (qnum r (k + 1) * qnum r (j1 + k + 1 - A3)) =
      - (Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) *
        (qnum r (j1 + k + 2) * qnum r (n - k))) := by
  rw [Sj_val (k := k + 1) r h21 h51 hA3 hS hB hδ hγ hnS hk hA,
    Sj_val (k := k) r h21 h51 hA3 hS hB hδ hγ hnS (by omega) hA]
  have f1 : qfact r (j1 + (k + 1) + 1) = qfact r (j1 + k + 1) * qnum r (j1 + k + 2) :=
    qfact_succ' r (j1 + k + 1)
  have f2 : qfact r (k + 1) = qfact r k * qnum r (k + 1) := qfact_succ' r k
  have f3 : qfact r (j1 + (k + 1) - A3) = qfact r (j1 + k - A3) * qnum r (j1 + k + 1 - A3) := by
    rw [show j1 + (k + 1) - A3 = (j1 + k - A3) + 1 by omega,
      show j1 + k + 1 - A3 = (j1 + k - A3) + 1 by omega]; exact qfact_succ' r _
  have f4 : qfact r (n - k) = qfact r (n - (k + 1)) * qnum r (n - k) := by
    rw [show n - k = (n - (k + 1)) + 1 by omega]; exact qfact_succ' r _
  rw [f1, f2, f3, f4]
  have p1 := qfact_pos (r := r) (n := k) hr (by omega)
  have p2 := qfact_pos (r := r) (n := j1 + k - A3) hr (by omega)
  have p3 := qfact_pos (r := r) (n := δ) hr hδr
  have p4 := qfact_pos (r := r) (n := n - (k + 1)) hr (by omega)
  have p5 := qfact_pos (r := r) (n := γ) hr hγr
  have p6 := qfact_pos (r := r) (n := j1 + k + 1) hr (by omega)
  have q1 : 0 < qnum r (k + 1) := qnum_pos hr (by omega) (by omega)
  have q2 : 0 < qnum r (j1 + k + 1 - A3) := qnum_pos hr (by omega) (by omega)
  have q3 : 0 < qnum r (n - k) := qnum_pos hr (by omega) (by omega)
  rw [show (-1 : ℝ) ^ (j1 + (k + 1)) = - (-1) ^ (j1 + k) by
    rw [show j1 + (k + 1) = (j1 + k) + 1 by ring, pow_succ]; ring]
  field_simp

/-- **The step of the weighted term**, cross-multiplied (no division): with `d = j1 - j2`,
`W(k+1) · [d+2k+1] [j2-k] [j1+k+2] [n-k] [S+k+2] [k+1]² [j1+k+1-A3]²` equals
`W(k) · [d+2k+3] [k+1] [d+k+1] [S+k+1-j4] [S+k+1-j5] [j1+k+2]² [n-k]²`. -/
theorem wTerm_succ {r : ℕ} (hr : 2 ≤ r) {j1 j2 j4 j5 k A3 S B δ γ n : ℕ} (h21 : j2 ≤ j1)
    (h51 : j5 ≤ j1) (hA3 : 2 * A3 = j4 + j2 + (j1 - j5)) (hS : 2 * S = j4 + j5 + (j1 - j2))
    (hB : 2 * B = j1 + j2 + j4 + j5) (hδ : 2 * δ + j4 + j5 = j1 + j2)
    (hγ : 2 * γ + j2 = (j1 - j5) + j4) (hnS : S = (j1 - j2) + n) (hk : k + 1 ≤ n)
    (hA : j4 + j2 ≤ j5 + j1) (hlt : j1 + k + 2 < r) (hδr : δ < r) (hγr : γ < r) (hnr : n < r)
    (a1 : qAdm r j1 j2 (j1 - j2 + 2 * k)) (a1' : qAdm r j1 j2 (j1 - j2 + 2 * (k + 1)))
    (a2 : qAdm r j4 j5 (j1 - j2 + 2 * k)) (a2' : qAdm r j4 j5 (j1 - j2 + 2 * (k + 1))) :
    wTerm r j1 j2 j4 j5 (k + 1) *
        (qnum r (j1 - j2 + 2 * k + 1) * qnum r (j2 - k) * qnum r (j1 + k + 2) * qnum r (n - k) *
          qnum r (S + k + 2) * qnum r (k + 1) ^ 2 * qnum r (j1 + k + 1 - A3) ^ 2) =
      wTerm r j1 j2 j4 j5 k *
        (qnum r (j1 - j2 + 2 * k + 3) * qnum r (k + 1) * qnum r (j1 - j2 + k + 1) *
          qnum r (S + k + 1 - j4) * qnum r (S + k + 1 - j5) * qnum r (j1 + k + 2) ^ 2 *
          qnum r (n - k) ^ 2) := by
  have st1 := qDelta_sq_step hr a1 a1'
  have st2 := qDelta_sq_step hr a2 a2'
  have sj := Sj_val_succ hr h21 h51 hA3 hS hB hδ hγ hnS hk hA hlt hδr hγr hnr
  have e1 : (j1 + j2 + (j1 - j2 + 2 * k)) / 2 = j1 + k := by omega
  have e2 : (j4 + j5 + (j1 - j2 + 2 * k)) / 2 = S + k := by omega
  rw [e1, show j1 + k - (j1 - j2 + 2 * k) = j2 - k by omega,
    show j1 + k - j1 + 1 = k + 1 by omega, show j1 + k - j2 + 1 = j1 - j2 + k + 1 by omega] at st1
  rw [e2, show S + k - (j1 - j2 + 2 * k) = n - k by omega,
    show S + k - j4 + 1 = S + k + 1 - j4 by omega,
    show S + k - j5 + 1 = S + k + 1 - j5 by omega] at st2
  have sj2 : Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) ^ 2 *
        (qnum r (k + 1) * qnum r (j1 + k + 1 - A3)) ^ 2 =
      Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2 *
        (qnum r (j1 + k + 2) * qnum r (n - k)) ^ 2 := by
    calc _ = (Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) *
          (qnum r (k + 1) * qnum r (j1 + k + 1 - A3))) ^ 2 := by ring
      _ = (-(Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) *
          (qnum r (j1 + k + 2) * qnum r (n - k)))) ^ 2 := by rw [sj]
      _ = _ := by ring
  have e : j1 - j2 + 2 * (k + 1) = j1 - j2 + 2 * k + 2 := by ring
  have q3 : qnum r (j1 - j2 + 2 * k + 2 + 1) = qnum r (j1 - j2 + 2 * k + 3) := by
    rw [show j1 - j2 + 2 * k + 2 + 1 = j1 - j2 + 2 * k + 3 by ring]
  unfold wTerm jOmega
  rw [e, q3]
  rw [e] at sj2
  set qy := qnum r (j1 - j2 + 2 * k + 1)
  set q3' := qnum r (j1 - j2 + 2 * k + 3)
  set A1 := qnum r (j2 - k)
  set A2 := qnum r (j1 + k + 2)
  set C1 := qnum r (n - k)
  set C2 := qnum r (S + k + 2)
  set B1 := qnum r (k + 1)
  set B2 := qnum r (j1 - j2 + k + 1)
  set E1 := qnum r (S + k + 1 - j4)
  set E2 := qnum r (S + k + 1 - j5)
  set F := qnum r (j1 + k + 1 - A3)
  set D1 := qDelta r j1 j2 (j1 - j2 + 2 * k) ^ 2
  set D1' := qDelta r j1 j2 (j1 - j2 + 2 * k + 2) ^ 2
  set D2 := qDelta r j4 j5 (j1 - j2 + 2 * k) ^ 2
  set D2' := qDelta r j4 j5 (j1 - j2 + 2 * k + 2) ^ 2
  set T := Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2
  set T' := Sj r j1 j2 j4 j5 (j1 - j5) ((j1 - j2 + 2 * k + 2 : ℕ) : ℤ) ^ 2
  linear_combination (q3' * qy * D2' * C1 * C2 * T' * B1 ^ 2 * F ^ 2) * st1 +
    (q3' * qy * D1 * B1 * B2 * T' * B1 ^ 2 * F ^ 2) * st2 +
    (q3' * qy * D1 * B1 * B2 * D2 * E1 * E2) * sj2


/-- The quantum integer `qZ` at a natural number is `qnum`. -/
lemma qZ_natCast (r m : ℕ) : qZ r (m : ℤ) = qnum r m := by
  simp [qZ, qnum]

/-- `qZ` is odd. -/
lemma qZ_neg (r : ℕ) (m : ℤ) : qZ r (-m) = - qZ r m := by
  simp only [qZ]; push_cast
  rw [show (-(m : ℝ)) * Real.pi / r = -((m : ℝ) * Real.pi / r) by ring, Real.sin_neg]; ring

/-- `u - u⁻¹ ≠ 0` at the root of unity. -/
lemma uC_sub_inv_ne {r : ℕ} (hr : 2 ≤ r) : uC r - (uC r)⁻¹ ≠ 0 := by
  have := bk_uC_ne hr (m := 1) (by
    intro h
    have : (r : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h
    omega)
  simpa [bk] using this

/-- Each factor of Jackson's series is a quantum integer: `1 - Q^m = - u^m (u - u⁻¹) [m]`. -/
lemma one_sub_Q_qZ {r : ℕ} (hr : 2 ≤ r) (m : ℤ) :
    1 - (uC r ^ 2) ^ m = - uC r ^ m * (uC r - (uC r)⁻¹) * ((qZ r m : ℝ) : ℂ) := by
  have h := (div_eq_iff (uC_sub_inv_ne hr)).1 (bk_uC_div hr m)
  rw [one_sub_Q_zpow, h]; ring

/-- The ratio factor of consecutive Jackson summands (`Tj_succ`) at `Q`-power parameters. -/
noncomputable def rhoT (q a b c x : ℂ) (k : ℕ) : ℂ :=
  (1 - a * q ^ (2 * (k + 1))) / (1 - a * q ^ (2 * k)) *
    ((1 - a * q ^ k) * (1 - b * q ^ k) * (1 - c * q ^ k) * (1 - x⁻¹ * q ^ k)) /
    ((1 - q * q ^ k) * (1 - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
      (1 - a * q * x * q ^ k)) * (a * q * x / (b * c))

/-- **Step C.** The ratio factor of consecutive Jackson summands at the parameters of the boundary
evaluation is the ratio of quantum integers by which the weighted terms step: the powers of `u` and
the signs of the brackets cancel. -/
theorem rhoT_eq {r : ℕ} (hr : 2 ≤ r) {d j2 n j5 k ec : ℕ} (hec : ec + j5 = d + n + 1)
    (hnj : n ≤ j5) (hj5 : j5 ≤ d + n) (hkn : k < n) (hj2 : n ≤ j2)
    (h1 : d + 2 * k + 3 < r) (h2 : j2 + d + k + 2 < r) (h3 : d + n + k + 2 < r)
    (h5 : k + j5 + 1 < r) :
    rhoT (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (j2 + d + 2)) ((uC r ^ 2) ^ ec)
        ((uC r ^ 2) ^ n) k =
      (((qnum r (d + 2 * k + 3) * qnum r (d + k + 1) * qnum r (j2 + d + k + 2) *
          qnum r (ec + k) * qnum r (n - k)) /
        (qnum r (d + 2 * k + 1) * qnum r (k + 1) * qnum r (j2 - k) * qnum r (k + j5 - n + 1) *
          qnum r (d + n + k + 2)) : ℝ) : ℂ) := by
  have hkj : k ≤ j2 := by omega
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have hu : uC r ≠ 0 := uC_ne_zero r
  have z : ∀ e : ℕ, (uC r ^ 2) ^ e = (uC r ^ 2) ^ (e : ℤ) := fun e => (zpow_natCast _ e).symm
  have p1 : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) ^ (2 * (k + 1)) = (uC r ^ 2) ^ ((d + 2 * k + 3 : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  have p2 : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) ^ (2 * k) = (uC r ^ 2) ^ ((d + 2 * k + 1 : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  have p3 : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((d + k + 1 : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  have p4 : (uC r ^ 2) ^ (j2 + d + 2) * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((j2 + d + k + 2 : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  have p5 : (uC r ^ 2) ^ ec * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((ec + k : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  have p6 : ((uC r ^ 2) ^ n)⁻¹ * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((k : ℤ) - n) := by
    rw [zpow_sub₀ hQ, zpow_natCast, zpow_natCast]; field_simp
  have p7 : (uC r ^ 2) * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((k + 1 : ℕ) : ℤ) := by
    rw [← zpow_natCast, ← pow_succ']; congr 1
  have p8 := Qpow_ratio (uC r ^ 2) hQ (d + 1) (j2 + d + 2) k
  have p9 := Qpow_ratio (uC r ^ 2) hQ (d + 1) ec k
  have p10 : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ n * (uC r ^ 2) ^ k =
      (uC r ^ 2) ^ ((d + n + k + 2 : ℕ) : ℤ) := by
    rw [zpow_natCast]; ring
  unfold rhoT
  have p11 : (uC r ^ 2) ^ (d + 1) * uC r ^ 2 * (uC r ^ 2) ^ n / ((uC r ^ 2) ^ (j2 + d + 2) * (uC r ^ 2) ^ ec) =
      (uC r ^ 2) ^ ((n : ℤ) - j2 - ec) := by
    rw [zpow_sub₀ hQ, zpow_sub₀ hQ, zpow_natCast, zpow_natCast, zpow_natCast]
    field_simp; ring
  have hbal : uC r ^ ((d + 2 * k + 3 : ℕ) : ℤ) * uC r ^ ((d + k + 1 : ℕ) : ℤ) *
      uC r ^ ((j2 + d + k + 2 : ℕ) : ℤ) * uC r ^ ((ec + k : ℕ) : ℤ) * uC r ^ (-((n - k : ℕ) : ℤ)) *
      (uC r ^ ((n : ℤ) - j2 - ec)) * uC r ^ ((n : ℤ) - j2 - ec) =
      uC r ^ ((d + 2 * k + 1 : ℕ) : ℤ) * uC r ^ ((k + 1 : ℕ) : ℤ) * uC r ^ (-((j2 - k : ℕ) : ℤ)) *
        uC r ^ ((k + j5 - n + 1 : ℕ) : ℤ) * uC r ^ ((d + n + k + 2 : ℕ) : ℤ) := by
    simp only [← zpow_add₀ hu]
    congr 1
    omega
  have hQsq : ∀ m : ℤ, (uC r ^ 2) ^ m = uC r ^ m * uC r ^ m := fun m => by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu]; congr 1; push_cast; ring
  rw [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, hQsq ((n : ℤ) - j2 - ec)]
  rw [show ((d + 1 : ℕ) : ℤ) + 1 - ((j2 + d + 2 : ℕ) : ℤ) + k = -((j2 - k : ℕ) : ℤ) by push_cast; omega,
    show ((d + 1 : ℕ) : ℤ) + 1 - ec + k = ((k + j5 - n + 1 : ℕ) : ℤ) by push_cast; omega,
    show (k : ℤ) - n = -((n - k : ℕ) : ℤ) by push_cast; omega]
  simp only [one_sub_Q_qZ hr, qZ_neg, qZ_natCast]
  have ht := uC_sub_inv_ne hr
  have qp : ∀ m : ℕ, 0 < m → m < r → ((qnum r m : ℝ) : ℂ) ≠ 0 := fun m h0 h1 =>
    Complex.ofReal_ne_zero.2 (qnum_pos hr h0 h1).ne'
  have a1 := qp (d + 2 * k + 3) (by omega) (by omega)
  have a2 := qp (d + 2 * k + 1) (by omega) (by omega)
  have a3 := qp (d + k + 1) (by omega) (by omega)
  have a4 := qp (j2 + d + k + 2) (by omega) (by omega)
  have a5 := qp (ec + k) (by omega) (by omega)
  have a6 := qp (n - k) (by omega) (by omega)
  have a7 := qp (k + 1) (by omega) (by omega)
  have a8 := qp (j2 - k) (by omega) (by omega)
  have a9 := qp (k + j5 - n + 1) (by omega) (by omega)
  have a10 := qp (d + n + k + 2) (by omega) (by omega)
  have b : ∀ m : ℤ, uC r ^ m ≠ 0 := fun m => zpow_ne_zero m hu
  have hX : uC r ^ ((n : ℤ) - j2 - ec) * uC r ^ ((n : ℤ) - j2 - ec) =
      (uC r ^ ((d + 2 * k + 1 : ℕ) : ℤ) * uC r ^ ((k + 1 : ℕ) : ℤ) * uC r ^ (-((j2 - k : ℕ) : ℤ)) *
        uC r ^ ((k + j5 - n + 1 : ℕ) : ℤ) * uC r ^ ((d + n + k + 2 : ℕ) : ℤ)) /
      (uC r ^ ((d + 2 * k + 3 : ℕ) : ℤ) * uC r ^ ((d + k + 1 : ℕ) : ℤ) *
        uC r ^ ((j2 + d + k + 2 : ℕ) : ℤ) * uC r ^ ((ec + k : ℕ) : ℤ) * uC r ^ (-((n - k : ℕ) : ℤ))) := by
    rw [eq_div_iff (by simp only [ne_eq, mul_eq_zero, b, or_self, not_false_eq_true])]
    linear_combination hbal
  have hu2 : -1 + uC r ^ 2 ≠ 0 := by
    intro h
    apply ht
    have : uC r - (uC r)⁻¹ = (uC r ^ 2 - 1) / uC r := by field_simp
    rw [this, show uC r ^ 2 - 1 = -1 + uC r ^ 2 by ring, h, zero_div]
  rw [hX]
  push_cast
  field_simp
  ring_nf
  linear_combination mul_inv_cancel₀ hu2


/-- `1 - Q^m ≠ 0` for `0 < m < r`. -/
lemma Qne_pos {r : ℕ} (hr : 2 ≤ r) {m : ℤ} (h0 : 0 < m) (h1 : m < r) : 1 - (uC r ^ 2) ^ m ≠ 0 :=
  one_sub_Q_ne hr (fun hd => by
    obtain ⟨t, ht⟩ := hd
    rcases lt_trichotomy t 0 with h | h | h <;> nlinarith [show (0:ℤ) < r by omega])

/-- `1 - Q^m ≠ 0` for `-r < m < 0`. -/
lemma Qne_neg {r : ℕ} (hr : 2 ≤ r) {m : ℤ} (h0 : m < 0) (h1 : -(r : ℤ) < m) :
    1 - (uC r ^ 2) ^ m ≠ 0 :=
  one_sub_Q_ne hr (fun hd => by
    obtain ⟨t, ht⟩ := hd
    rcases lt_trichotomy t 0 with h | h | h <;> nlinarith [show (0:ℤ) < r by omega])

/-- The nonvanishing hypotheses of `Tj_succ` at the parameters of the boundary evaluation. -/
theorem Tj_succ_hyps {r : ℕ} (hr : 2 ≤ r) {d j2 n j5 k ec : ℕ} (hec : ec + j5 = d + n + 1)
    (hnj : n ≤ j5) (hj5 : j5 ≤ d + n) (hkn : k < n) (hj2 : n ≤ j2)
    (h1 : d + 2 * k + 3 < r) (h2 : j2 + d + k + 2 < r) (h3 : d + n + k + 2 < r)
    (h5 : k + j5 + 1 < r) :
    let Q := uC r ^ 2
    1 - Q ^ (d + 1) ≠ 0 ∧ 1 - Q ^ (d + 1) * Q ^ (2 * k) ≠ 0 ∧ pk Q Q k ≠ 0 ∧
      pk (Q ^ (d + 1) * Q / Q ^ (j2 + d + 2)) Q k ≠ 0 ∧ pk (Q ^ (d + 1) * Q / Q ^ ec) Q k ≠ 0 ∧
      pk (Q ^ (d + 1) * Q * Q ^ n) Q k ≠ 0 ∧ 1 - Q * Q ^ k ≠ 0 ∧
      1 - Q ^ (d + 1) * Q / Q ^ (j2 + d + 2) * Q ^ k ≠ 0 ∧ 1 - Q ^ (d + 1) * Q / Q ^ ec * Q ^ k ≠ 0 ∧
      1 - Q ^ (d + 1) * Q * Q ^ n * Q ^ k ≠ 0 := by
  intro Q
  have hQ : Q ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have hz : ∀ e : ℕ, Q ^ e = Q ^ (e : ℤ) := fun e => (zpow_natCast _ e).symm
  have F1 : ∀ i ≤ k, 1 - Q * Q ^ i ≠ 0 := by
    intro i hi
    rw [show Q * Q ^ i = Q ^ ((1 + i : ℕ) : ℤ) by rw [zpow_natCast]; ring]
    exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  have F2 : ∀ i ≤ k, 1 - Q ^ (d + 1) * Q / Q ^ (j2 + d + 2) * Q ^ i ≠ 0 := by
    intro i hi
    rw [Qpow_ratio Q hQ]
    exact Qne_neg hr (by push_cast; omega) (by push_cast; omega)
  have F3 : ∀ i ≤ k, 1 - Q ^ (d + 1) * Q / Q ^ ec * Q ^ i ≠ 0 := by
    intro i hi
    rw [Qpow_ratio Q hQ]
    exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  have F4 : ∀ i ≤ k, 1 - Q ^ (d + 1) * Q * Q ^ n * Q ^ i ≠ 0 := by
    intro i hi
    rw [show Q ^ (d + 1) * Q * Q ^ n * Q ^ i = Q ^ ((d + n + 2 + i : ℕ) : ℤ) by rw [zpow_natCast]; ring]
    exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, F1 k le_rfl, F2 k le_rfl, F3 k le_rfl, F4 k le_rfl⟩
  · rw [hz]; exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  · rw [show Q ^ (d + 1) * Q ^ (2 * k) = Q ^ ((d + 1 + 2 * k : ℕ) : ℤ) by rw [zpow_natCast]; ring]
    exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  · exact pk_ne_zero Q Q k fun i hi => F1 i (by omega)
  · exact pk_ne_zero _ Q k fun i hi => F2 i (by omega)
  · exact pk_ne_zero _ Q k fun i hi => F3 i (by omega)
  · exact pk_ne_zero _ Q k fun i hi => F4 i (by omega)

-- 400000 heartbeats: the default 200000 is not enough.
set_option maxHeartbeats 400000 in
/-- **The map.** In the case `x0 = j1 - j2`, `q0 = j1 - j5`, `j4 + j5 < j1 + j2`, the weighted terms
of the boundary evaluation are the first term times the summand of Jackson's series at
`Q = uC r ^ 2`, `a = Q^(x0+1)`, `b = Q^(j1+2)`, `c = Q^((x0+j4-j5)/2+1)`, `x = Q^n`. -/
theorem wTerm_eq_Tj {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hnd : j4 + j5 ≤ j1 + j2) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    ∀ k ≤ n, (wTerm r j1 j2 j4 j5 k : ℂ) = (wTerm r j1 j2 j4 j5 0 : ℂ) *
      Tj (uC r ^ 2) ((uC r ^ 2) ^ (j1 - j2 + 1)) ((uC r ^ 2) ^ (j1 + 2))
        ((uC r ^ 2) ^ ((j1 - j2 + j4 - j5) / 2 + 1)) ((uC r ^ 2) ^ n) k := by
  have A0 := hadmX 0 (by omega)
  have An := hadmX n le_rfl
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨⟨hqn, h21', h22, h23⟩, hsn⟩ := An.2
  obtain ⟨⟨hpQ, hQ1, hQ2, hQ3⟩, hrQ⟩ := hadmQ.2
  obtain ⟨A3, hA3⟩ : ∃ A3, 2 * A3 = j4 + j2 + (j1 - j5) := ⟨(j4 + j2 + (j1 - j5)) / 2, by omega⟩
  obtain ⟨S, hS⟩ : ∃ S, 2 * S = j4 + j5 + (j1 - j2) := ⟨(j4 + j5 + (j1 - j2)) / 2, by omega⟩
  obtain ⟨B, hB⟩ : ∃ B, 2 * B = j1 + j2 + j4 + j5 := ⟨(j1 + j2 + j4 + j5) / 2, by omega⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, 2 * δ + j4 + j5 = j1 + j2 := ⟨(j1 + j2 - j4 - j5) / 2, by omega⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, 2 * γ + j2 = (j1 - j5) + j4 := ⟨((j1 - j5) + j4 - j2) / 2, by omega⟩
  have hnS : S = (j1 - j2) + n := by omega
  have hA : j4 + j2 ≤ j5 + j1 := by omega
  obtain ⟨_, hsum⟩ := An.1
  obtain ⟨ec, hecd⟩ : ∃ ec, ec = (j1 - j2 + j4 - j5) / 2 + 1 := ⟨_, rfl⟩
  rw [← hecd]
  have eb : (uC r ^ 2) ^ (j1 + 2) = (uC r ^ 2) ^ (j2 + (j1 - j2) + 2) := by
    congr 1; omega
  rw [eb]
  have hec : ec + j5 = (j1 - j2) + n + 1 := by omega
  have hnj : n ≤ j5 := by omega
  have hj5 : j5 ≤ (j1 - j2) + n := by omega
  have hj2 : n ≤ j2 := by omega
  intro k
  induction k with
  | zero =>
    intro _
    have ha : 1 - (uC r ^ 2) ^ (j1 - j2 + 1) ≠ 0 := by
      rw [← zpow_natCast]
      exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
    simp [Tj, pk, ha]
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have W := wTerm_succ hr h21 h51 hA3 hS hB hδ hγ hnS hk hA (by omega)
      (by omega) (by omega) (by omega) (hadmX k (by omega)).1 (hadmX (k + 1) hk).1
      (hadmX k (by omega)).2 (hadmX (k + 1) hk).2
    have hkn : k < n := by omega
    have h1 : (j1 - j2) + 2 * k + 3 < r := by omega
    have h2 : j2 + (j1 - j2) + k + 2 < r := by omega
    have h3 : (j1 - j2) + n + k + 2 < r := by omega
    have h5 : k + j5 + 1 < r := by omega
    have rt := rhoT_eq hr hec hnj hj5 hkn hj2 h1 h2 h3 h5
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := Tj_succ_hyps hr hec hnj hj5 hkn hj2 h1 h2 h3 h5
    have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
    have T := Tj_succ (q := uC r ^ 2) (a := (uC r ^ 2) ^ ((j1 - j2) + 1))
      (b := (uC r ^ 2) ^ (j2 + (j1 - j2) + 2)) (c := (uC r ^ 2) ^ ec) (x := (uC r ^ 2) ^ n) k
      c1 (pow_ne_zero _ hQ) (pow_ne_zero _ hQ) c2 c3 c4 c5 c6 c7 c8 c9 c10
    have T' : Tj (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (j2 + (j1 - j2) + 2))
        ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ n) (k + 1) =
        Tj (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (j2 + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ n) k *
        rhoT (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (j2 + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ n) k := T
    rw [show j1 + k + 2 = j2 + (j1 - j2) + k + 2 by omega,
      show S + k + 2 = (j1 - j2) + n + k + 2 by omega,
      show j1 + k + 1 - A3 = k + j5 - n + 1 by omega,
      show S + k + 1 - j4 = k + j5 - n + 1 by omega,
      show S + k + 1 - j5 = ec + k by omega] at W
    have pq : ∀ m : ℕ, 0 < m → m < r → 0 < qnum r m := fun m h0 h1 => qnum_pos hr h0 h1
    have hM : qnum r (j2 + (j1 - j2) + k + 2) * qnum r (n - k) * qnum r (k + 1) *
        qnum r (k + j5 - n + 1) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos (pq _ (by omega) (by omega)) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))) (pq _ (by omega) (by omega))).ne'
    have hden : qnum r ((j1 - j2) + 2 * k + 1) * qnum r (k + 1) * qnum r (j2 - k) *
        qnum r (k + j5 - n + 1) * qnum r ((j1 - j2) + n + k + 2) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos (mul_pos (pq _ (by omega) (by omega)) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))).ne'
    have hRatio : wTerm r j1 j2 j4 j5 (k + 1) = wTerm r j1 j2 j4 j5 k *
        ((qnum r ((j1 - j2) + 2 * k + 3) * qnum r ((j1 - j2) + k + 1) *
            qnum r (j2 + (j1 - j2) + k + 2) * qnum r (ec + k) * qnum r (n - k)) /
          (qnum r ((j1 - j2) + 2 * k + 1) * qnum r (k + 1) * qnum r (j2 - k) *
            qnum r (k + j5 - n + 1) * qnum r ((j1 - j2) + n + k + 2))) := by
      rw [mul_div_assoc', eq_div_iff hden]
      apply mul_right_cancel₀ hM
      linear_combination W
    have hc : (wTerm r j1 j2 j4 j5 (k + 1) : ℂ) = (wTerm r j1 j2 j4 j5 k : ℂ) *
        rhoT (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (j2 + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ n) k := by
      rw [rt, hRatio]; push_cast; ring
    rw [hc, ihk, T']; ring


/-- A `q`-Pochhammer symbol of a power of `Q = u²` is a product of quantum integers, up to a power
of `-(u - u⁻¹)` and a power of `u`. -/
lemma pk_Q_zpow {r : ℕ} (hr : 2 ≤ r) (e : ℤ) (n : ℕ) :
    pk ((uC r ^ 2) ^ e) (uC r ^ 2) n =
      (-(uC r - (uC r)⁻¹)) ^ n * uC r ^ (∑ i ∈ range n, (e + i)) *
        ∏ i ∈ range n, ((qZ r (e + i) : ℝ) : ℂ) := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have h1 : (uC r ^ 2) ^ e * (uC r ^ 2) ^ n = 1 - (1 - (uC r ^ 2) ^ (e + n)) := by
      rw [zpow_add₀ (pow_ne_zero 2 hu), zpow_natCast]; ring
    rw [pk, ih, h1, sub_sub_cancel, one_sub_Q_qZ hr, sum_range_succ, prod_range_succ,
      zpow_add₀ hu (∑ i ∈ range n, (e + (i : ℤ))), pow_succ]
    ring

/-- `∏_{i<n} [e+1+i] = [e+n]! / [e]!`. -/
lemma prod_qnum {r : ℕ} (e n : ℕ) (h : e + n < r) (hr : 2 ≤ r) :
    (∏ i ∈ range n, qnum r (e + 1 + i)) * qfact r e = qfact r (e + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, mul_right_comm, ih (by omega), show e + (n + 1) = (e + n) + 1 by ring,
      qfact_succ', show e + 1 + n = e + n + 1 by ring]

/-- `∏_{i<n} [-m+i] · [m-n]! = (-1)^n [m]!` for `n ≤ m`. -/
lemma prod_qZ_neg {r : ℕ} (m n : ℕ) (h : n ≤ m) (hm : m < r) :
    (∏ i ∈ range n, qZ r (-(m : ℤ) + i)) * qfact r (m - n) = (-1) ^ n * qfact r m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : qZ r (-(m : ℤ) + n) = - qnum r (m - n) := by
      rw [show -(m : ℤ) + n = -((m - n : ℕ) : ℤ) by push_cast; omega, qZ_neg, qZ_natCast]
    have f : qfact r (m - n) = qfact r (m - (n + 1)) * qnum r (m - n) := by
      rw [show m - n = (m - (n + 1)) + 1 by omega]; exact qfact_succ' r _
    have ih' := ih (by omega)
    rw [prod_range_succ, e, pow_succ]
    rw [f] at ih'
    linear_combination (-1 : ℝ) * ih'

/-- **Jackson's right side at the parameters of the boundary evaluation** is a ratio of quantum
factorials. -/
theorem jacksonRhs_val {r : ℕ} (hr : 2 ≤ r) {d j2 n j5 ec : ℕ} (hec : ec + j5 = d + n + 1)
    (hnj : n ≤ j5) (hj5 : j5 ≤ d + n) (hj2 : n ≤ j2) (hb1 : d + n + 1 < r) (hb2 : j2 + ec < r) :
    jacksonRhs (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (j2 + d + 2)) ((uC r ^ 2) ^ ec) n =
      (((qfact r (d + n + 1) / qfact r (d + 1)) * (qfact r (j2 + ec) / qfact r (j2 + ec - n)) /
        ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n))) : ℝ) : ℂ) := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have A : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) = (uC r ^ 2) ^ ((d : ℤ) + 2) := by
    rw [zpow_add₀ hQ]; rw [zpow_natCast]; simp; ring
  have B : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / ((uC r ^ 2) ^ (j2 + d + 2) * (uC r ^ 2) ^ ec) =
      (uC r ^ 2) ^ (-(j2 : ℤ) - ec) := by
    rw [show -(j2 : ℤ) - ec = -((j2 + ec : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    field_simp; ring
  have C : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / (uC r ^ 2) ^ (j2 + d + 2) =
      (uC r ^ 2) ^ (-(j2 : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    field_simp; ring
  have D : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / (uC r ^ 2) ^ ec =
      (uC r ^ 2) ^ (((j5 - n + 1 : ℕ)) : ℤ) := by
    rw [zpow_natCast, div_eq_iff (pow_ne_zero _ hQ), ← pow_succ, ← pow_add]
    congr 1; omega
  unfold jacksonRhs
  rw [B, C, D, A, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr]
  have pf : ∀ m : ℕ, m < r → 0 < qfact r m := fun m h => qfact_pos hr h
  have g1 : ∏ i ∈ range n, qZ r (((d : ℤ) + 2) + i) = qfact r (d + n + 1) / qfact r (d + 1) := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (d + 1) n (by omega) hr
    rw [show d + 1 + n = d + n + 1 by ring] at this
    rw [← this]
    congr 1
  have g4 : ∏ i ∈ range n, qZ r ((((j5 - n + 1 : ℕ)) : ℤ) + i) = qfact r j5 / qfact r (j5 - n) := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (j5 - n) n (by omega) hr
    rw [show j5 - n + n = j5 by omega] at this
    rw [← this]
    congr 1
  have g3 : ∏ i ∈ range n, qZ r (-(j2 : ℤ) + i) = (-1) ^ n * (qfact r j2 / qfact r (j2 - n)) := by
    rw [mul_div_assoc', eq_div_iff (pf _ (by omega)).ne']
    exact prod_qZ_neg j2 n (by omega) (by omega)
  have g2 : ∏ i ∈ range n, qZ r (-(j2 : ℤ) - ec + i) =
      (-1) ^ n * (qfact r (j2 + ec) / qfact r (j2 + ec - n)) := by
    rw [mul_div_assoc', eq_div_iff (pf _ (by omega)).ne']
    have := prod_qZ_neg (r := r) (j2 + ec) n (by omega) hb2
    rw [← this]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [show -(j2 : ℤ) - ec + i = -((j2 + ec : ℕ) : ℤ) + i by push_cast; ring]
  have hsum : ∀ e : ℤ, ∑ i ∈ range n, (e + (i : ℤ)) = n * e + ∑ i ∈ range n, (i : ℤ) := by
    intro e; simp [sum_add_distrib]
  have hbal : uC r ^ (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ))) *
      uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ) - ec) + (i : ℤ))) =
      uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ)) + (i : ℤ))) *
        uC r ^ (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ))) := by
    rw [← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1
    rw [hsum, hsum, hsum, hsum]
    have h1 : (ec : ℤ) = d + n + 1 - j5 := by omega
    have h2 : (((j5 - n + 1 : ℕ)) : ℤ) = j5 - n + 1 := by omega
    rw [h1, h2]; ring
  have ht := uC_sub_inv_ne hr
  have hX : (-(uC r - (uC r)⁻¹)) ^ n ≠ 0 := pow_ne_zero n (neg_ne_zero.2 ht)
  have hzp : ∀ z : ℤ, uC r ^ z ≠ 0 := fun z => zpow_ne_zero z hu
  have pos : ∀ m : ℕ, m < r → (0 : ℝ) < qfact r m := fun m h => qfact_pos hr h
  have c1 := (pos (d + n + 1) (by omega)).ne'
  have c2 := (pos (d + 1) (by omega)).ne'
  have c3 := (pos (j2 + ec) hb2).ne'
  have c4 := (pos (j2 + ec - n) (by omega)).ne'
  have c5 := (pos j2 (by omega)).ne'
  have c6 := (pos (j2 - n) (by omega)).ne'
  have c7 := (pos j5 (by omega)).ne'
  have c8 := (pos (j5 - n) (by omega)).ne'
  simp only [← Complex.ofReal_prod]
  rw [g1, g2, g3, g4]
  have z1 := hzp (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ)))
  have z2 := hzp (∑ i ∈ range n, ((-(j2 : ℤ) - ec) + (i : ℤ)))
  have z3 := hzp (∑ i ∈ range n, ((-(j2 : ℤ)) + (i : ℤ)))
  have z4 := hzp (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ)))
  have hs : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  generalize uC r ^ (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ))) = Z1 at *
  generalize uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ) - ec) + (i : ℤ))) = Z2 at *
  generalize uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ)) + (i : ℤ))) = Z3 at *
  generalize uC r ^ (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ))) = Z4 at *
  generalize (-(uC r - (uC r)⁻¹)) ^ n = X at *
  have hZ4 : Z4 = Z1 * Z2 / Z3 := by
    rw [eq_div_iff z3]; linear_combination (-1 : ℂ) * hbal
  rw [hZ4]
  push_cast
  field_simp

/-- **The product identity**, in clean parameters `j1 = j2 + d`, `j4 = d + 2n - j5`,
`q0 = j2 + d - j5`, `ec = d + n + 1 - j5`: the weight of the lowest column, the first weighted term
and Jackson's right side multiply to `1`. Every quantum factorial cancels. -/
theorem prod_identity {r : ℕ} (hr : 2 ≤ r) {d j2 n j5 : ℕ} (hnj : n ≤ j5) (hj5 : j5 ≤ d + n)
    (hj2 : n ≤ j2) (hb1 : d + n + 1 < r) (hb2 : j2 + d + n + 1 - j5 < r) (hb3 : j2 + d + 1 < r) :
    qnum r (j2 + d - j5 + 1) *
        (qfact r (j2 + d - j5) * qfact r j5 / qfact r (j2 + d + 1)) *
        (qfact r (j2 - n) * qfact r (d + n - j5) * qfact r n / qfact r (j2 + d + n + 1 - j5)) *
      (qnum r (d + 1) * (qfact r d * qfact r j2 / qfact r (j2 + d + 1)) *
        (qfact r (j5 - n) * qfact r (d + n - j5) * qfact r n / qfact r (d + n + 1)) *
        (qfact r (j2 + d + 1) /
          (qfact r (j5 - n) * qfact r (j2 - n) * qfact r n * qfact r (d + n - j5))) ^ 2) *
      ((qfact r (d + n + 1) / qfact r (d + 1)) *
        (qfact r (j2 + (d + n + 1 - j5)) / qfact r (j2 + (d + n + 1 - j5) - n)) /
        ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n)))) = 1 := by
  have pos : ∀ m : ℕ, m < r → 0 < qfact r m := fun m h => qfact_pos hr h
  have f1 : qfact r (j2 + d - j5 + 1) = qfact r (j2 + d - j5) * qnum r (j2 + d - j5 + 1) :=
    qfact_succ' r _
  have f2 : qfact r (d + 1) = qfact r d * qnum r (d + 1) := qfact_succ' r _
  have e1 : j2 + (d + n + 1 - j5) = j2 + d + n + 1 - j5 := by omega
  have e2 : j2 + d + n + 1 - j5 - n = j2 + d - j5 + 1 := by omega
  rw [e1, e2, f1, f2]
  have p1 := (pos (j2 + d - j5) (by omega)).ne'
  have p2 := (pos j5 (by omega)).ne'
  have p3 := (pos (j2 + d + 1) hb3).ne'
  have p4 := (pos (j2 - n) (by omega)).ne'
  have p5 := (pos (d + n - j5) (by omega)).ne'
  have p6 := (pos n (by omega)).ne'
  have p7 := (pos (j2 + d + n + 1 - j5) hb2).ne'
  have p8 := (pos d (by omega)).ne'
  have p9 := (pos j2 (by omega)).ne'
  have p10 := (pos (j5 - n) (by omega)).ne'
  have p11 := (pos (d + n + 1) hb1).ne'
  have q1 : 0 < qnum r (j2 + d - j5 + 1) := qnum_pos hr (by omega) (by omega)
  have q2 : 0 < qnum r (d + 1) := qnum_pos hr (by omega) (by omega)
  field_simp


/-- `qDelta²` with the arguments of the quantum factorials given as explicit numbers. -/
lemma qDelta_sq_of {r : ℕ} (hr : 2 ≤ r) {a b c : ℕ} (h : qAdm r a b c) {s x y z w : ℕ}
    (hs : 2 * s = a + b + c) (hx : x = s - a) (hy : y = s - b) (hz : z = s - c) (hw : w = s + 1) :
    qDelta r a b c ^ 2 = qfact r x * qfact r y * qfact r z / qfact r w := by
  rw [qDelta_sq hr h, show (a + b + c) / 2 = s by omega, hx, hy, hz, hw]

/-- **The boundary evaluation `QDougall`, non-degenerate case**, in the parameters
`j1 = j2 + d`, `j4 = d + 2n - j5`, third colour from `d`, lowest sixth colour `j2 + d - j5`. -/
theorem qDougall_nondeg_param {r d j2 n j5 : ℕ} (hr : 2 ≤ r) (hnj : n ≤ j5) (hj5 : j5 ≤ d + n)
    (hj2 : n < j2)
    (hadmX : ∀ k ≤ n, qAdm r (j2 + d) j2 (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (j2 + d) j5 (j2 + d - j5) ∧ qAdm r (d + 2 * n - j5) j2 (j2 + d - j5)) :
    QDougall r (j2 + d) j2 (d + 2 * n - j5) j5 d n (j2 + d - j5) := by
  have hX' : ∀ k ≤ n, qAdm r (j2 + d) j2 (j2 + d - j2 + 2 * k) ∧
      qAdm r (d + 2 * n - j5) j5 (j2 + d - j2 + 2 * k) := by
    simpa only [Nat.add_sub_cancel_left] using hadmX
  have hmap := wTerm_eq_Tj hr (j1 := j2 + d) (j2 := j2) (j4 := d + 2 * n - j5) (j5 := j5) (n := n)
    (by omega) (by omega) (by omega) (by omega) hX' hadmQ
  have jh := qd_jhyp hr (j1 := j2 + d) (j2 := j2) (j4 := d + 2 * n - j5) (j5 := j5) (n := n)
    (by omega) (by omega) (by omega) (by omega) hX' hadmQ
  have e1 : j2 + d - j2 + 1 = d + 1 := by omega
  have e2 : (j2 + d - j2 + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  have e3 : (j2 + d + j2 + (j2 + d - j2)) / 2 + 2 = j2 + d + 2 := by omega
  rw [e1, e2, e3] at jh
  have e2' : (d + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  simp only [Nat.add_sub_cancel_left, e1, e2, e2'] at hmap
  have jsum := jackson_sumT jh n le_rfl
  obtain ⟨_, bQ1⟩ := hadmQ.1
  obtain ⟨_, bQ2⟩ := hadmQ.2
  obtain ⟨_, bX⟩ := (hadmX n le_rfl).2
  have hb1 : d + n + 1 < r := by omega
  have hb2 : j2 + (d + n + 1 - j5) < r := by omega
  have hRhs := jacksonRhs_val hr (d := d) (j2 := j2) (n := n) (j5 := j5) (ec := d + n + 1 - j5)
    (by omega) hnj hj5 hj2.le hb1 hb2
  have sumC : (∑ k ∈ range (n + 1), (wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k : ℂ)) =
      (wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 0 : ℂ) *
        ((((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (j2 + (d + n + 1 - j5)) / qfact r (j2 + (d + n + 1 - j5) - n)) /
          ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n))) : ℝ)) : ℂ) := by
    rw [sum_congr rfl (fun k hk => hmap k (by simp only [mem_range] at hk; omega)), ← mul_sum,
      jsum, hRhs]
  have sumR : ∑ k ∈ range (n + 1), wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k =
      wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 0 *
        ((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (j2 + (d + n + 1 - j5)) / qfact r (j2 + (d + n + 1 - j5) - n)) /
          ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n)))) := by
    exact_mod_cast sumC
  have hS : (∑ k ∈ range (n + 1), (jOmega r (j2 + d) j2 (d + 2 * n - j5) j5 (d + 2 * k) *
      Sj r (j2 + d) j2 (d + 2 * n - j5) j5 (j2 + d - j5) ((d + 2 * k : ℕ) : ℤ) ^ 2)) =
      ∑ k ∈ range (n + 1), wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k := by
    simp only [wTerm, Nat.add_sub_cancel_left]
  unfold QDougall
  rw [hS, sumR]
  unfold wTerm jOmega
  simp only [Nat.add_sub_cancel_left, mul_zero, add_zero]
  have hA : (d + 2 * n - j5) + j2 ≤ j5 + (j2 + d) := by omega
  have hSj := Sj_val r (j1 := j2 + d) (j2 := j2) (j4 := d + 2 * n - j5) (j5 := j5) (k := 0)
    (A3 := d + n + j2 - j5) (S := d + n) (B := j2 + d + n) (δ := j2 - n) (γ := d + n - j5) (n := n)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hA
  rw [show ((j2 + d - j2 + 2 * 0 : ℕ) : ℤ) = (d : ℤ) by omega] at hSj
  rw [show j2 + d + 0 - (d + n + j2 - j5) = j5 - n by omega, show n - 0 = n by omega,
    show j2 + d + 0 + 1 = j2 + d + 1 by omega] at hSj
  have sq1 : ∀ m : ℕ, ((-1 : ℝ) ^ m) ^ 2 = 1 := fun m => by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have T1 := qDelta_sq_of hr hadmQ.1 (s := j2 + d) (x := 0) (y := j2 + d - j5) (z := j5)
    (w := j2 + d + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T2 := qDelta_sq_of hr hadmQ.2 (s := d + n + j2 - j5) (x := j2 - n) (y := d + n - j5)
    (z := n) (w := j2 + d + n + 1 - j5) (by omega) (by omega) (by omega) (by omega) (by omega)
  have X0 := hadmX 0 (by omega)
  simp only [mul_zero, add_zero] at X0
  have T3 := qDelta_sq_of hr X0.1 (s := j2 + d) (x := 0) (y := d) (z := j2)
    (w := j2 + d + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T4 := qDelta_sq_of hr X0.2 (s := d + n) (x := j5 - n) (y := d + n - j5)
    (z := n) (w := d + n + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [T1, T2, T3, T4]
  have hsqSj : Sj r (j2 + d) j2 (d + 2 * n - j5) j5 (j2 + d - j5) (d : ℤ) ^ 2 =
      (qfact r (j2 + d + 1) / (qfact r (j5 - n) * qfact r (j2 - n) * qfact r n *
        qfact r (d + n - j5))) ^ 2 := by
    rw [hSj, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, sq1]
    have q0 : qfact r 0 = 1 := by simp [qfact]
    rw [q0]; field_simp
  rw [hsqSj]
  have q0 : qfact r 0 = 1 := by simp [qfact]
  rw [q0]
  have key := prod_identity hr hnj hj5 hj2.le hb1 (by omega) (by omega)
  linear_combination key

/-- **The boundary evaluation `QDougall`, non-degenerate case, for admissible spins.** In the case
`x0 = j1 - j2`, `q0 = j1 - j5` and `j4 + j5 < j1 + j2`. -/
theorem qDougall_nondeg {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hnd : j4 + j5 < j1 + j2) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    QDougall r j1 j2 j4 j5 (j1 - j2) n (j1 - j5) := by
  have A0 := hadmX 0 (by omega)
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨d, rfl⟩ : ∃ d, j1 = j2 + d := ⟨j1 - j2, by omega⟩
  obtain rfl : j4 = d + 2 * n - j5 := by omega
  simp only [Nat.add_sub_cancel_left] at hadmX ⊢
  exact qDougall_nondeg_param hr (by omega) (by omega) (by omega) hadmX hadmQ

end Lightlike.TV.Refl
