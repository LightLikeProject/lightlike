import Lightlike.TuraevViro.Reflect.JacksonWZ
import Lightlike.TuraevViro.Reflect.RacahDc
import Lightlike.TuraevViro.Reflect.SixJNormOne
import Lightlike.TuraevViro.Reflect.JacksonDegenerate
import Lightlike.TuraevViro.Reflect.OrthInterior
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
  `j4 + j5 < j1 + j2`, for admissible spins whose third colours run up to `j4 + j5`, from Jackson's
  sum (`jackson_sumT`).
* `Tj_eq_tDeg`, `sDeg_val`, `qDougall_deg_param`: the degenerate case `j1 + j2 = j4 + j5`, where the
  hypotheses of Jackson's sum fail, from the partial sums of the series with fewer parameters.
* `qDougall_orbit`: **`QDougall` holds** for the lowest sixth colour `j1 - j5` and the third colours
  from `j1 - j2`, in both cases, when the admissible third colours run up to `j4 + j5` (the
  hypothesis `2 * n = j4 + j5 - (j1 - j2)` with admissibility at every step). When the level cut-off
  `2 (r - 2)` ends the range earlier, this does not apply.
* `qDougallAt_dual`: the boundary evaluation for the dual data `B, F, E, A` gives the one for
  `B, A, E, F` (the weighted norms of the rows and of the columns of one matrix are equal).
* `qDougall_k1`, `qDougall_k2`, `qDougall_k3`, `qDougallAt_k1`, `qDougallAt_k2`, `qDougallAt_k3`: the
  boundary evaluation is invariant under the permutations `(j1 j4)(j2 j5)`, `(j1 j2)(j4 j5)` and
  `(j1 j5)(j2 j4)` of the four spins.
* `qDougallAt_O1`, `qDougallAt_O1_k1`, `qDougallAt_O1_k2`, `qDougallAt_O1_k3`: `QDougallAt` for the
  first orbit of the forms of the lowest colours, when the range of third colours runs up to the
  triangle top (no level cut-off), in the four forms the permutations give.
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
    (hA : j4 + j2 ≤ j5 + j1) (hlt : j1 + k + 2 < r) (hδr : δ < r) (hγr : γ < r) (hnr : n - k < r) :
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
    (hA : j4 + j2 ≤ j5 + j1) (hlt : j1 + k + 2 < r) (hδr : δ < r) (hγr : γ < r) (hnr : n - k < r)
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
/-- **The map, with the range `N ≤ n` separate from the length `n`.** (The sum may stop at `N` before the triangle top `n`, e.g. at a level cut-off.) In the case `x0 = j1 - j2`, `q0 = j1 - j5`, `j4 + j5 < j1 + j2`, the weighted terms
of the boundary evaluation are the first term times the summand of Jackson's series at
`Q = uC r ^ 2`, `a = Q^(x0+1)`, `b = Q^(j1+2)`, `c = Q^((x0+j4-j5)/2+1)`, `x = Q^n`. -/
theorem wTerm_eq_Tj_N {r j1 j2 j4 j5 n N : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hnd : j4 + j5 ≤ j1 + j2) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hN : N ≤ n)
    (hadmX : ∀ k ≤ N, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    ∀ k ≤ N, (wTerm r j1 j2 j4 j5 k : ℂ) = (wTerm r j1 j2 j4 j5 0 : ℂ) *
      Tj (uC r ^ 2) ((uC r ^ 2) ^ (j1 - j2 + 1)) ((uC r ^ 2) ^ (j1 + 2))
        ((uC r ^ 2) ^ ((j1 - j2 + j4 - j5) / 2 + 1)) ((uC r ^ 2) ^ n) k := by
  have A0 := hadmX 0 (by omega)
  have An := hadmX N le_rfl
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
    have W := wTerm_succ hr h21 h51 hA3 hS hB hδ hγ hnS (by omega) hA (by omega)
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

/-- **The map.** The case `N = n` of `wTerm_eq_Tj_N`. -/
theorem wTerm_eq_Tj {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hnd : j4 + j5 ≤ j1 + j2) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    ∀ k ≤ n, (wTerm r j1 j2 j4 j5 k : ℂ) = (wTerm r j1 j2 j4 j5 0 : ℂ) *
      Tj (uC r ^ 2) ((uC r ^ 2) ^ (j1 - j2 + 1)) ((uC r ^ 2) ^ (j1 + 2))
        ((uC r ^ 2) ^ ((j1 - j2 + j4 - j5) / 2 + 1)) ((uC r ^ 2) ^ n) k :=
  wTerm_eq_Tj_N hr h21 h51 hnd hn le_rfl hadmX hadmQ

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


/-- At `b = a q x` Jackson's summand is the term `tDeg` of the series with fewer parameters, when
the Pochhammer symbols that cancel do not vanish. -/
lemma Tj_eq_tDeg {q a c x : ℂ} (k : ℕ) (hq : q ≠ 0) (ha : a ≠ 0) (hx : x ≠ 0) (hc : c ≠ 0)
    (hP1 : pk (a * q * x) q k ≠ 0) (hP2 : pk x⁻¹ q k ≠ 0) :
    Tj q a (a * q * x) c x k = tDeg q a c k := by
  have h1 : a * q / (a * q * x) = x⁻¹ := by field_simp
  have h2 : a * q * x / (a * q * x * c) = c⁻¹ := by field_simp
  unfold Tj tDeg
  rw [h1, h2]
  generalize pk a q k = A
  generalize pk c q k = C
  generalize pk (a * q * x) q k = P1 at hP1 ⊢
  generalize pk x⁻¹ q k = P2 at hP2 ⊢
  generalize pk q q k = P3
  generalize pk (a * q / c) q k = P4
  field_simp

/-- The closed form of the degenerate partial sums at the parameters of the boundary evaluation is a
ratio of quantum factorials. -/
theorem sDeg_val {r : ℕ} (hr : 2 ≤ r) {d n j5 ec : ℕ} (hec : ec + j5 = d + n + 1) (hnj : n ≤ j5)
    (hj5 : j5 ≤ d + n) (hb1 : d + n + 1 < r) (hb2 : ec + n < r) :
    sDeg (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ ec) n =
      (((qfact r (d + n + 1) / qfact r (d + 1)) * (qfact r (ec + n) / qfact r ec) /
        (qfact r n * (qfact r j5 / qfact r (j5 - n))) : ℝ) : ℂ) := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have A : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) = (uC r ^ 2) ^ ((d : ℤ) + 2) := by
    rw [zpow_add₀ hQ, zpow_natCast]; simp; ring
  have Cq : (uC r ^ 2) ^ ec * (uC r ^ 2) = (uC r ^ 2) ^ ((ec : ℤ) + 1) := by
    rw [zpow_add₀ hQ, zpow_natCast]; simp
  have D : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / (uC r ^ 2) ^ ec =
      (uC r ^ 2) ^ (((j5 - n + 1 : ℕ)) : ℤ) := by
    rw [zpow_natCast, div_eq_iff (pow_ne_zero _ hQ), ← pow_succ, ← pow_add]
    congr 1; omega
  have E : pk (uC r ^ 2) (uC r ^ 2) n = pk ((uC r ^ 2) ^ (1 : ℤ)) (uC r ^ 2) n := by rw [zpow_one]
  have F : ((uC r ^ 2) ^ ec) ^ n = uC r ^ (((2 * ec * n : ℕ)) : ℤ) := by
    rw [zpow_natCast, ← pow_mul, ← pow_mul]; congr 1; ring
  unfold sDeg
  rw [D, A, Cq, E, F, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr]
  have pf : ∀ m : ℕ, m < r → 0 < qfact r m := fun m h => qfact_pos hr h
  have g1 : ∏ i ∈ range n, qZ r (((d : ℤ) + 2) + i) = qfact r (d + n + 1) / qfact r (d + 1) := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (d + 1) n (by omega) hr
    rw [show d + 1 + n = d + n + 1 by ring] at this
    rw [← this]
    congr 1
  have g5 : ∏ i ∈ range n, qZ r (((ec : ℤ) + 1) + i) = qfact r (ec + n) / qfact r ec := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) ec n (by omega) hr
    rw [← this]
    congr 1
  have g6 : ∏ i ∈ range n, qZ r ((1 : ℤ) + i) = qfact r n := by
    have := prod_qnum (r := r) 0 n (by omega) hr
    have q0 : qfact r 0 = 1 := by simp [qfact]
    simp only [zero_add, q0, mul_one] at this
    rw [← this]
    exact prod_congr rfl fun i _ => by
      rw [show (1 : ℤ) + i = ((1 + i : ℕ) : ℤ) by push_cast; ring, qZ_natCast]
  have g4 : ∏ i ∈ range n, qZ r ((((j5 - n + 1 : ℕ)) : ℤ) + i) = qfact r j5 / qfact r (j5 - n) := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (j5 - n) n (by omega) hr
    rw [show j5 - n + n = j5 by omega] at this
    rw [← this]
    congr 1
  have hsum : ∀ e : ℤ, ∑ i ∈ range n, (e + (i : ℤ)) = n * e + ∑ i ∈ range n, (i : ℤ) := by
    intro e; simp [sum_add_distrib]
  have hbal : uC r ^ (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ))) *
      uC r ^ (∑ i ∈ range n, (((ec : ℤ) + 1) + (i : ℤ))) =
      uC r ^ (∑ i ∈ range n, ((1 : ℤ) + (i : ℤ))) *
        uC r ^ (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ))) *
        uC r ^ (((2 * ec * n : ℕ)) : ℤ) := by
    rw [← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1
    rw [hsum, hsum, hsum, hsum]
    have h1 : (ec : ℤ) = d + n + 1 - j5 := by omega
    have h2' : ((j5 - n : ℕ) : ℤ) = j5 - n := by omega
    push_cast
    rw [h1, h2']; ring
  have ht := uC_sub_inv_ne hr
  have hX : (-(uC r - (uC r)⁻¹)) ^ n ≠ 0 := pow_ne_zero n (neg_ne_zero.2 ht)
  have hzp : ∀ z : ℤ, uC r ^ z ≠ 0 := fun z => zpow_ne_zero z hu
  have pos : ∀ m : ℕ, m < r → (0 : ℝ) < qfact r m := fun m h => qfact_pos hr h
  have c1 := (pos (d + n + 1) (by omega)).ne'
  have c2 := (pos (d + 1) (by omega)).ne'
  have c3 := (pos (ec + n) hb2).ne'
  have c4 := (pos ec (by omega)).ne'
  have c5 := (pos n (by omega)).ne'
  have c7 := (pos j5 (by omega)).ne'
  have c8 := (pos (j5 - n) (by omega)).ne'
  simp only [← Complex.ofReal_prod]
  rw [g1, g5, g6, g4]
  have z1 := hzp (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ)))
  have z2 := hzp (∑ i ∈ range n, (((ec : ℤ) + 1) + (i : ℤ)))
  have z3 := hzp (∑ i ∈ range n, ((1 : ℤ) + (i : ℤ)))
  have z4 := hzp (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ)))
  have zc := hzp (((2 * ec * n : ℕ)) : ℤ)
  generalize uC r ^ (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ))) = Z1 at *
  generalize uC r ^ (∑ i ∈ range n, (((ec : ℤ) + 1) + (i : ℤ))) = Z2 at *
  generalize uC r ^ (∑ i ∈ range n, ((1 : ℤ) + (i : ℤ))) = Z3 at *
  generalize uC r ^ (∑ i ∈ range n, ((((j5 - n + 1 : ℕ)) : ℤ) + (i : ℤ))) = Z4 at *
  generalize uC r ^ (((2 * ec * n : ℕ)) : ℤ) = Zc at *
  generalize (-(uC r - (uC r)⁻¹)) ^ n = X at *
  have hZc : Zc = Z1 * Z2 / (Z3 * Z4) := by
    rw [eq_div_iff (mul_ne_zero z3 z4)]; linear_combination (-1 : ℂ) * hbal
  rw [hZc]
  push_cast
  field_simp

/-- In the degenerate case `b = Q^(n+d+2) = a Q Q^n`, for `k ≤ n`, the summand of Jackson's series at
the parameters of the boundary evaluation is `tDeg`. -/
theorem Tj_eq_tDeg_Q {r : ℕ} (hr : 2 ≤ r) {d n j5 ec k : ℕ} (hec : ec + j5 = d + n + 1)
    (hnj : n ≤ j5) (hj5 : j5 ≤ d + n) (hk : k ≤ n) (hb1 : d + 2 * n + 1 < r) :
    Tj (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (n + d + 2)) ((uC r ^ 2) ^ ec)
        ((uC r ^ 2) ^ n) k = tDeg (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ ec) k := by
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have hb : (uC r ^ 2) ^ (n + d + 2) = (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ n := by ring
  rw [hb]
  refine Tj_eq_tDeg k hQ (pow_ne_zero _ hQ) (pow_ne_zero _ hQ) (pow_ne_zero _ hQ) ?_ ?_
  · refine pk_ne_zero _ _ _ fun i hi => ?_
    rw [show (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ n * (uC r ^ 2) ^ i =
      (uC r ^ 2) ^ ((d + n + 2 + i : ℕ) : ℤ) by rw [zpow_natCast]; ring]
    exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)
  · refine pk_ne_zero _ _ _ fun i hi => ?_
    rw [show ((uC r ^ 2) ^ n)⁻¹ * (uC r ^ 2) ^ i = (uC r ^ 2) ^ ((i : ℤ) - n) by
      rw [zpow_sub₀ hQ, zpow_natCast, zpow_natCast]; field_simp]
    exact Qne_neg hr (by omega) (by omega)

/-- The last step of the evaluation: given the sum of the weighted terms as the first term times
Jackson's right side, the product identity gives `QDougall`. -/
theorem qDougall_of_sumR_N {r d j2 n j5 N : ℕ} (hr : 2 ≤ r) (hnj : n ≤ j5) (hj5 : j5 ≤ d + n)
    (hj2 : n ≤ j2) (hN : N ≤ n)
    (hadmX : ∀ k ≤ N, qAdm r (j2 + d) j2 (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (j2 + d) j5 (j2 + d - j5) ∧ qAdm r (d + 2 * n - j5) j2 (j2 + d - j5))
    (sumR : ∑ k ∈ range (N + 1), wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k =
      wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 0 *
        ((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (j2 + (d + n + 1 - j5)) / qfact r (j2 + (d + n + 1 - j5) - n)) /
          ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n))))) :
    QDougall r (j2 + d) j2 (d + 2 * n - j5) j5 d N (j2 + d - j5) := by
  obtain ⟨_, bQ1⟩ := hadmQ.1
  obtain ⟨_, bQ2⟩ := hadmQ.2
  obtain ⟨_, bX⟩ := (hadmX 0 (by omega)).2
  have hb1 : d + n + 1 < r := by omega
  have hS : (∑ k ∈ range (N + 1), (jOmega r (j2 + d) j2 (d + 2 * n - j5) j5 (d + 2 * k) *
      Sj r (j2 + d) j2 (d + 2 * n - j5) j5 (j2 + d - j5) ((d + 2 * k : ℕ) : ℤ) ^ 2)) =
      ∑ k ∈ range (N + 1), wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k := by
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
  have key := prod_identity hr hnj hj5 hj2 hb1 (by omega) (by omega)
  linear_combination key

/-- The last step of the evaluation, for the full range. -/
theorem qDougall_of_sumR {r d j2 n j5 : ℕ} (hr : 2 ≤ r) (hnj : n ≤ j5) (hj5 : j5 ≤ d + n)
    (hj2 : n ≤ j2)
    (hadmX : ∀ k ≤ n, qAdm r (j2 + d) j2 (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (j2 + d) j5 (j2 + d - j5) ∧ qAdm r (d + 2 * n - j5) j2 (j2 + d - j5))
    (sumR : ∑ k ∈ range (n + 1), wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 k =
      wTerm r (j2 + d) j2 (d + 2 * n - j5) j5 0 *
        ((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (j2 + (d + n + 1 - j5)) / qfact r (j2 + (d + n + 1 - j5) - n)) /
          ((qfact r j2 / qfact r (j2 - n)) * (qfact r j5 / qfact r (j5 - n))))) :
    QDougall r (j2 + d) j2 (d + 2 * n - j5) j5 d n (j2 + d - j5) :=
  qDougall_of_sumR_N hr hnj hj5 hj2 le_rfl hadmX hadmQ sumR

/-- **The boundary evaluation `QDougall`, degenerate case** `j1 + j2 = j4 + j5` (`j2 = n`), in the
parameters `j1 = n + d`, `j4 = d + 2n - j5`. There the hypotheses of Jackson's sum fail, and the
partial sums of the series with fewer parameters (`tDeg_sum`) replace it. -/
theorem qDougall_deg_param {r d n j5 : ℕ} (hr : 2 ≤ r) (hnj : n ≤ j5) (hj5 : j5 ≤ d + n)
    (hadmX : ∀ k ≤ n, qAdm r (n + d) n (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (n + d) j5 (n + d - j5) ∧ qAdm r (d + 2 * n - j5) n (n + d - j5)) :
    QDougall r (n + d) n (d + 2 * n - j5) j5 d n (n + d - j5) := by
  have hX' : ∀ k ≤ n, qAdm r (n + d) n (n + d - n + 2 * k) ∧
      qAdm r (d + 2 * n - j5) j5 (n + d - n + 2 * k) := by
    simpa only [Nat.add_sub_cancel_left] using hadmX
  have hmap := wTerm_eq_Tj hr (j1 := n + d) (j2 := n) (j4 := d + 2 * n - j5) (j5 := j5) (n := n)
    (by omega) (by omega) (by omega) (by omega) hX' hadmQ
  have e1 : n + d - n + 1 = d + 1 := by omega
  have e2 : (n + d - n + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  have e2' : (d + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  simp only [Nat.add_sub_cancel_left, e1, e2, e2'] at hmap
  obtain ⟨_, bQ1⟩ := hadmQ.1
  obtain ⟨_, bQ2⟩ := hadmQ.2
  obtain ⟨_, bX⟩ := (hadmX n le_rfl).2
  have hb1 : d + n + 1 < r := by omega
  have hb1' : d + 2 * n + 1 < r := by omega
  have hb2 : d + n + 1 - j5 + n < r := by omega
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have hTj : ∀ k ≤ n, Tj (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (n + d + 2))
      ((uC r ^ 2) ^ (d + n + 1 - j5)) ((uC r ^ 2) ^ n) k =
      tDeg (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (d + n + 1 - j5)) k :=
    fun k hk => Tj_eq_tDeg_Q hr (ec := d + n + 1 - j5) (by omega) hnj hj5 hk hb1'
  have hsumT := tDeg_sum (q := uC r ^ 2) (a := (uC r ^ 2) ^ (d + 1)) (c := (uC r ^ 2) ^ (d + n + 1 - j5))
    (N := n) hQ (pow_ne_zero _ hQ) (by
      rw [← zpow_natCast]; exact Qne_pos hr (by push_cast; omega) (by push_cast; omega))
    (fun i hi => ⟨by
      rw [show (uC r ^ 2) * (uC r ^ 2) ^ i = (uC r ^ 2) ^ ((1 + i : ℕ) : ℤ) by rw [zpow_natCast]; ring]
      exact Qne_pos hr (by push_cast; omega) (by push_cast; omega), by
      rw [Qpow_ratio _ hQ]
      exact Qne_pos hr (by push_cast; omega) (by push_cast; omega)⟩) n le_rfl
  have hv := sDeg_val hr (d := d) (n := n) (j5 := j5) (ec := d + n + 1 - j5) (by omega) hnj hj5 hb1 hb2
  have sumC : (∑ k ∈ range (n + 1), (wTerm r (n + d) n (d + 2 * n - j5) j5 k : ℂ)) =
      (wTerm r (n + d) n (d + 2 * n - j5) j5 0 : ℂ) *
        ((((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (d + n + 1 - j5 + n) / qfact r (d + n + 1 - j5)) /
          (qfact r n * (qfact r j5 / qfact r (j5 - n)))) : ℝ) : ℂ) := by
    rw [sum_congr rfl (fun k hk => (hmap k (by simp only [mem_range] at hk; omega)).trans
      (by rw [hTj k (by simp only [mem_range] at hk; omega)])), ← mul_sum, hsumT, hv]
  have hR : (qfact r (d + n + 1) / qfact r (d + 1)) *
        (qfact r (d + n + 1 - j5 + n) / qfact r (d + n + 1 - j5)) /
        (qfact r n * (qfact r j5 / qfact r (j5 - n))) =
      (qfact r (d + n + 1) / qfact r (d + 1)) *
        (qfact r (n + (d + n + 1 - j5)) / qfact r (n + (d + n + 1 - j5) - n)) /
        ((qfact r n / qfact r (n - n)) * (qfact r j5 / qfact r (j5 - n))) := by
    have q0 : qfact r 0 = 1 := by simp [qfact]
    rw [show n + (d + n + 1 - j5) - n = d + n + 1 - j5 by omega, show n - n = 0 by omega, q0,
      add_comm n (d + n + 1 - j5), div_one]
  have sumR : ∑ k ∈ range (n + 1), wTerm r (n + d) n (d + 2 * n - j5) j5 k =
      wTerm r (n + d) n (d + 2 * n - j5) j5 0 *
        ((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (n + (d + n + 1 - j5)) / qfact r (n + (d + n + 1 - j5) - n)) /
          ((qfact r n / qfact r (n - n)) * (qfact r j5 / qfact r (j5 - n)))) := by
    rw [← hR]; exact_mod_cast sumC
  exact qDougall_of_sumR hr hnj hj5 le_rfl hadmX hadmQ sumR

/-- **The boundary evaluation `QDougall` for the lowest sixth colour `j1 - j5` and the third colours
from `j1 - j2`**, for admissible spins whose third colours run up to `j4 + j5` (no level cut-off
inside the range): the non-degenerate case by Jackson's sum and the degenerate
case `j1 + j2 = j4 + j5` by the partial sums of the series with fewer parameters. -/
theorem qDougall_orbit {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h51 : j5 ≤ j1)
    (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j1 - j5) ∧ qAdm r j4 j2 (j1 - j5)) :
    QDougall r j1 j2 j4 j5 (j1 - j2) n (j1 - j5) := by
  have A0 := hadmX 0 (by omega)
  have An := hadmX n le_rfl
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨⟨hpn, hn1, hn2, hn3⟩, hrn⟩ := An.1
  rcases lt_or_eq_of_le (show j4 + j5 ≤ j1 + j2 by omega) with hlt | heq
  · exact qDougall_nondeg hr h21 h51 hlt hn hadmX hadmQ
  · obtain ⟨d, rfl⟩ : ∃ d, j1 = j2 + d := ⟨j1 - j2, by omega⟩
    obtain rfl : j4 = d + 2 * n - j5 := by omega
    obtain rfl : j2 = n := by omega
    simp only [Nat.add_sub_cancel_left] at hadmX ⊢
    exact qDougall_deg_param hr (by omega) (by omega) hadmX hadmQ


/-- **The dual step.** The boundary evaluation for the dual data `B, F, E, A` (rows and columns
exchanged) gives the one for `B, A, E, F`: the weighted norms of the rows and of the columns of one
matrix are the same constant (`sixj_norm_one`), and `Sj_dual` exchanges the two colours. -/
theorem qDougallAt_dual {r : ℕ} (hr : 2 ≤ r) (B A E F x : ℕ) (hx1 : qAdm r B A x)
    (hx2 : qAdm r E F x) (hD : QDougallAt r B F E A) : QDougallAt r B A E F := by
  have hqf := hx1; have hqe := hx2
  unfold qAdm Lightlike.Pentagon.Tri at hx1 hx2
  have hparX : (B + F + E + A) % 2 = 0 := by omega
  have hparQ : (B + A + E + F) % 2 = 0 := by omega
  have iffX := adm_pair_iff hr hparX
  have iffQ := adm_pair_iff hr hparQ
  obtain ⟨xLpar, xHpar, heqX, hloX0, hhiX0⟩ :=
    pair_facts (r := r) (a := B) (b := F) (c := E) (d := A) hparX (by omega) (by omega)
  obtain ⟨qLpar, qHpar, heqQ, hloQ0, hhiQ0⟩ :=
    pair_facts (r := r) (a := B) (b := A) (c := E) (d := F) hparQ (by omega) (by omega)
  have hxle : aLo B F E A ≤ aHi r B F E A := by
    have h1 := (aLo_spec B F E A).2.2.2.2
    have h2 := (aHi_spec r B F E A).2.2.2.2
    omega
  have hqle : aLo B A E F ≤ aHi r B A E F := by
    have h1 := (aLo_spec B A E F).2.2.2.2
    have h2 := (aHi_spec r B A E F).2.2.2.2
    omega
  obtain ⟨sL1, sL2, sL3, sL4, -⟩ := aLo_spec B F E A
  obtain ⟨tL1, tL2, tL3, tL4, -⟩ := aLo_spec B A E F
  obtain ⟨sH1, sH2, sH3, sH4, -⟩ := aHi_spec r B F E A
  obtain ⟨tH1, tH2, tH3, tH4, -⟩ := aHi_spec r B A E F
  unfold QDougallAt at hD ⊢
  generalize aLo B F E A = xL at *
  generalize aHi r B F E A = xH at *
  generalize aLo B A E F = qL at *
  generalize aHi r B A E F = qH at *
  revert heqX heqQ hhiX0 hhiQ0 hloX0 hloQ0
  have hadmX : ∀ k ≤ (xH - xL) / 2, qAdm r B F (xL + 2 * k) ∧ qAdm r E A (xL + 2 * k) := by
    intro k hk
    rw [iffX]
    omega
  have hadmQ : ∀ l ≤ (qH - qL) / 2, qAdm r B A (qL + 2 * l) ∧ qAdm r E F (qL + 2 * l) := by
    intro l hl
    rw [iffQ]
    omega
  have hxn : xL + 2 * ((xH - xL) / 2) = xH := by omega
  have hqn : qL + 2 * ((qH - qL) / 2) = qH := by omega
  intro d1 d2 d3 d4 d5 d6
  have key := sixj_norm_one hr B F E A xL ((xH - xL) / 2) qL ((qH - qL) / 2) hadmX
    (by assumption) (by rw [hxn]; push_cast; assumption) hadmQ (by assumption)
    (by rw [hqn]; push_cast; assumption) (by assumption) (by assumption) hD
  have h0 := key.2 0 (by omega)
  simp only [mul_zero, add_zero] at h0
  rw [show (∑ l ∈ range ((qH - qL) / 2 + 1), jOmega r B A E F (qL + 2 * l) *
        Sj r B F E A (qL + 2 * l) ((xL : ℕ) : ℤ) ^ 2) =
      ∑ l ∈ range ((qH - qL) / 2 + 1), jOmega r B A E F (qL + 2 * l) *
        Sj r B A E F xL ((qL + 2 * l : ℕ) : ℤ) ^ 2 from
    sum_congr rfl fun l _ => by rw [Sj_dual r B A E F xL (qL + 2 * l)]] at h0
  exact h0


/-- Exchanging the two pairs of `jOmega`. -/
lemma jOmega_swap_pairs (r a b c d x : ℕ) : jOmega r c d a b x = jOmega r a b c d x := by
  unfold jOmega; ring

/-- Exchanging the entries of both pairs of `jOmega`. -/
lemma jOmega_swap_in (r a b c d x : ℕ) : jOmega r b a d c x = jOmega r a b c d x := by
  unfold jOmega; rw [qDelta_swap12 r a b x, qDelta_swap12 r c d x]

/-- `qRacahTerm` is symmetric in the four `α` and in `β₂, β₃`: the three permutations used. -/
lemma qRacahTerm_k1 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) (z : ℕ) :
    qRacahTerm r a4 a3 a2 a1 b1 b2 b3 z = qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z := by
  unfold qRacahTerm; ring

lemma qRacahTerm_k2 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) (z : ℕ) :
    qRacahTerm r a1 a3 a2 a4 b1 b3 b2 z = qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z := by
  unfold qRacahTerm; ring

lemma qRacahTerm_k3 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) (z : ℕ) :
    qRacahTerm r a4 a2 a3 a1 b1 b3 b2 z = qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z := by
  unfold qRacahTerm; ring

lemma SR_k1 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SR r a4 a3 a2 a1 b1 b2 b3 = SR r a1 a2 a3 a4 b1 b2 b3 := by
  unfold SR; exact sum_congr rfl fun z _ => qRacahTerm_k1 r a1 a2 a3 a4 b1 b2 b3 z

lemma SR_k2 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SR r a1 a3 a2 a4 b1 b3 b2 = SR r a1 a2 a3 a4 b1 b2 b3 := by
  unfold SR; exact sum_congr rfl fun z _ => qRacahTerm_k2 r a1 a2 a3 a4 b1 b2 b3 z

lemma SR_k3 (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SR r a4 a2 a3 a1 b1 b3 b2 = SR r a1 a2 a3 a4 b1 b2 b3 := by
  unfold SR; exact sum_congr rfl fun z _ => qRacahTerm_k3 r a1 a2 a3 a4 b1 b2 b3 z

/-- `Sj` under `(j1 j4)(j2 j5)`. -/
lemma Sj_k1 (r j1 j2 j4 j5 q : ℕ) (y : ℤ) :
    Sj r j4 j5 j1 j2 q y = Sj r j1 j2 j4 j5 q y := by
  have key := SR_k1 r (((j1 : ℤ) + j2 + y) / 2) (((j1 : ℤ) + j5 + q) / 2) (((j4 : ℤ) + j2 + q) / 2)
    (((j4 : ℤ) + j5 + y) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2) ((y + j2 + j5 + q) / 2)
    ((y + j1 + q + j4) / 2)
  unfold Sj; rw [← key]; congr 1 <;> omega

/-- `Sj` under `(j1 j2)(j4 j5)`. -/
lemma Sj_k2 (r j1 j2 j4 j5 q : ℕ) (y : ℤ) :
    Sj r j2 j1 j5 j4 q y = Sj r j1 j2 j4 j5 q y := by
  have key := SR_k2 r (((j1 : ℤ) + j2 + y) / 2) (((j1 : ℤ) + j5 + q) / 2) (((j4 : ℤ) + j2 + q) / 2)
    (((j4 : ℤ) + j5 + y) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2) ((y + j2 + j5 + q) / 2)
    ((y + j1 + q + j4) / 2)
  unfold Sj; rw [← key]; congr 1 <;> omega

/-- `Sj` under `(j1 j5)(j2 j4)`. -/
lemma Sj_k3 (r j1 j2 j4 j5 q : ℕ) (y : ℤ) :
    Sj r j5 j4 j2 j1 q y = Sj r j1 j2 j4 j5 q y := by
  have key := SR_k3 r (((j1 : ℤ) + j2 + y) / 2) (((j1 : ℤ) + j5 + q) / 2) (((j4 : ℤ) + j2 + q) / 2)
    (((j4 : ℤ) + j5 + y) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2) ((y + j2 + j5 + q) / 2)
    ((y + j1 + q + j4) / 2)
  unfold Sj; rw [← key]; congr 1 <;> omega

/-- `QDougall` is invariant under `(j1 j4)(j2 j5)`. -/
theorem qDougall_k1 (r j1 j2 j4 j5 x n q : ℕ) :
    QDougall r j4 j5 j1 j2 x n q ↔ QDougall r j1 j2 j4 j5 x n q := by
  unfold QDougall
  simp only [jOmega_swap_pairs r j1 j5 j4 j2 q, jOmega_swap_pairs r j1 j2 j4 j5, Sj_k1]

/-- `QDougall` is invariant under `(j1 j2)(j4 j5)`. -/
theorem qDougall_k2 (r j1 j2 j4 j5 x n q : ℕ) :
    QDougall r j2 j1 j5 j4 x n q ↔ QDougall r j1 j2 j4 j5 x n q := by
  unfold QDougall
  have w : jOmega r j2 j4 j5 j1 q = jOmega r j1 j5 j4 j2 q := by
    rw [jOmega_swap_in r j4 j2 j1 j5 q, jOmega_swap_pairs r j1 j5 j4 j2 q]
  simp only [w, jOmega_swap_in r j1 j2 j4 j5, Sj_k2]

/-- `QDougall` is invariant under `(j1 j5)(j2 j4)`. -/
theorem qDougall_k3 (r j1 j2 j4 j5 x n q : ℕ) :
    QDougall r j5 j4 j2 j1 x n q ↔ QDougall r j1 j2 j4 j5 x n q := by
  unfold QDougall
  have w : jOmega r j5 j1 j2 j4 q = jOmega r j1 j5 j4 j2 q := jOmega_swap_in r j1 j5 j4 j2 q
  have t : ∀ y, jOmega r j5 j4 j2 j1 y = jOmega r j1 j2 j4 j5 y := fun y => by
    rw [jOmega_swap_pairs r j2 j1 j5 j4 y, jOmega_swap_in r j1 j2 j4 j5 y]
  simp only [w, t, Sj_k3]

/-- The boundary evaluation for the data is invariant under `(B E)(A F)`. -/
theorem qDougallAt_k1 (r B A E F : ℕ) : QDougallAt r E F B A ↔ QDougallAt r B A E F := by
  unfold QDougallAt
  have h1 : aLo E F B A = aLo B A E F := by unfold aLo; omega
  have h2 : aHi r E F B A = aHi r B A E F := by unfold aHi; omega
  have h3 : aLo E A B F = aLo B F E A := by unfold aLo; omega
  rw [h1, h2, h3]; exact qDougall_k1 r B A E F _ _ _

/-- The boundary evaluation for the data is invariant under `(B A)(E F)`. -/
theorem qDougallAt_k2 (r B A E F : ℕ) : QDougallAt r A B F E ↔ QDougallAt r B A E F := by
  unfold QDougallAt
  have h1 : aLo A B F E = aLo B A E F := by unfold aLo; omega
  have h2 : aHi r A B F E = aHi r B A E F := by unfold aHi; omega
  have h3 : aLo A E F B = aLo B F E A := by unfold aLo; omega
  rw [h1, h2, h3]; exact qDougall_k2 r B A E F _ _ _

/-- The boundary evaluation for the data is invariant under `(B F)(A E)`. -/
theorem qDougallAt_k3 (r B A E F : ℕ) : QDougallAt r F E A B ↔ QDougallAt r B A E F := by
  unfold QDougallAt
  have h1 : aLo F E A B = aLo B A E F := by unfold aLo; omega
  have h2 : aHi r F E A B = aHi r B A E F := by unfold aHi; omega
  have h3 : aLo F B A E = aLo B F E A := by unfold aLo; omega
  rw [h1, h2, h3]; exact qDougall_k3 r B A E F _ _ _


/-- **`QDougallAt` for the first orbit, untruncated range**: the lowest third colour is `B - A`, the
lowest sixth colour is `B - F`, and the third colours run up to `E + F` (no level cut-off before
it). -/
theorem qDougallAt_O1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : A ≤ B) (hF : F ≤ B) (hx : aLo B A E F = B - A)
    (hq : aLo B F E A = B - F) (htop : aHi r B A E F = E + F) : QDougallAt r B A E F := by
  have hqf := hq1; have hqe := hq2
  unfold qAdm Lightlike.Pentagon.Tri at hq1 hq2
  have hparX : (B + A + E + F) % 2 = 0 := by omega
  have hparQ : (B + F + E + A) % 2 = 0 := by omega
  have iffX := adm_pair_iff hr hparX
  have iffQ := adm_pair_iff hr hparQ
  obtain ⟨xLpar, xHpar, -, -, -⟩ :=
    pair_facts (r := r) (a := B) (b := A) (c := E) (d := F) hparX (by omega) (by omega)
  obtain ⟨qLpar, qHpar, -, -, -⟩ :=
    pair_facts (r := r) (a := B) (b := F) (c := E) (d := A) hparQ (by omega) (by omega)
  have hqmem := (iffQ q).1 ⟨hqf, hqe⟩
  have hqL := (iffQ (aLo B F E A)).2 ⟨le_rfl, by omega, qLpar, hqmem.2.2.2⟩
  unfold QDougallAt
  rw [hx, htop, hq]
  have hxle : B - A ≤ E + F := by
    have := (aLo_spec B A E F).2.2.2.2
    have h2 := (aHi_spec r B A E F).2.2.2.2
    omega
  have hadmX : ∀ k ≤ (E + F - (B - A)) / 2, qAdm r B A (B - A + 2 * k) ∧ qAdm r E F (B - A + 2 * k) := by
    intro k hk
    rw [iffX]
    rw [hx, htop]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  rw [hq] at hqL
  exact qDougall_orbit hr hA hF (by omega) hadmX hqL

/-- The first orbit, untruncated, for the image under `(B E)(A F)`. -/
theorem qDougallAt_O1_k1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : F ≤ E) (hF : A ≤ E) (hx : aLo E F B A = E - F)
    (hq : aLo E A B F = E - A) (htop : aHi r E F B A = B + A) : QDougallAt r B A E F :=
  (qDougallAt_k1 r B A E F).1 (qDougallAt_O1 hr E F B A q hq2 hq1 hA hF hx hq htop)

/-- The first orbit, untruncated, for the image under `(B A)(E F)`. -/
theorem qDougallAt_O1_k2 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : B ≤ A) (hF : E ≤ A) (hx : aLo A B F E = A - B)
    (hq : aLo A E F B = A - E) (htop : aHi r A B F E = F + E) : QDougallAt r B A E F :=
  (qDougallAt_k2 r B A E F).1 (qDougallAt_O1 hr A B F E q (qAdm_swap12 hq2) (qAdm_swap12 hq1)
    hA hF hx hq htop)

/-- The first orbit, untruncated, for the image under `(B F)(A E)`. -/
theorem qDougallAt_O1_k3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : E ≤ F) (hF : B ≤ F) (hx : aLo F E A B = F - E)
    (hq : aLo F B A E = F - B) (htop : aHi r F E A B = A + B) : QDougallAt r B A E F :=
  (qDougallAt_k3 r B A E F).1 (qDougallAt_O1 hr F E A B q (qAdm_swap12 hq1) (qAdm_swap12 hq2)
    hA hF hx hq htop)

/-- The ratio of Jackson's summand at the parameters `a = Q^(d+1)`, `b = Q^(n+d+2)`, `c = Q^ec`, `x = Q^j2`, with the fourth Pochhammer argument `d + 2 + k - ec` free (the exponent `ec` is not tied to a spin here). -/
theorem rhoT_gen {r : ℕ} (hr : 2 ≤ r) {d j2 n k ec : ℕ} (hec0 : 0 < ec) (hec1 : ec ≤ d + 1)
    (hkn : k < n) (hj2 : k < j2)
    (h1 : d + 2 * k + 3 < r) (h2 : j2 + d + k + 2 < r) (h3 : d + n + k + 2 < r)
    (h5 : d + 2 + k - ec < r) :
    rhoT (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (j2 + d + 2)) ((uC r ^ 2) ^ ec)
        ((uC r ^ 2) ^ n) k =
      (((qnum r (d + 2 * k + 3) * qnum r (d + k + 1) * qnum r (j2 + d + k + 2) *
          qnum r (ec + k) * qnum r (n - k)) /
        (qnum r (d + 2 * k + 1) * qnum r (k + 1) * qnum r (j2 - k) * qnum r (d + 2 + k - ec) *
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
        uC r ^ ((d + 2 + k - ec : ℕ) : ℤ) * uC r ^ ((d + n + k + 2 : ℕ) : ℤ) := by
    simp only [← zpow_add₀ hu]
    congr 1
    omega
  have hQsq : ∀ m : ℤ, (uC r ^ 2) ^ m = uC r ^ m * uC r ^ m := fun m => by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu]; congr 1; push_cast; ring
  rw [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, hQsq ((n : ℤ) - j2 - ec)]
  rw [show ((d + 1 : ℕ) : ℤ) + 1 - ((j2 + d + 2 : ℕ) : ℤ) + k = -((j2 - k : ℕ) : ℤ) by push_cast; omega,
    show ((d + 1 : ℕ) : ℤ) + 1 - ec + k = ((d + 2 + k - ec : ℕ) : ℤ) by push_cast; omega,
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
  have a9 := qp (d + 2 + k - ec) (by omega) (by omega)
  have a10 := qp (d + n + k + 2) (by omega) (by omega)
  have b : ∀ m : ℤ, uC r ^ m ≠ 0 := fun m => zpow_ne_zero m hu
  have hX : uC r ^ ((n : ℤ) - j2 - ec) * uC r ^ ((n : ℤ) - j2 - ec) =
      (uC r ^ ((d + 2 * k + 1 : ℕ) : ℤ) * uC r ^ ((k + 1 : ℕ) : ℤ) * uC r ^ (-((j2 - k : ℕ) : ℤ)) *
        uC r ^ ((d + 2 + k - ec : ℕ) : ℤ) * uC r ^ ((d + n + k + 2 : ℕ) : ℤ)) /
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



/-- The nonvanishing facts that `Tj_succ` needs, at the parameters of `rhoT_gen`. -/
theorem Tj_succ_hyps_gen {r : ℕ} (hr : 2 ≤ r) {d j2 n k ec : ℕ} (hec0 : 0 < ec) (hec1 : ec ≤ d + 1)
    (hkn : k < n) (hj2 : k < j2)
    (h1 : d + 2 * k + 3 < r) (h2 : j2 + d + k + 2 < r) (h3 : d + n + k + 2 < r)
    (h5 : d + 2 + k - ec < r) :
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




/-- The right side of Jackson's sum at `a = Q^(d+1)`, `b = Q^(j2+d+2)`, `c = Q^ec`, `x = Q^n` as a ratio of quantum factorials, with `ec` free. -/
theorem jacksonRhs_gen {r : ℕ} (hr : 2 ≤ r) {d j2 n ec : ℕ} (hec1 : ec ≤ d + 1) (hn2 : n ≤ j2)
    (hb1 : d + n + 1 < r) (hb2 : j2 + ec < r) (hb3 : d + 1 - ec + n < r) (hec0 : 0 < ec) :
    jacksonRhs (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (j2 + d + 2)) ((uC r ^ 2) ^ ec) n =
      (((qfact r (d + n + 1) / qfact r (d + 1)) * (qfact r (j2 + ec) / qfact r (j2 + ec - n)) /
        ((qfact r j2 / qfact r (j2 - n)) *
          (qfact r (d + 1 - ec + n) / qfact r (d + 1 - ec))) : ℝ) : ℂ) := by
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
      (uC r ^ 2) ^ (((d + 1 - ec + 1 : ℕ)) : ℤ) := by
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
  have g4 : ∏ i ∈ range n, qZ r ((((d + 1 - ec + 1 : ℕ)) : ℤ) + i) = qfact r (d + 1 - ec + n) / qfact r (d + 1 - ec) := by
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (d + 1 - ec) n (by omega) hr
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
        uC r ^ (∑ i ∈ range n, ((((d + 1 - ec + 1 : ℕ)) : ℤ) + (i : ℤ))) := by
    rw [← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1
    rw [hsum, hsum, hsum, hsum]
    have h2 : (((d + 1 - ec + 1 : ℕ)) : ℤ) = d + 1 - ec + 1 := by omega
    rw [h2]; ring
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
  have c7 := (pos (d + 1 - ec + n) hb3).ne'
  have c8 := (pos (d + 1 - ec) (by omega)).ne'
  simp only [← Complex.ofReal_prod]
  rw [g1, g2, g3, g4]
  have z1 := hzp (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ)))
  have z2 := hzp (∑ i ∈ range n, ((-(j2 : ℤ) - ec) + (i : ℤ)))
  have z3 := hzp (∑ i ∈ range n, ((-(j2 : ℤ)) + (i : ℤ)))
  have z4 := hzp (∑ i ∈ range n, ((((d + 1 - ec + 1 : ℕ)) : ℤ) + (i : ℤ)))
  have hs : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  generalize uC r ^ (∑ i ∈ range n, (((d : ℤ) + 2) + (i : ℤ))) = Z1 at *
  generalize uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ) - ec) + (i : ℤ))) = Z2 at *
  generalize uC r ^ (∑ i ∈ range n, ((-(j2 : ℤ)) + (i : ℤ))) = Z3 at *
  generalize uC r ^ (∑ i ∈ range n, ((((d + 1 - ec + 1 : ℕ)) : ℤ) + (i : ℤ))) = Z4 at *
  generalize (-(uC r - (uC r)⁻¹)) ^ n = X at *
  have hZ4 : Z4 = Z1 * Z2 / Z3 := by
    rw [eq_div_iff z3]; linear_combination (-1 : ℂ) * hbal
  rw [hZ4]
  push_cast
  field_simp



/-- The single term of `Sj` at the lowest sixth colour `j4 - j2`, for the third colour
`j1 - j2 + 2k`, as a signed product of inverse quantum factorials. -/
lemma Sj_val3 (r : ℕ) {j1 j2 j4 j5 k S B ε γ : ℕ} (h21 : j2 ≤ j1) (h42 : j2 ≤ j4)
    (hS : 2 * S = j4 + j5 + (j1 - j2)) (hB : 2 * B = j1 + j2 + j4 + j5)
    (hε : 2 * ε + j1 + j2 = j4 + j5) (hγ : 2 * γ + j5 = (j1 - j2) + j4) (hk : k ≤ j2)
    (hA : j4 ≤ S + k) :
    Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) =
      (-1) ^ (S + k) * qfact r (S + k + 1) * (qfact r ε)⁻¹ * (qfact r k)⁻¹ *
        (qfact r (S + k - j4))⁻¹ * (qfact r (j2 - k))⁻¹ * (qfact r γ)⁻¹ := by
  unfold Sj
  have e1 : (((j1 : ℤ) + j2 + ((j1 - j2 + 2 * k : ℕ) : ℤ)) / 2) = ((j1 + k : ℕ) : ℤ) := by omega
  have e2 : (((j1 : ℤ) + j5 + ((j4 - j2 : ℕ) : ℤ)) / 2) = (S : ℤ) := by omega
  have e3 : (((j4 : ℤ) + j2 + ((j4 - j2 : ℕ) : ℤ)) / 2) = (j4 : ℤ) := by omega
  have e4 : (((j4 : ℤ) + j5 + ((j1 - j2 + 2 * k : ℕ) : ℤ)) / 2) = ((S + k : ℕ) : ℤ) := by omega
  have e5 : (((j1 : ℤ) + j2 + j4 + j5) / 2) = (B : ℤ) := by omega
  have e6 : ((((j1 - j2 + 2 * k : ℕ) : ℤ) + j2 + j5 + ((j4 - j2 : ℕ) : ℤ)) / 2) =
      ((S + k : ℕ) : ℤ) := by omega
  have e7 : ((((j1 - j2 + 2 * k : ℕ) : ℤ) + j1 + ((j4 - j2 : ℕ) : ℤ) + j4) / 2) =
      ((S + k + γ : ℕ) : ℤ) := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  rw [SR_single (z0 := S + k) (by simp) (Or.inl (by simp)) (by omega)]
  have key : ∀ (m : ℕ) (a b : ℤ), a - b = (m : ℤ) → invQFact r (a - b) = (qfact r m)⁻¹ := by
    intro m a b h; rw [h, invQFact_nat]
  have q0 : qfact r 0 = 1 := by simp [qfact]
  unfold qRacahTerm
  rw [key ε ((S + k : ℕ) : ℤ) ((j1 + k : ℕ) : ℤ) (by push_cast; omega),
    key k ((S + k : ℕ) : ℤ) (S : ℤ) (by push_cast; omega),
    key (S + k - j4) ((S + k : ℕ) : ℤ) (j4 : ℤ) (by push_cast; omega),
    key 0 ((S + k : ℕ) : ℤ) ((S + k : ℕ) : ℤ) (by simp),
    key (j2 - k) (B : ℤ) ((S + k : ℕ) : ℤ) (by push_cast; omega),
    key γ ((S + k + γ : ℕ) : ℤ) ((S + k : ℕ) : ℤ) (by push_cast; omega), q0]
  simp only [inv_one, mul_one, one_mul]
  ring

/-- The step of `Sj` from `k` to `k + 1` at the lowest sixth colour `j4 - j2`, cross-multiplied. -/
lemma Sj_val3_succ {r : ℕ} (hr : 2 ≤ r) {j1 j2 j4 j5 k S B ε γ : ℕ} (h21 : j2 ≤ j1)
    (h42 : j2 ≤ j4) (hS : 2 * S = j4 + j5 + (j1 - j2)) (hB : 2 * B = j1 + j2 + j4 + j5)
    (hε : 2 * ε + j1 + j2 = j4 + j5) (hγ : 2 * γ + j5 = (j1 - j2) + j4) (hk : k + 1 ≤ j2)
    (hA : j4 ≤ S + k) (hlt : S + k + 2 < r) (hεr : ε < r) (hγr : γ < r) :
    Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) *
        (qnum r (k + 1) * qnum r (S + k + 1 - j4)) =
      - (Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) *
        (qnum r (S + k + 2) * qnum r (j2 - k))) := by
  rw [Sj_val3 (k := k + 1) r h21 h42 hS hB hε hγ hk (by omega),
    Sj_val3 (k := k) r h21 h42 hS hB hε hγ (by omega) hA]
  have f1 : qfact r (S + (k + 1) + 1) = qfact r (S + k + 1) * qnum r (S + k + 2) :=
    qfact_succ' r (S + k + 1)
  have f2 : qfact r (k + 1) = qfact r k * qnum r (k + 1) := qfact_succ' r k
  have f3 : qfact r (S + (k + 1) - j4) = qfact r (S + k - j4) * qnum r (S + k + 1 - j4) := by
    rw [show S + (k + 1) - j4 = (S + k - j4) + 1 by omega,
      show S + k + 1 - j4 = (S + k - j4) + 1 by omega]; exact qfact_succ' r _
  have f4 : qfact r (j2 - k) = qfact r (j2 - (k + 1)) * qnum r (j2 - k) := by
    rw [show j2 - k = (j2 - (k + 1)) + 1 by omega]; exact qfact_succ' r _
  rw [f1, f2, f3, f4]
  have p1 := qfact_pos (r := r) (n := k) hr (by omega)
  have p2 := qfact_pos (r := r) (n := S + k - j4) hr (by omega)
  have p3 := qfact_pos (r := r) (n := ε) hr hεr
  have p4 := qfact_pos (r := r) (n := j2 - (k + 1)) hr (by omega)
  have p5 := qfact_pos (r := r) (n := γ) hr hγr
  have p6 := qfact_pos (r := r) (n := S + k + 1) hr (by omega)
  have q1 : 0 < qnum r (k + 1) := qnum_pos hr (by omega) (by omega)
  have q2 : 0 < qnum r (S + k + 1 - j4) := qnum_pos hr (by omega) (by omega)
  have q3 : 0 < qnum r (j2 - k) := qnum_pos hr (by omega) (by omega)
  rw [show (-1 : ℝ) ^ (S + (k + 1)) = - (-1) ^ (S + k) by
    rw [show S + (k + 1) = (S + k) + 1 by ring, pow_succ]; ring]
  field_simp

/-- The weighted term of the boundary evaluation at the third colour `j1 - j2 + 2k` and the lowest
sixth colour `j4 - j2`. -/
noncomputable def wTerm3 (r j1 j2 j4 j5 k : ℕ) : ℝ :=
  jOmega r j1 j2 j4 j5 (j1 - j2 + 2 * k) *
    Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2

/-- **The step of the weighted term at the lowest sixth colour `j4 - j2`**, cross-multiplied. -/
theorem wTerm3_succ {r : ℕ} (hr : 2 ≤ r) {j1 j2 j4 j5 k S B ε γ n : ℕ} (h21 : j2 ≤ j1)
    (h42 : j2 ≤ j4) (hS : 2 * S = j4 + j5 + (j1 - j2)) (hB : 2 * B = j1 + j2 + j4 + j5)
    (hε : 2 * ε + j1 + j2 = j4 + j5) (hγ : 2 * γ + j5 = (j1 - j2) + j4) (hnS : S = (j1 - j2) + n)
    (hk : k + 1 ≤ j2) (hA : j4 ≤ S + k) (hlt : S + k + 2 < r) (hεr : ε < r) (hγr : γ < r)
    (a1 : qAdm r j1 j2 (j1 - j2 + 2 * k)) (a1' : qAdm r j1 j2 (j1 - j2 + 2 * (k + 1)))
    (a2 : qAdm r j4 j5 (j1 - j2 + 2 * k)) (a2' : qAdm r j4 j5 (j1 - j2 + 2 * (k + 1))) :
    wTerm3 r j1 j2 j4 j5 (k + 1) *
        (qnum r (j1 - j2 + 2 * k + 1) * qnum r (j2 - k) * qnum r (j1 + k + 2) * qnum r (n - k) *
          qnum r (S + k + 2) * qnum r (k + 1) ^ 2 * qnum r (S + k + 1 - j4) ^ 2) =
      wTerm3 r j1 j2 j4 j5 k *
        (qnum r (j1 - j2 + 2 * k + 3) * qnum r (k + 1) * qnum r (j1 - j2 + k + 1) *
          qnum r (S + k + 1 - j4) * qnum r (S + k + 1 - j5) * qnum r (S + k + 2) ^ 2 *
          qnum r (j2 - k) ^ 2) := by
  have st1 := qDelta_sq_step hr a1 a1'
  have st2 := qDelta_sq_step hr a2 a2'
  have sj := Sj_val3_succ hr h21 h42 hS hB hε hγ hk hA hlt hεr hγr
  have e1 : (j1 + j2 + (j1 - j2 + 2 * k)) / 2 = j1 + k := by omega
  have e2 : (j4 + j5 + (j1 - j2 + 2 * k)) / 2 = S + k := by omega
  rw [e1, show j1 + k - (j1 - j2 + 2 * k) = j2 - k by omega,
    show j1 + k - j1 + 1 = k + 1 by omega, show j1 + k - j2 + 1 = j1 - j2 + k + 1 by omega] at st1
  rw [e2, show S + k - (j1 - j2 + 2 * k) = n - k by omega,
    show S + k - j4 + 1 = S + k + 1 - j4 by omega,
    show S + k - j5 + 1 = S + k + 1 - j5 by omega] at st2
  have sj2 : Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) ^ 2 *
        (qnum r (k + 1) * qnum r (S + k + 1 - j4)) ^ 2 =
      Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2 *
        (qnum r (S + k + 2) * qnum r (j2 - k)) ^ 2 := by
    calc _ = (Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * (k + 1) : ℕ) : ℤ) *
          (qnum r (k + 1) * qnum r (S + k + 1 - j4))) ^ 2 := by ring
      _ = (-(Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) *
          (qnum r (S + k + 2) * qnum r (j2 - k)))) ^ 2 := by rw [sj]
      _ = _ := by ring
  have e : j1 - j2 + 2 * (k + 1) = j1 - j2 + 2 * k + 2 := by ring
  have q3 : qnum r (j1 - j2 + 2 * k + 2 + 1) = qnum r (j1 - j2 + 2 * k + 3) := by
    rw [show j1 - j2 + 2 * k + 2 + 1 = j1 - j2 + 2 * k + 3 by ring]
  unfold wTerm3 jOmega
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
  set D1 := qDelta r j1 j2 (j1 - j2 + 2 * k) ^ 2
  set D1' := qDelta r j1 j2 (j1 - j2 + 2 * k + 2) ^ 2
  set D2 := qDelta r j4 j5 (j1 - j2 + 2 * k) ^ 2
  set D2' := qDelta r j4 j5 (j1 - j2 + 2 * k + 2) ^ 2
  set T := Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k : ℕ) : ℤ) ^ 2
  set T' := Sj r j1 j2 j4 j5 (j4 - j2) ((j1 - j2 + 2 * k + 2 : ℕ) : ℤ) ^ 2
  linear_combination (q3' * qy * D2' * C1 * C2 * T' * B1 ^ 2 * E1 ^ 2) * st1 +
    (q3' * qy * D1 * B1 * B2 * T' * B1 ^ 2 * E1 ^ 2) * st2 +
    (q3' * qy * D1 * B1 * B2 * D2 * E1 * E2) * sj2


-- 400000 heartbeats: the default 200000 fails (timeout at `whnf`); 400000 passes.
set_option maxHeartbeats 400000 in
/-- **The map for the lowest sixth colour `j4 - j2`.** For the third colours `j1 - j2 + 2k` up to
`j1 + j2` (`k ≤ j2`, `j1 + j2 < j4 + j5`), the weighted terms are the first term times the summand
of Jackson's series at `Q = uC r ^ 2`, `a = Q^(x0+1)`, `b = Q^(n+x0+2)`, `c = Q^((x0+j4-j5)/2+1)`,
`x = Q^j2`, with `2n = j4 + j5 - x0`. -/
theorem wTerm3_eq_Tj {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h42 : j2 ≤ j4)
    (hnd : j1 + j2 < j4 + j5) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ j2, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j4 - j2) ∧ qAdm r j4 j2 (j4 - j2)) :
    ∀ k ≤ j2, (wTerm3 r j1 j2 j4 j5 k : ℂ) = (wTerm3 r j1 j2 j4 j5 0 : ℂ) *
      Tj (uC r ^ 2) ((uC r ^ 2) ^ (j1 - j2 + 1)) ((uC r ^ 2) ^ (n + (j1 - j2) + 2))
        ((uC r ^ 2) ^ ((j1 - j2 + j4 - j5) / 2 + 1)) ((uC r ^ 2) ^ j2) k := by
  have A0 := hadmX 0 (by omega)
  have An := hadmX j2 le_rfl
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨⟨hpn, hn1, hn2, hn3⟩, hrn⟩ := An.1
  obtain ⟨⟨hqn, hm1, hm2, hm3⟩, hsn⟩ := An.2
  obtain ⟨S, hS⟩ : ∃ S, S = (j1 - j2) + n := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, 2 * B = j1 + j2 + j4 + j5 := ⟨(j1 + j2 + j4 + j5) / 2, by omega⟩
  obtain ⟨ε, hε⟩ : ∃ ε, ε = n - j2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = n + (j1 - j2) - j5 := ⟨_, rfl⟩
  obtain ⟨ec, hecd⟩ : ∃ ec, ec = (j1 - j2 + j4 - j5) / 2 + 1 := ⟨_, rfl⟩
  rw [← hecd]
  have hec : ec = (j1 - j2) + n + 1 - j5 := by omega
  have hec0 : 0 < ec := by omega
  have hec1 : ec ≤ (j1 - j2) + 1 := by omega
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
    have W := wTerm3_succ hr (S := S) (B := B) (ε := ε) (γ := γ) (n := n) h21 h42
      (by omega) hB (by omega) (by omega) (by omega) hk (by omega) (by omega) (by omega) (by omega)
      (hadmX k (by omega)).1 (hadmX (k + 1) hk).1 (hadmX k (by omega)).2 (hadmX (k + 1) hk).2
    have hkn : k < n := by omega
    have hkj : k < j2 := by omega
    have h1 : (j1 - j2) + 2 * k + 3 < r := by omega
    have h2 : n + (j1 - j2) + k + 2 < r := by omega
    have h3 : (j1 - j2) + j2 + k + 2 < r := by omega
    have h5 : (j1 - j2) + 2 + k - ec < r := by omega
    have rt := rhoT_gen hr (d := j1 - j2) (j2 := n) (n := j2) (k := k) (ec := ec) hec0 hec1 hkj hkn
      h1 h2 h3 h5
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ :=
      Tj_succ_hyps_gen hr (d := j1 - j2) (j2 := n) (n := j2) (k := k) (ec := ec) hec0 hec1 hkj hkn
        h1 h2 h3 h5
    have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
    have T := Tj_succ (q := uC r ^ 2) (a := (uC r ^ 2) ^ ((j1 - j2) + 1))
      (b := (uC r ^ 2) ^ (n + (j1 - j2) + 2)) (c := (uC r ^ 2) ^ ec) (x := (uC r ^ 2) ^ j2) k
      c1 (pow_ne_zero _ hQ) (pow_ne_zero _ hQ) c2 c3 c4 c5 c6 c7 c8 c9 c10
    have T' : Tj (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (n + (j1 - j2) + 2))
        ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ j2) (k + 1) =
        Tj (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (n + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ j2) k *
        rhoT (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (n + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ j2) k := T
    rw [show S + k + 2 = n + (j1 - j2) + k + 2 by omega,
      show j1 + k + 2 = (j1 - j2) + j2 + k + 2 by omega,
      show S + k + 1 - j4 = (j1 - j2) + 2 + k - ec by omega,
      show S + k + 1 - j5 = ec + k by omega] at W
    have pq : ∀ m : ℕ, 0 < m → m < r → 0 < qnum r m := fun m h0 h1 => qnum_pos hr h0 h1
    have hM : qnum r (j2 - k) * qnum r (n + (j1 - j2) + k + 2) * qnum r (k + 1) *
        qnum r ((j1 - j2) + 2 + k - ec) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos (pq _ (by omega) (by omega)) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))) (pq _ (by omega) (by omega))).ne'
    have hden : qnum r ((j1 - j2) + 2 * k + 1) * qnum r (k + 1) * qnum r (n - k) *
        qnum r ((j1 - j2) + 2 + k - ec) * qnum r ((j1 - j2) + j2 + k + 2) ≠ 0 :=
      (mul_pos (mul_pos (mul_pos (mul_pos (pq _ (by omega) (by omega)) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))) (pq _ (by omega) (by omega)))
        (pq _ (by omega) (by omega))).ne'
    have hRatio : wTerm3 r j1 j2 j4 j5 (k + 1) = wTerm3 r j1 j2 j4 j5 k *
        ((qnum r ((j1 - j2) + 2 * k + 3) * qnum r ((j1 - j2) + k + 1) *
            qnum r (n + (j1 - j2) + k + 2) * qnum r (ec + k) * qnum r (j2 - k)) /
          (qnum r ((j1 - j2) + 2 * k + 1) * qnum r (k + 1) * qnum r (n - k) *
            qnum r ((j1 - j2) + 2 + k - ec) * qnum r ((j1 - j2) + j2 + k + 2))) := by
      rw [mul_div_assoc', eq_div_iff hden]
      apply mul_right_cancel₀ hM
      linear_combination W
    have hc : (wTerm3 r j1 j2 j4 j5 (k + 1) : ℂ) = (wTerm3 r j1 j2 j4 j5 k : ℂ) *
        rhoT (uC r ^ 2) ((uC r ^ 2) ^ ((j1 - j2) + 1)) ((uC r ^ 2) ^ (n + (j1 - j2) + 2))
          ((uC r ^ 2) ^ ec) ((uC r ^ 2) ^ j2) k := by
      rw [rt, hRatio]; push_cast; ring
    rw [hc, ihk, T']; ring

/-- **The product identity for the lowest sixth colour `j4 - j2`**, in clean parameters `j1 = m + d`, `j4 = d + 2n - j5`, `j2 = m`: the weight of the lowest column, the first weighted term and Jackson's right side multiply to `1`. Every quantum factorial cancels. -/
theorem prod_identity3 {r : ℕ} (hr : 2 ≤ r) {d m n j5 : ℕ} (hmn : m < n) (hj5 : n ≤ j5)
    (hj5' : j5 ≤ d + n) (hq0 : m + j5 ≤ d + 2 * n)
    (hb1 : d + n + 1 < r) (hb2 : d + 2 * n + 1 - j5 < r) (hb3 : m + d + 1 < r)
    (hb4 : j5 - n + m < r) :
    qnum r (d + 2 * n - j5 - m + 1) *
        (qfact r (n - m) * qfact r (d + n - j5) * qfact r (j5 - n + m) / qfact r (d + n + 1)) *
        (qfact r 0 * qfact r (d + 2 * n - j5 - m) * qfact r m / qfact r (d + 2 * n - j5 + 1)) *
      (qnum r (d + 1) * (qfact r 0 * qfact r d * qfact r m / qfact r (m + d + 1)) *
        (qfact r (j5 - n) * qfact r (d + n - j5) * qfact r n / qfact r (d + n + 1)) *
        (qfact r (d + n + 1) /
          (qfact r (n - m) * qfact r (j5 - n) * qfact r m * qfact r (d + n - j5))) ^ 2) *
      ((qfact r (m + d + 1) / qfact r (d + 1)) *
        (qfact r (n + (d + n + 1 - j5)) / qfact r (n + (d + n + 1 - j5) - m)) /
        ((qfact r n / qfact r (n - m)) * (qfact r (d + 1 - (d + n + 1 - j5) + m) /
          qfact r (d + 1 - (d + n + 1 - j5))))) = 1 := by
  have pos : ∀ k : ℕ, k < r → 0 < qfact r k := fun k h => qfact_pos hr h
  have q0 : qfact r 0 = 1 := by simp [qfact]
  have f1 : qfact r (d + 2 * n - j5 - m + 1) = qfact r (d + 2 * n - j5 - m) * qnum r (d + 2 * n - j5 - m + 1) :=
    qfact_succ' r _
  have f2 : qfact r (d + 1) = qfact r d * qnum r (d + 1) := qfact_succ' r _
  have f3 : qfact r (d + 2 * n - j5 + 1) = qfact r (d + 2 * n - j5) * qnum r (d + 2 * n - j5 + 1) :=
    qfact_succ' r _
  have e1 : n + (d + n + 1 - j5) = d + 2 * n + 1 - j5 := by omega
  have e2 : d + 2 * n + 1 - j5 - m = d + 2 * n - j5 - m + 1 := by omega
  have e3 : d + 1 - (d + n + 1 - j5) = j5 - n := by omega
  have e4 : d + 2 * n + 1 - j5 = d + 2 * n - j5 + 1 := by omega
  rw [e1, show d + 2 * n + 1 - j5 - m = d + 2 * n - j5 - m + 1 by omega, e3, q0, e4, f1, f2, f3]
  have p1 := (pos (n - m) (by omega)).ne'
  have p2 := (pos (d + n - j5) (by omega)).ne'
  have p3 := (pos (j5 - n + m) hb4).ne'
  have p4 := (pos (d + n + 1) hb1).ne'
  have p5 := (pos (d + 2 * n - j5 - m) (by omega)).ne'
  have p6 := (pos m (by omega)).ne'
  have p7 := (pos (d + 2 * n - j5) (by omega)).ne'
  have p8 := (pos d (by omega)).ne'
  have p9 := (pos (m + d + 1) hb3).ne'
  have p10 := (pos (j5 - n) (by omega)).ne'
  have p11 := (pos n (by omega)).ne'
  have q1 : 0 < qnum r (d + 2 * n - j5 - m + 1) := qnum_pos hr (by omega) (by omega)
  have q2 : 0 < qnum r (d + 1) := qnum_pos hr (by omega) (by omega)
  have q3 : 0 < qnum r (d + 2 * n - j5 + 1) := qnum_pos hr (by omega) (by omega)
  field_simp


/-- **The boundary evaluation `QDougall` for the lowest sixth colour `j4 - j2`**, in the parameters
`j1 = m + d`, `j4 = d + 2n - j5`, `j2 = m < n`: the third colours run from `d` to `d + 2m`. -/
theorem qDougall_orbit3_param {r d m n j5 : ℕ} (hr : 2 ≤ r) (hmn : m < n) (hj5 : n ≤ j5)
    (hj5' : j5 ≤ d + n) (hq0 : m + j5 ≤ d + 2 * n)
    (hadmX : ∀ k ≤ m, qAdm r (m + d) m (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (m + d) j5 (d + 2 * n - j5 - m) ∧ qAdm r (d + 2 * n - j5) m (d + 2 * n - j5 - m)) :
    QDougall r (m + d) m (d + 2 * n - j5) j5 d m (d + 2 * n - j5 - m) := by
  have hX' : ∀ k ≤ m, qAdm r (m + d) m (m + d - m + 2 * k) ∧
      qAdm r (d + 2 * n - j5) j5 (m + d - m + 2 * k) := by
    simpa only [Nat.add_sub_cancel_left] using hadmX
  have hmap := wTerm3_eq_Tj hr (j1 := m + d) (j2 := m) (j4 := d + 2 * n - j5) (j5 := j5) (n := n)
    (by omega) (by omega) (by omega) (by omega) hX' hadmQ
  obtain ⟨_, bX⟩ := (hadmX m le_rfl).1
  obtain ⟨_, bY⟩ := (hadmX m le_rfl).2
  obtain ⟨_, bQ1⟩ := hadmQ.1
  obtain ⟨_, bQ2⟩ := hadmQ.2
  obtain ⟨_, bX0⟩ := (hadmX 0 (by omega)).1
  obtain ⟨_, bY0⟩ := (hadmX 0 (by omega)).2
  have e1 : m + d - m + 1 = d + 1 := by omega
  have e2 : (m + d - m + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  simp only [Nat.add_sub_cancel_left, e1, e2] at hmap
  have e2' : (d + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  rw [e2'] at hmap
  have jh : JHypT (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ (n + d + 2))
      ((uC r ^ 2) ^ (d + n + 1 - j5)) m :=
    jhypT_of_exponents hr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have jsum := jackson_sumT jh m le_rfl
  have hRhs := jacksonRhs_gen hr (d := d) (j2 := n) (n := m) (ec := d + n + 1 - j5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have sumC : (∑ k ∈ range (m + 1), (wTerm3 r (m + d) m (d + 2 * n - j5) j5 k : ℂ)) =
      (wTerm3 r (m + d) m (d + 2 * n - j5) j5 0 : ℂ) *
        ((((qfact r (d + m + 1) / qfact r (d + 1)) *
          (qfact r (n + (d + n + 1 - j5)) / qfact r (n + (d + n + 1 - j5) - m)) /
          ((qfact r n / qfact r (n - m)) *
            (qfact r (d + 1 - (d + n + 1 - j5) + m) / qfact r (d + 1 - (d + n + 1 - j5))))) : ℝ) : ℂ) := by
    rw [sum_congr rfl (fun k hk => hmap k (by simp only [mem_range] at hk; omega)), ← mul_sum,
      jsum, hRhs]
  have sumR : ∑ k ∈ range (m + 1), wTerm3 r (m + d) m (d + 2 * n - j5) j5 k =
      wTerm3 r (m + d) m (d + 2 * n - j5) j5 0 *
        ((qfact r (d + m + 1) / qfact r (d + 1)) *
          (qfact r (n + (d + n + 1 - j5)) / qfact r (n + (d + n + 1 - j5) - m)) /
          ((qfact r n / qfact r (n - m)) *
            (qfact r (d + 1 - (d + n + 1 - j5) + m) / qfact r (d + 1 - (d + n + 1 - j5))))) := by
    exact_mod_cast sumC
  have hS : (∑ k ∈ range (m + 1), (jOmega r (m + d) m (d + 2 * n - j5) j5 (d + 2 * k) *
      Sj r (m + d) m (d + 2 * n - j5) j5 (d + 2 * n - j5 - m) ((d + 2 * k : ℕ) : ℤ) ^ 2)) =
      ∑ k ∈ range (m + 1), wTerm3 r (m + d) m (d + 2 * n - j5) j5 k := by
    simp only [wTerm3, Nat.add_sub_cancel_left]
  unfold QDougall
  rw [hS, sumR]
  unfold wTerm3 jOmega
  simp only [Nat.add_sub_cancel_left, mul_zero, add_zero]
  have hSj := Sj_val3 r (j1 := m + d) (j2 := m) (j4 := d + 2 * n - j5) (j5 := j5) (k := 0)
    (S := d + n) (B := m + d + n) (ε := n - m) (γ := d + n - j5)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [show ((m + d - m + 2 * 0 : ℕ) : ℤ) = (d : ℤ) by omega,
    show d + n + 0 - (d + 2 * n - j5) = j5 - n by omega, show m - 0 = m by omega,
    show d + n + 0 + 1 = d + n + 1 by omega, show d + 2 * n - j5 - m = d + 2 * n - j5 - m from rfl]
    at hSj
  have sq1 : ∀ k : ℕ, ((-1 : ℝ) ^ k) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]; simp
  have T1 := qDelta_sq_of hr hadmQ.1 (s := d + n) (x := n - m) (y := d + n - j5) (z := j5 - n + m)
    (w := d + n + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have T2 := qDelta_sq_of hr hadmQ.2 (s := d + 2 * n - j5) (x := 0) (y := d + 2 * n - j5 - m)
    (z := m) (w := d + 2 * n - j5 + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have X0 := hadmX 0 (by omega)
  simp only [mul_zero, add_zero] at X0
  have T3 := qDelta_sq_of hr X0.1 (s := m + d) (x := 0) (y := d) (z := m) (w := m + d + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have T4 := qDelta_sq_of hr X0.2 (s := d + n) (x := j5 - n) (y := d + n - j5) (z := n)
    (w := d + n + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [T1, T2, T3, T4]
  have hsqSj : Sj r (m + d) m (d + 2 * n - j5) j5 (d + 2 * n - j5 - m) (d : ℤ) ^ 2 =
      (qfact r (d + n + 1) / (qfact r (n - m) * qfact r (j5 - n) * qfact r m *
        qfact r (d + n - j5))) ^ 2 := by
    rw [hSj, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, sq1]
    have q0 : qfact r 0 = 1 := by simp [qfact]
    rw [q0]; field_simp
  rw [hsqSj]
  have key := prod_identity3 hr hmn hj5 hj5' hq0 (by omega) (by omega) (by omega) (by omega)
  rw [show d + m + 1 = m + d + 1 by ring]
  linear_combination key


/-- **The boundary evaluation `QDougall` for the lowest sixth colour `j4 - j2`**, for admissible spins
whose third colours run from `j1 - j2` up to `j1 + j2` (no level cut-off inside the range) and
`j1 + j2 < j4 + j5`. -/
theorem qDougall_orbit3 {r j1 j2 j4 j5 n : ℕ} (hr : 2 ≤ r) (h21 : j2 ≤ j1) (h42 : j2 ≤ j4)
    (hnd : j1 + j2 < j4 + j5) (hn : 2 * n = j4 + j5 - (j1 - j2))
    (hadmX : ∀ k ≤ j2, qAdm r j1 j2 (j1 - j2 + 2 * k) ∧ qAdm r j4 j5 (j1 - j2 + 2 * k))
    (hadmQ : qAdm r j1 j5 (j4 - j2) ∧ qAdm r j4 j2 (j4 - j2)) :
    QDougall r j1 j2 j4 j5 (j1 - j2) j2 (j4 - j2) := by
  have A0 := hadmX 0 (by omega)
  obtain ⟨⟨hp0, h01, h02, h03⟩, hr0⟩ := A0.1
  obtain ⟨⟨hq0, h11, h12, h13⟩, hs0⟩ := A0.2
  obtain ⟨d, rfl⟩ : ∃ d, j1 = j2 + d := ⟨j1 - j2, by omega⟩
  obtain rfl : j4 = d + 2 * n - j5 := by omega
  simp only [Nat.add_sub_cancel_left] at hadmX ⊢
  exact qDougall_orbit3_param hr (by omega) (by omega) (by omega) (by omega) hadmX hadmQ

/-- **`QDougallAt` for the third orbit, untruncated range**: the lowest third colour is `B - A`, the
lowest sixth colour is `E - A`, and the third colours run up to `B + A`, below `E + F`. -/
theorem qDougallAt_O3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : A ≤ B) (hE : A ≤ E) (hnd : B + A < E + F)
    (hx : aLo B A E F = B - A) (hq : aLo B F E A = E - A) (htop : aHi r B A E F = B + A) :
    QDougallAt r B A E F := by
  have hqf := hq1; have hqe := hq2
  unfold qAdm Lightlike.Pentagon.Tri at hq1 hq2
  have hparX : (B + A + E + F) % 2 = 0 := by omega
  have hparQ : (B + F + E + A) % 2 = 0 := by omega
  have iffX := adm_pair_iff hr hparX
  have iffQ := adm_pair_iff hr hparQ
  obtain ⟨xLpar, xHpar, -, -, -⟩ :=
    pair_facts (r := r) (a := B) (b := A) (c := E) (d := F) hparX (by omega) (by omega)
  obtain ⟨qLpar, qHpar, -, -, -⟩ :=
    pair_facts (r := r) (a := B) (b := F) (c := E) (d := A) hparQ (by omega) (by omega)
  have hqmem := (iffQ q).1 ⟨hqf, hqe⟩
  have hqL := (iffQ (aLo B F E A)).2 ⟨le_rfl, by omega, qLpar, hqmem.2.2.2⟩
  unfold QDougallAt
  rw [hx, htop, hq]
  have hxle : B - A ≤ B + A := by omega
  have hadmX : ∀ k ≤ ((B + A) - (B - A)) / 2, qAdm r B A (B - A + 2 * k) ∧
      qAdm r E F (B - A + 2 * k) := by
    intro k hk
    rw [iffX]
    rw [hx, htop]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  rw [hq] at hqL
  rw [show ((B + A) - (B - A)) / 2 = A by omega] at hadmX ⊢
  exact qDougall_orbit3 hr hA hE hnd (n := (E + F - (B - A)) / 2) (by omega) hadmX hqL

/-- The third orbit, untruncated, for the image under `(B E)(A F)`. -/
theorem qDougallAt_O3_k1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : F ≤ E) (hE : F ≤ B) (hnd : E + F < B + A)
    (hx : aLo E F B A = E - F) (hq : aLo E A B F = B - F) (htop : aHi r E F B A = E + F) :
    QDougallAt r B A E F :=
  (qDougallAt_k1 r B A E F).1 (qDougallAt_O3 hr E F B A q hq2 hq1 hA hE hnd hx hq htop)

/-- The third orbit, untruncated, for the image under `(B A)(E F)`. -/
theorem qDougallAt_O3_k2 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : B ≤ A) (hE : B ≤ F) (hnd : A + B < F + E)
    (hx : aLo A B F E = A - B) (hq : aLo A E F B = F - B) (htop : aHi r A B F E = A + B) :
    QDougallAt r B A E F :=
  (qDougallAt_k2 r B A E F).1 (qDougallAt_O3 hr A B F E q (qAdm_swap12 hq2) (qAdm_swap12 hq1)
    hA hE hnd hx hq htop)

/-- The third orbit, untruncated, for the image under `(B F)(A E)`. -/
theorem qDougallAt_O3_k3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q)
    (hq2 : qAdm r E A q) (hA : E ≤ F) (hE : E ≤ A) (hnd : F + E < A + B)
    (hx : aLo F E A B = F - E) (hq : aLo F B A E = A - E) (htop : aHi r F E A B = F + E) :
    QDougallAt r B A E F :=
  (qDougallAt_k3 r B A E F).1 (qDougallAt_O3 hr F E A B q (qAdm_swap12 hq1) (qAdm_swap12 hq2)
    hA hE hnd hx hq htop)

/-- The reflection of the quantum factorial: `[m]! · [r-1-m]! = [r-1]!` for `m ≤ r - 1`, from
`[r - k] = [k]`. -/
theorem qfact_mul_qfact_reflect {r m : ℕ} (hr : 2 ≤ r) (hm : m + 1 ≤ r) :
    qfact r m * qfact r (r - 1 - m) = qfact r (r - 1) := by
  obtain ⟨t, ht⟩ : ∃ t, r - 1 = m + t := ⟨r - 1 - m, by omega⟩
  rw [ht, show m + t - m = t by omega]
  unfold qfact
  rw [prod_range_add]
  congr 1
  rw [← prod_range_reflect]
  refine prod_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  rw [show m + i + 1 = r - (t - 1 - i + 1) by omega, qnum_sub hr (by omega)]

/-- **The summand of the `₆φ₅` series is symmetric in `b`, `c` and `x⁻¹`**: exchanging `b` with `x⁻¹`
(and `x` with `b⁻¹`). -/
theorem Tj_perm {q a b c x : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0) (k : ℕ) :
    Tj q a x⁻¹ c b⁻¹ k = Tj q a b c x k := by
  unfold Tj
  have e1 : a * q / x⁻¹ = a * q * x := by field_simp
  have e2 : a * q * b⁻¹ = a * q / b := by field_simp
  have e3 : a * q / b / (x⁻¹ * c) = a * q * x / (b * c) := by field_simp
  rw [e1, e2, e3]
  simp only [inv_inv]
  generalize pk a q k = A
  generalize pk b q k = B
  generalize pk c q k = C
  generalize pk x⁻¹ q k = X
  generalize pk (a * q * x) q k = P
  generalize pk (a * q / b) q k = R
  ring

/-- **A balanced ratio of four Pochhammer symbols at powers of `Q = uC r ^ 2`, with positive
exponents, as a ratio of quantum factorials.** The exponents `e1 + e2 = e3 + e4` balance, so the
powers of `uC r` cancel. -/
theorem pk_ratio_pos {r : ℕ} (hr : 2 ≤ r) {e1 e2 e3 e4 K : ℕ} (h1 : 1 ≤ e1) (h2 : 1 ≤ e2)
    (h3 : 1 ≤ e3) (h4 : 1 ≤ e4) (hbal : e1 + e2 = e3 + e4) (b1 : e1 - 1 + K < r)
    (b2 : e2 - 1 + K < r) (b3 : e3 - 1 + K < r) (b4 : e4 - 1 + K < r) :
    pk ((uC r ^ 2) ^ e1) (uC r ^ 2) K * pk ((uC r ^ 2) ^ e2) (uC r ^ 2) K /
        (pk ((uC r ^ 2) ^ e3) (uC r ^ 2) K * pk ((uC r ^ 2) ^ e4) (uC r ^ 2) K) =
      (((qfact r (e1 - 1 + K) / qfact r (e1 - 1)) * (qfact r (e2 - 1 + K) / qfact r (e2 - 1)) /
        ((qfact r (e3 - 1 + K) / qfact r (e3 - 1)) * (qfact r (e4 - 1 + K) / qfact r (e4 - 1))) :
          ℝ) : ℂ) := by
  have hu : uC r ≠ 0 := uC_ne_zero r
  have z : ∀ e : ℕ, (uC r ^ 2) ^ e = (uC r ^ 2) ^ (e : ℤ) := fun e => (zpow_natCast _ e).symm
  rw [z e1, z e2, z e3, z e4, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr, pk_Q_zpow hr]
  have pf : ∀ m : ℕ, m < r → 0 < qfact r m := fun m h => qfact_pos hr h
  have g : ∀ e : ℕ, 1 ≤ e → e - 1 + K < r →
      ∏ i ∈ range K, qZ r ((e : ℤ) + i) = qfact r (e - 1 + K) / qfact r (e - 1) := by
    intro e he hb
    rw [eq_div_iff (pf _ (by omega)).ne']
    have := prod_qnum (r := r) (e - 1) K hb hr
    rw [← this]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [show (e : ℤ) + i = ((e - 1 + 1 + i : ℕ) : ℤ) by push_cast; omega, qZ_natCast]
  have hsum : ∀ e : ℤ, ∑ i ∈ range K, (e + (i : ℤ)) = K * e + ∑ i ∈ range K, (i : ℤ) := by
    intro e; simp [sum_add_distrib]
  have hb : uC r ^ (∑ i ∈ range K, ((e1 : ℤ) + (i : ℤ))) * uC r ^ (∑ i ∈ range K, ((e2 : ℤ) + (i : ℤ))) =
      uC r ^ (∑ i ∈ range K, ((e3 : ℤ) + (i : ℤ))) * uC r ^ (∑ i ∈ range K, ((e4 : ℤ) + (i : ℤ))) := by
    rw [← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1
    rw [hsum, hsum, hsum, hsum]
    have : (e1 : ℤ) + e2 = e3 + e4 := by exact_mod_cast hbal
    linear_combination (K : ℤ) * this
  have ht := uC_sub_inv_ne hr
  have hX : (-(uC r - (uC r)⁻¹)) ^ K ≠ 0 := pow_ne_zero K (neg_ne_zero.2 ht)
  have hzp : ∀ z : ℤ, uC r ^ z ≠ 0 := fun z => zpow_ne_zero z hu
  have c1 := (pf (e1 - 1 + K) b1).ne'
  have c2 := (pf (e1 - 1) (by omega)).ne'
  have c3 := (pf (e2 - 1 + K) b2).ne'
  have c4 := (pf (e2 - 1) (by omega)).ne'
  have c5 := (pf (e3 - 1 + K) b3).ne'
  have c6 := (pf (e3 - 1) (by omega)).ne'
  have c7 := (pf (e4 - 1 + K) b4).ne'
  have c8 := (pf (e4 - 1) (by omega)).ne'
  simp only [← Complex.ofReal_prod]
  rw [g e1 h1 b1, g e2 h2 b2, g e3 h3 b3, g e4 h4 b4]
  have z1 := hzp (∑ i ∈ range K, ((e1 : ℤ) + (i : ℤ)))
  have z2 := hzp (∑ i ∈ range K, ((e2 : ℤ) + (i : ℤ)))
  have z3 := hzp (∑ i ∈ range K, ((e3 : ℤ) + (i : ℤ)))
  have z4 := hzp (∑ i ∈ range K, ((e4 : ℤ) + (i : ℤ)))
  generalize uC r ^ (∑ i ∈ range K, ((e1 : ℤ) + (i : ℤ))) = Z1 at *
  generalize uC r ^ (∑ i ∈ range K, ((e2 : ℤ) + (i : ℤ))) = Z2 at *
  generalize uC r ^ (∑ i ∈ range K, ((e3 : ℤ) + (i : ℤ))) = Z3 at *
  generalize uC r ^ (∑ i ∈ range K, ((e4 : ℤ) + (i : ℤ))) = Z4 at *
  generalize (-(uC r - (uC r)⁻¹)) ^ K = X at *
  have hZ4 : Z4 = Z1 * Z2 / Z3 := by
    rw [eq_div_iff z3]; linear_combination (-1 : ℂ) * hb
  rw [hZ4]
  push_cast
  field_simp

/-- **The truncated right side equals the untruncated one.** With `K + m + d + 2 = r` (the
level cut-off), the ratio of quantum factorials from Jackson's sum for the terminating parameter
`Q^K` equals the one for the terminating parameter `Q^n`, by `[x]! · [r-1-x]! = [r-1]!`. -/
theorem rhs_trunc_eq {r d m n j5 K : ℕ} (hr : 2 ≤ r) (hK : K + m + d + 2 = r) (hnm : n ≤ m)
    (hj5 : j5 ≤ m + d) (hnj : n ≤ j5) (hj5' : j5 ≤ d + n) :
    (qfact r (d + 1 + K) / qfact r (d + 1)) * (qfact r (j5 + K) / qfact r j5) /
        ((qfact r (d + n + 1 + K) / qfact r (d + n + 1)) *
          (qfact r (j5 - n + K) / qfact r (j5 - n))) =
      (qfact r (d + n + 1) / qfact r (d + 1)) *
        (qfact r (m + (d + n + 1 - j5)) / qfact r (m + (d + n + 1 - j5) - n)) /
        ((qfact r m / qfact r (m - n)) * (qfact r j5 / qfact r (j5 - n))) := by
  have pos : ∀ x : ℕ, x < r → 0 < qfact r x := fun x h => qfact_pos hr h
  have R1 := qfact_mul_qfact_reflect hr (m := m) (by omega)
  have R2 := qfact_mul_qfact_reflect hr (m := m + d + 1 - j5) (by omega)
  have R3 := qfact_mul_qfact_reflect hr (m := m - n) (by omega)
  have R4 := qfact_mul_qfact_reflect hr (m := m + d + 1 - j5 + n) (by omega)
  rw [show r - 1 - m = d + 1 + K by omega] at R1
  rw [show r - 1 - (m + d + 1 - j5) = j5 + K by omega] at R2
  rw [show r - 1 - (m - n) = d + n + 1 + K by omega] at R3
  rw [show r - 1 - (m + d + 1 - j5 + n) = j5 - n + K by omega] at R4
  rw [show m + (d + n + 1 - j5) = m + d + 1 - j5 + n by omega,
    show m + d + 1 - j5 + n - n = m + d + 1 - j5 by omega]
  have p1 := (pos m (by omega)).ne'
  have p2 := (pos (d + 1) (by omega)).ne'
  have p3 := (pos j5 (by omega)).ne'
  have p4 := (pos (m + d + 1 - j5) (by omega)).ne'
  have p5 := (pos (m - n) (by omega)).ne'
  have p6 := (pos (d + n + 1) (by omega)).ne'
  have p7 := (pos (j5 - n) (by omega)).ne'
  have p8 := (pos (m + d + 1 - j5 + n) (by omega)).ne'
  have p9 := (pos (r - 1) (by omega)).ne'
  have f1 : qfact r (d + 1 + K) = qfact r (r - 1) / qfact r m := by rw [← R1]; field_simp
  have f2 : qfact r (j5 + K) = qfact r (r - 1) / qfact r (m + d + 1 - j5) := by rw [← R2]; field_simp
  have f3 : qfact r (d + n + 1 + K) = qfact r (r - 1) / qfact r (m - n) := by rw [← R3]; field_simp
  have f4 : qfact r (j5 - n + K) = qfact r (r - 1) / qfact r (m + d + 1 - j5 + n) := by
    rw [← R4]; field_simp
  rw [f1, f2, f3, f4]
  field_simp

/-- `Q ^ (2 r) = 1` for `Q = uC r ^ 2`, in the form `Q ^ r = 1`. -/
lemma Q_pow_r {r : ℕ} (hr : 2 ≤ r) : (uC r ^ 2) ^ r = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, uC_pow_self hr]; norm_num

/-- `JHypT` for the terminating parameter `b = (Q^n)⁻¹` of length `K`, with `a = Q^(d+1)` and
`c = Q^ec`: the exponents of `Q` stay between `0` and `r`. -/
theorem jhypT_trunc {r : ℕ} (hr : 2 ≤ r) {d n ec K : ℕ} (h1 : K + 1 < r) (h2 : d + 1 < r)
    (h3 : d + 2 + n + K < r) (hec : ec ≤ d + 1) (h4 : d + 2 - ec + K < r)
    (h5 : d + 1 + 2 * K < r) (hec0 : 0 < ec) :
    JHypT (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ n)⁻¹ ((uC r ^ 2) ^ ec) K := by
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have ne : ∀ m : ℤ, 0 < m → m < r → 1 - (uC r ^ 2) ^ m ≠ 0 := fun m h0 h1 => Qne_pos hr h0 h1
  have e1 : ∀ i : ℕ, 1 - (uC r ^ 2) * (uC r ^ 2) ^ i = 1 - (uC r ^ 2) ^ ((1 + i : ℕ) : ℤ) := by
    intro i; rw [zpow_natCast, pow_add, pow_one]
  have hpowQ : ∀ e : ℕ, (uC r ^ 2) ^ e = (uC r ^ 2) ^ (e : ℤ) := fun e => (zpow_natCast _ e).symm
  have f3 : ∀ i : ℕ, (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / ((uC r ^ 2) ^ n)⁻¹ * (uC r ^ 2) ^ i =
      (uC r ^ 2) ^ ((d + 2 + n + i : ℕ) : ℤ) := by
    intro i; rw [zpow_natCast]; field_simp; ring
  have f4 : ∀ i : ℕ, (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) / (uC r ^ 2) ^ ec * (uC r ^ 2) ^ i =
      (uC r ^ 2) ^ ((d + 2 - ec + i : ℕ) : ℤ) := by
    intro i
    rw [zpow_natCast, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hQ), ← pow_succ, ← pow_add,
      ← pow_add]
    congr 1; omega
  have f5 : ∀ m i : ℕ, (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ m * (uC r ^ 2) ^ i =
      (uC r ^ 2) ^ ((d + 2 + m + i : ℕ) : ℤ) := by
    intro m i; rw [zpow_natCast]; ring
  have f6 : ∀ m : ℕ, (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ m / ((uC r ^ 2) ^ n)⁻¹ =
      (uC r ^ 2) ^ ((d + 2 + m + n : ℕ) : ℤ) := by
    intro m; rw [zpow_natCast]; field_simp; ring
  have f7 : ∀ m : ℕ, (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) * (uC r ^ 2) ^ m / (uC r ^ 2) ^ ec =
      (uC r ^ 2) ^ ((d + 2 + m - ec : ℕ) : ℤ) := by
    intro m
    rw [zpow_natCast, div_eq_iff (pow_ne_zero _ hQ), ← pow_succ, ← pow_add, ← pow_add]
    congr 1; omega
  unfold JHypT
  refine ⟨hQ, inv_ne_zero (pow_ne_zero _ hQ), pow_ne_zero _ hQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpowQ]; exact ne (d + 1) (by exact_mod_cast Nat.succ_pos d) (by exact_mod_cast h2)
  · intro i hi; rw [e1]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro i hi; rw [f3]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro i hi; rw [f4]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro m hm i hi; rw [f5]; exact ne _ (by push_cast; omega) (by push_cast; omega)
  · intro m hm
    constructor
    · rw [f6]; exact ne _ (by push_cast; omega) (by push_cast; omega)
    · rw [f7]; exact ne _ (by push_cast; omega) (by push_cast; omega)

/-- **The boundary evaluation `QDougall`, level-truncated first orbit, `n < m`.** The third colours
`d, ..., d + 2K` stop at the level cut-off `K + m + d + 2 = r`; the terminating parameter of Jackson's
sum is `Q^K = b⁻¹`, `b = Q^(m+d+2)` (`Q^r = 1`), after exchanging `b` with `x⁻¹` (`Tj_perm`).
Limits: only `n < m` (that is `j4 + j5 < j1 + j2`); the case `n = m`, where two factors of Jackson's
right side vanish together, is not covered here. -/
theorem qDougall_trunc_param {r d m n j5 K : ℕ} (hr : 2 ≤ r) (hK : K + m + d + 2 = r)
    (hKn : K ≤ n) (hnm : n < m) (hnj : n ≤ j5) (hj5 : j5 ≤ d + n) (hj5m : j5 ≤ m + d)
    (hadmX : ∀ k ≤ K, qAdm r (m + d) m (d + 2 * k) ∧ qAdm r (d + 2 * n - j5) j5 (d + 2 * k))
    (hadmQ : qAdm r (m + d) j5 (m + d - j5) ∧ qAdm r (d + 2 * n - j5) m (m + d - j5)) :
    QDougall r (m + d) m (d + 2 * n - j5) j5 d K (m + d - j5) := by
  have hX' : ∀ k ≤ K, qAdm r (m + d) m (m + d - m + 2 * k) ∧
      qAdm r (d + 2 * n - j5) j5 (m + d - m + 2 * k) := by
    simpa only [Nat.add_sub_cancel_left] using hadmX
  have hmap := wTerm_eq_Tj_N hr (j1 := m + d) (j2 := m) (j4 := d + 2 * n - j5) (j5 := j5) (n := n)
    (N := K) (by omega) (by omega) (by omega) (by omega) hKn hX' hadmQ
  have e1 : m + d - m + 1 = d + 1 := by omega
  have e2 : (m + d - m + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  have e2' : (d + (d + 2 * n - j5) - j5) / 2 + 1 = d + n + 1 - j5 := by omega
  have e3 : m + d + 2 = m + d + 2 := rfl
  simp only [Nat.add_sub_cancel_left, e1, e2, e2'] at hmap
  obtain ⟨_, bQ1⟩ := hadmQ.1
  obtain ⟨_, bQ2⟩ := hadmQ.2
  obtain ⟨_, bX0⟩ := (hadmX 0 (by omega)).1
  obtain ⟨_, bY0⟩ := (hadmX 0 (by omega)).2
  have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
  have hQr := Q_pow_r hr
  have hbinv : ((uC r ^ 2) ^ (m + d + 2))⁻¹ = (uC r ^ 2) ^ K := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show m + d + 2 + K = r by omega, hQr]
  have hmap' : ∀ k ≤ K, (wTerm r (m + d) m (d + 2 * n - j5) j5 k : ℂ) =
      (wTerm r (m + d) m (d + 2 * n - j5) j5 0 : ℂ) *
        Tj (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ n)⁻¹ ((uC r ^ 2) ^ (d + n + 1 - j5))
          ((uC r ^ 2) ^ K) k := by
    intro k hk
    rw [hmap k hk, ← hbinv, Tj_perm (pow_ne_zero _ hQ) (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)]
  have jh := jhypT_trunc hr (d := d) (n := n) (ec := d + n + 1 - j5) (K := K) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have jsum := jackson_sumT jh K le_rfl
  have hA : (uC r ^ 2) ^ (d + 1) * (uC r ^ 2) = (uC r ^ 2) ^ (d + 2) := by ring
  have hBC : (uC r ^ 2) ^ (d + 2) / (((uC r ^ 2) ^ n)⁻¹ * (uC r ^ 2) ^ (d + n + 1 - j5)) =
      (uC r ^ 2) ^ (j5 + 1) := by
    rw [div_eq_iff (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hQ)) (pow_ne_zero _ hQ))]
    calc (uC r ^ 2) ^ (d + 2) = (uC r ^ 2) ^ (j5 + 1 + (d + n + 1 - j5)) * ((uC r ^ 2) ^ n)⁻¹ := by
          rw [show j5 + 1 + (d + n + 1 - j5) = d + 2 + n by omega, pow_add _ (d + 2) n]
          field_simp
      _ = _ := by rw [pow_add]; ring
  have hB : (uC r ^ 2) ^ (d + 2) / ((uC r ^ 2) ^ n)⁻¹ = (uC r ^ 2) ^ (d + 2 + n) := by
    rw [div_inv_eq_mul, pow_add _ (d + 2) n]
  have hC : (uC r ^ 2) ^ (d + 2) / (uC r ^ 2) ^ (d + n + 1 - j5) = (uC r ^ 2) ^ (j5 - n + 1) := by
    rw [div_eq_iff (pow_ne_zero _ hQ), ← pow_add]
    congr 1; omega
  have hRhs : jacksonRhs (uC r ^ 2) ((uC r ^ 2) ^ (d + 1)) ((uC r ^ 2) ^ n)⁻¹
      ((uC r ^ 2) ^ (d + n + 1 - j5)) K =
      (((qfact r (d + 1 + K) / qfact r (d + 1)) * (qfact r (j5 + K) / qfact r j5) /
        ((qfact r (d + n + 1 + K) / qfact r (d + n + 1)) *
          (qfact r (j5 - n + K) / qfact r (j5 - n))) : ℝ) : ℂ) := by
    unfold jacksonRhs
    rw [hA, hBC, hB, hC]
    have := pk_ratio_pos hr (e1 := d + 2) (e2 := j5 + 1) (e3 := d + 2 + n) (e4 := j5 - n + 1)
      (K := K) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    rw [this]
    rw [show d + 2 - 1 = d + 1 by omega, show j5 + 1 - 1 = j5 by omega,
      show d + 2 + n - 1 = d + n + 1 by omega, show j5 - n + 1 - 1 = j5 - n by omega]
  have hTr := rhs_trunc_eq (r := r) (d := d) (m := m) (n := n) (j5 := j5) (K := K) hr hK
    (by omega) hj5m hnj hj5
  have sumC : (∑ k ∈ range (K + 1), (wTerm r (m + d) m (d + 2 * n - j5) j5 k : ℂ)) =
      (wTerm r (m + d) m (d + 2 * n - j5) j5 0 : ℂ) *
        ((((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (m + (d + n + 1 - j5)) / qfact r (m + (d + n + 1 - j5) - n)) /
          ((qfact r m / qfact r (m - n)) * (qfact r j5 / qfact r (j5 - n)))) : ℝ) : ℂ) := by
    rw [sum_congr rfl (fun k hk => hmap' k (by simp only [mem_range] at hk; omega)), ← mul_sum,
      jsum, hRhs, hTr]
  have sumR : ∑ k ∈ range (K + 1), wTerm r (m + d) m (d + 2 * n - j5) j5 k =
      wTerm r (m + d) m (d + 2 * n - j5) j5 0 *
        ((qfact r (d + n + 1) / qfact r (d + 1)) *
          (qfact r (m + (d + n + 1 - j5)) / qfact r (m + (d + n + 1 - j5) - n)) /
          ((qfact r m / qfact r (m - n)) * (qfact r j5 / qfact r (j5 - n)))) := by
    exact_mod_cast sumC
  exact qDougall_of_sumR_N hr hnj hj5 hnm.le hKn hadmX hadmQ sumR

end Lightlike.TV.Refl
