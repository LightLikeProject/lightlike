import Lightlike.TuraevViro.Reflect.QDougallMap

/-!
# The q-Racah sum is a balanced `₄φ₃` series

The q-Racah sum of the quantum 6j symbol, `qRacahSum`, is a sum over `z` of `qRacahTerm`. Seen from its
first nonzero term `z = a1`, where `a1` is the largest of the four triad sums, it is a terminating balanced
basic hypergeometric series `₄φ₃` at `Q = u²`, `u = e^{iπ/r}`, with upper parameters `Q^{a1+2}` and
`Q^{-(b_j - a1)}` (`j = 1, 2, 3`), lower parameters `Q^{a1+1-a_i}` (`i = 2, 3, 4`) and argument `Q`. This is the
form to which the transformations of terminating `₈φ₇` series apply.

## Main results

* `racahTerm_succ`: the ratio of consecutive terms of the q-Racah sum, as quantum integers (cross-multiplied).
* `racahTerm_ratioC`: the same ratio as a ratio of `Q`-powers `1 - Q^m`; the balance
  `b1 + b2 + b3 = a1 + a2 + a3 + a4` cancels the powers of `u`.
* `phi43Term`, `racahTerm_eq_phi43`: the term at `z = a1 + k` is the term at `z = a1` times `phi43Term k`.
* `racahSum_eq_phi43`: the sum over `z < N` is the first term times the `₄φ₃` series.

## Implementation notes

The hypotheses of `racahSum_eq_phi43` state the bounds that make every quantum integer divided by nonzero;
they hold for admissible 6j symbols (every `b_j - a_i` is at most `r - 2`). The identity was also checked
numerically at `r = 7, 9, 11` with the argument fitted from the first term ratio: it is exactly `Q`, with a
relative error below `3e-15`.
-/

namespace Lightlike.TV.Refl
open Finset Lightlike.TV

/-- `1/[m+1]! · [m+1] = 1/[m]!` when `[m+1] ≠ 0`. -/
lemma invQFact_succ_mul {r : ℕ} (m : ℕ) (h : qnum r (m + 1) ≠ 0) :
    invQFact r ((m + 1 : ℕ) : ℤ) * qnum r (m + 1) = invQFact r (m : ℤ) := by
  rw [invQFact_nat, invQFact_nat, qfact_succ' r m]
  rcases eq_or_ne (qfact r m) 0 with hq | hq
  · simp [hq]
  · field_simp

/-- `1/[m]! = [m+1]/[m+1]!` shifted: `1/[b-z-1]! = (1/[b-z]!) · [b - z]` when `[b - z] ≠ 0`. -/
lemma invQFact_pred {r : ℕ} (m : ℕ) (h : qnum r (m + 1) ≠ 0) :
    invQFact r (m : ℤ) = invQFact r ((m + 1 : ℕ) : ℤ) * qnum r (m + 1) :=
  (invQFact_succ_mul m h).symm

/-- The term ratio of the q-Racah sum (cross-multiplied): for `a_i ≤ z` and `z + 1 ≤ b_j`,
`t(z+1) ∏ [z+1-a_i] = - t(z) [z+2] ∏ [b_j - z]`, when the quantum integers that are divided by
do not vanish (all arguments are below `r`). -/
lemma racahTerm_succ {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 z : ℕ}
    (h1 : a1 ≤ z) (h2 : a2 ≤ z) (h3 : a3 ≤ z) (h4 : a4 ≤ z)
    (g1 : b1 ≥ z + 1) (g2 : b2 ≥ z + 1) (g3 : b3 ≥ z + 1)
    (c1 : z + 1 - a1 < r) (c2 : z + 1 - a2 < r) (c3 : z + 1 - a3 < r) (c4 : z + 1 - a4 < r)
    (d1 : b1 - z < r) (d2 : b2 - z < r) (d3 : b3 - z < r) :
    qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (z + 1) *
        (qnum r (z + 1 - a1) * qnum r (z + 1 - a2) * qnum r (z + 1 - a3) * qnum r (z + 1 - a4)) =
      - (qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z *
        (qnum r (z + 2) * qnum r (b1 - z) * qnum r (b2 - z) * qnum r (b3 - z))) := by
  have nz : ∀ m : ℕ, 0 < m → m < r → qnum r m ≠ 0 := fun m h0 h1 => (qnum_pos hr h0 h1).ne'
  have e : ∀ a : ℕ, a ≤ z → z + 1 - a < r → invQFact r (((z + 1 : ℕ) : ℤ) - a) * qnum r (z + 1 - a) =
      invQFact r ((z : ℤ) - a) := by
    intro a ha hlt
    have := invQFact_succ_mul (r := r) (z - a)
      (by rw [show z - a + 1 = z + 1 - a by omega]; exact nz _ (by omega) hlt)
    rw [show ((z + 1 : ℕ) : ℤ) - a = ((z - a + 1 : ℕ) : ℤ) by push_cast; omega,
      show ((z : ℤ) - a) = ((z - a : ℕ) : ℤ) by push_cast; omega,
      show z + 1 - a = z - a + 1 by omega]
    exact this
  have f : ∀ b : ℕ, z + 1 ≤ b → b - z < r → invQFact r ((b : ℤ) - ((z + 1 : ℕ) : ℤ)) =
      invQFact r ((b : ℤ) - z) * qnum r (b - z) := by
    intro b hb hlt
    have := invQFact_pred (r := r) (b - z - 1)
      (by rw [show b - z - 1 + 1 = b - z by omega]; exact nz _ (by omega) hlt)
    rw [show b - z - 1 + 1 = b - z by omega] at this
    rw [show (b : ℤ) - ((z + 1 : ℕ) : ℤ) = ((b - z - 1 : ℕ) : ℤ) by push_cast; omega,
      show (b : ℤ) - z = ((b - z : ℕ) : ℤ) by push_cast; omega]
    exact this
  unfold qRacahTerm
  rw [qfact_succ' r (z + 1), ← e a1 h1 c1, ← e a2 h2 c2, ← e a3 h3 c3, ← e a4 h4 c4,
    f b1 g1 d1, f b2 g2 d2, f b3 g3 d3]
  rw [show z + 1 + 1 = z + 2 by ring]
  ring


/-- **The term ratio of the q-Racah sum as a ratio of `Q`-powers** (`Q = uC r ^ 2`), cross-multiplied.
With `z = z0 + k` where `z0 = a1`, `m_j = b_j - z0`, `l_i = 1 + z0 - a_i`:
`t(z+1) (1 - Q^{k+1}) ∏ (1 - Q^{l_i + k}) = t(z) · Q · (1 - Q^{z0+2+k}) ∏ (1 - Q^{k - m_j})`.
The balance `b1 + b2 + b3 = a1 + a2 + a3 + a4` makes the powers of `u` cancel. -/
lemma racahTerm_ratioC {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 k : ℕ}
    (hbal : b1 + b2 + b3 = a1 + a2 + a3 + a4)
    (h2 : a2 ≤ a1) (h3 : a3 ≤ a1) (h4 : a4 ≤ a1)
    (g1 : a1 + k + 1 ≤ b1) (g2 : a1 + k + 1 ≤ b2) (g3 : a1 + k + 1 ≤ b3)
    (c1 : k + 1 < r) (c2 : a1 + k + 1 - a2 < r) (c3 : a1 + k + 1 - a3 < r) (c4 : a1 + k + 1 - a4 < r)
    (d1 : b1 - a1 - k < r) (d2 : b2 - a1 - k < r) (d3 : b3 - a1 - k < r) :
    ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (a1 + k + 1) : ℝ) : ℂ) *
        ((1 - (uC r ^ 2) ^ ((k : ℤ) + 1)) * (1 - (uC r ^ 2) ^ ((a1 + k + 1 - a2 : ℕ) : ℤ)) *
          (1 - (uC r ^ 2) ^ ((a1 + k + 1 - a3 : ℕ) : ℤ)) * (1 - (uC r ^ 2) ^ ((a1 + k + 1 - a4 : ℕ) : ℤ))) =
      ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (a1 + k) : ℝ) : ℂ) * (uC r ^ 2) *
        ((1 - (uC r ^ 2) ^ ((a1 + k + 2 : ℕ) : ℤ)) * (1 - (uC r ^ 2) ^ ((k : ℤ) - ((b1 - a1 : ℕ) : ℤ))) *
          (1 - (uC r ^ 2) ^ ((k : ℤ) - ((b2 - a1 : ℕ) : ℤ))) *
          (1 - (uC r ^ 2) ^ ((k : ℤ) - ((b3 - a1 : ℕ) : ℤ)))) := by
  have R := racahTerm_succ hr (z := a1 + k) (a1 := a1) (a2 := a2) (a3 := a3) (a4 := a4) (b1 := b1)
    (b2 := b2) (b3 := b3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) c2 c3 c4 (by omega) (by omega) (by omega)
  rw [show a1 + k + 1 - a1 = k + 1 by omega] at R
  have R' := congrArg (fun x : ℝ => (x : ℂ)) R
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at R'
  have hu : uC r ≠ 0 := uC_ne_zero r
  have F : ∀ e : ℤ, 1 - (uC r ^ 2) ^ e = - uC r ^ e * (uC r - (uC r)⁻¹) * ((qZ r e : ℝ) : ℂ) :=
    fun e => one_sub_Q_qZ hr e
  rw [F ((k : ℤ) + 1), F ((a1 + k + 1 - a2 : ℕ) : ℤ), F ((a1 + k + 1 - a3 : ℕ) : ℤ),
    F ((a1 + k + 1 - a4 : ℕ) : ℤ), F ((a1 + k + 2 : ℕ) : ℤ), F ((k : ℤ) - ((b1 - a1 : ℕ) : ℤ)),
    F ((k : ℤ) - ((b2 - a1 : ℕ) : ℤ)), F ((k : ℤ) - ((b3 - a1 : ℕ) : ℤ))]
  have q1 : qZ r ((k : ℤ) + 1) = qnum r (k + 1) := by
    rw [← qZ_natCast]; push_cast; ring_nf
  have q5 : ∀ m : ℕ, qZ r (m : ℤ) = qnum r m := qZ_natCast r
  have q6 : ∀ m : ℕ, k ≤ m → qZ r ((k : ℤ) - m) = - qnum r (m - k) := by
    intro m hm
    rw [show (k : ℤ) - m = -((m - k : ℕ) : ℤ) by push_cast; omega, qZ_neg, qZ_natCast]
  rw [q1, q5, q5, q5, q5, q6 _ (by omega), q6 _ (by omega), q6 _ (by omega)]
  have hexp : uC r ^ ((k : ℤ) + 1) * uC r ^ ((a1 + k + 1 - a2 : ℕ) : ℤ) *
        uC r ^ ((a1 + k + 1 - a3 : ℕ) : ℤ) * uC r ^ ((a1 + k + 1 - a4 : ℕ) : ℤ) =
      uC r ^ 2 * (uC r ^ ((a1 + k + 2 : ℕ) : ℤ) * uC r ^ ((k : ℤ) - ((b1 - a1 : ℕ) : ℤ)) *
        uC r ^ ((k : ℤ) - ((b2 - a1 : ℕ) : ℤ)) * uC r ^ ((k : ℤ) - ((b3 - a1 : ℕ) : ℤ))) := by
    have e2 : (uC r ^ 2 : ℂ) = uC r ^ (2 : ℤ) := by norm_cast
    rw [e2, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu, ← zpow_add₀ hu,
      ← zpow_add₀ hu, ← zpow_add₀ hu]
    congr 1
    push_cast [Nat.cast_sub (by omega : a2 ≤ a1 + k + 1), Nat.cast_sub (by omega : a3 ≤ a1 + k + 1),
      Nat.cast_sub (by omega : a4 ≤ a1 + k + 1), Nat.cast_sub (by omega : a1 ≤ b1),
      Nat.cast_sub (by omega : a1 ≤ b2), Nat.cast_sub (by omega : a1 ≤ b3)]
    have : (b1 : ℤ) + b2 + b3 = a1 + a2 + a3 + a4 := by exact_mod_cast hbal
    linarith
  have hn1 : qnum r (b1 - (a1 + k)) = qnum r (b1 - a1 - k) := by rw [show b1 - (a1 + k) = b1 - a1 - k by omega]
  have hn2 : qnum r (b2 - (a1 + k)) = qnum r (b2 - a1 - k) := by rw [show b2 - (a1 + k) = b2 - a1 - k by omega]
  have hn3 : qnum r (b3 - (a1 + k)) = qnum r (b3 - a1 - k) := by rw [show b3 - (a1 + k) = b3 - a1 - k by omega]
  rw [hn1, hn2, hn3] at R'
  simp only [Complex.ofReal_neg]
  generalize uC r - (uC r)⁻¹ = D
  linear_combination ((D ^ 4 * (uC r ^ ((k : ℤ) + 1) * uC r ^ ((a1 + k + 1 - a2 : ℕ) : ℤ) *
        uC r ^ ((a1 + k + 1 - a3 : ℕ) : ℤ) * uC r ^ ((a1 + k + 1 - a4 : ℕ) : ℤ))) : ℂ) * R' -
    (D ^ 4 * ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (a1 + k) : ℝ) : ℂ) *
      (((qnum r (a1 + k + 2) : ℝ) : ℂ) * ((qnum r (b1 - a1 - k) : ℝ) : ℂ) *
        ((qnum r (b2 - a1 - k) : ℝ) : ℂ) * ((qnum r (b3 - a1 - k) : ℝ) : ℂ))) * hexp


/-- The term of the balanced `₄φ₃` series that the q-Racah sum is (`Q = uC r ^ 2`):
`(Q^e0, Q^{-m1}, Q^{-m2}, Q^{-m3}; Q)_k / (Q, Q^{l2}, Q^{l3}, Q^{l4}; Q)_k · Q^k`. -/
noncomputable def phi43Term (r e0 m1 m2 m3 l2 l3 l4 k : ℕ) : ℂ :=
  pk ((uC r ^ 2) ^ e0) (uC r ^ 2) k * pk ((uC r ^ 2) ^ (-(m1 : ℤ))) (uC r ^ 2) k *
      pk ((uC r ^ 2) ^ (-(m2 : ℤ))) (uC r ^ 2) k * pk ((uC r ^ 2) ^ (-(m3 : ℤ))) (uC r ^ 2) k /
    (pk (uC r ^ 2) (uC r ^ 2) k * pk ((uC r ^ 2) ^ l2) (uC r ^ 2) k * pk ((uC r ^ 2) ^ l3) (uC r ^ 2) k *
      pk ((uC r ^ 2) ^ l4) (uC r ^ 2) k) * (uC r ^ 2) ^ k

/-- **The terms of the q-Racah sum are the terms of a balanced `₄φ₃` series.** With `z0 = a1` the
largest of the `a_i`, `m_j = b_j - a1` and `l_i = a1 + 1 - a_i`, for `k ≤ n` the term at `z = a1 + k` is the
term at `z = a1` times `phi43Term k`. -/
theorem racahTerm_eq_phi43 {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 n : ℕ}
    (hbal : b1 + b2 + b3 = a1 + a2 + a3 + a4) (h2 : a2 ≤ a1) (h3 : a3 ≤ a1) (h4 : a4 ≤ a1)
    (g1 : a1 + n ≤ b1) (g2 : a1 + n ≤ b2) (g3 : a1 + n ≤ b3)
    (hn : n < r) (c2 : a1 + n - a2 < r) (c3 : a1 + n - a3 < r) (c4 : a1 + n - a4 < r)
    (d1 : b1 - a1 < r) (d2 : b2 - a1 < r) (d3 : b3 - a1 < r) :
    ∀ k ≤ n, ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (a1 + k) : ℝ) : ℂ) =
      ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 a1 : ℝ) : ℂ) *
        phi43Term r (a1 + 2) (b1 - a1) (b2 - a1) (b3 - a1) (a1 + 1 - a2) (a1 + 1 - a3) (a1 + 1 - a4) k := by
  intro k
  induction k with
  | zero => intro _; simp [phi43Term, pk]
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hQ : uC r ^ 2 ≠ 0 := pow_ne_zero 2 (uC_ne_zero r)
    have R := racahTerm_ratioC hr (k := k) hbal h2 h3 h4 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have ne : ∀ m : ℤ, 0 < m → m < r → 1 - (uC r ^ 2) ^ m ≠ 0 := fun m h0 h1 => Qne_pos hr h0 h1
    have D1 := ne ((k : ℤ) + 1) (by omega) (by omega)
    have D2 := ne ((a1 + k + 1 - a2 : ℕ) : ℤ) (by omega) (by omega)
    have D3 := ne ((a1 + k + 1 - a3 : ℕ) : ℤ) (by omega) (by omega)
    have D4 := ne ((a1 + k + 1 - a4 : ℕ) : ℤ) (by omega) (by omega)
    have e1 : (uC r ^ 2) * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((k : ℤ) + 1) := by
      rw [zpow_add₀ hQ, zpow_natCast]; simp [mul_comm]
    have e2 : ∀ l : ℕ, (uC r ^ 2) ^ l * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((l + k : ℕ) : ℤ) := by
      intro l; rw [zpow_natCast, pow_add]
    have e3 : ∀ m : ℕ, (uC r ^ 2) ^ (-(m : ℤ)) * (uC r ^ 2) ^ k = (uC r ^ 2) ^ ((k : ℤ) - m) := by
      intro m
      rw [show (uC r ^ 2) ^ k = (uC r ^ 2) ^ (k : ℤ) from (zpow_natCast _ _).symm, ← zpow_add₀ hQ]
      congr 1; ring
    rw [← e1] at R D1
    have l2 := e2 (a1 + 1 - a2); rw [show a1 + 1 - a2 + k = a1 + k + 1 - a2 by omega] at l2
    have l3 := e2 (a1 + 1 - a3); rw [show a1 + 1 - a3 + k = a1 + k + 1 - a3 by omega] at l3
    have l4 := e2 (a1 + 1 - a4); rw [show a1 + 1 - a4 + k = a1 + k + 1 - a4 by omega] at l4
    have l0 := e2 (a1 + 2); rw [show a1 + 2 + k = a1 + k + 2 by omega] at l0
    rw [← l2, ← l3, ← l4, ← l0, ← e3, ← e3, ← e3] at R
    rw [← l2] at D2; rw [← l3] at D3; rw [← l4] at D4
    -- pk successor
    have pS : ∀ z q : ℂ, ∀ j : ℕ, pk z q (j + 1) = pk z q j * (1 - z * q ^ j) := fun z q j => rfl
    -- nonvanishing of the denominators of `phi43Term k`
    have e2g : ∀ l i : ℕ, (uC r ^ 2) ^ l * (uC r ^ 2) ^ i = (uC r ^ 2) ^ ((l + i : ℕ) : ℤ) := by
      intro l i; rw [zpow_natCast, pow_add]
    have pne : ∀ l : ℕ, 0 < l → l + k ≤ r → pk ((uC r ^ 2) ^ l) (uC r ^ 2) k ≠ 0 := by
      intro l hl hlk
      refine pk_ne_zero _ _ _ fun i hi => ?_
      rw [e2g]
      exact ne _ (by push_cast; omega) (by push_cast; omega)
    have p1 : pk (uC r ^ 2) (uC r ^ 2) k ≠ 0 := by
      have := pne 1 (by norm_num) (by omega); simpa [pow_one] using this
    have p2 := pne (a1 + 1 - a2) (by omega) (by omega)
    have p3 := pne (a1 + 1 - a3) (by omega) (by omega)
    have p4 := pne (a1 + 1 - a4) (by omega) (by omega)
    have hD0 : (1 - uC r ^ 2 * (uC r ^ 2) ^ k) * (1 - (uC r ^ 2) ^ (a1 + 1 - a2) * (uC r ^ 2) ^ k) *
        (1 - (uC r ^ 2) ^ (a1 + 1 - a3) * (uC r ^ 2) ^ k) * (1 - (uC r ^ 2) ^ (a1 + 1 - a4) * (uC r ^ 2) ^ k) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero D1 D2) D3) D4
    have hT := (eq_div_iff hD0).2 R
    unfold phi43Term at ihk ⊢
    simp only [pS]
    rw [pow_succ (uC r ^ 2) k, show a1 + (k + 1) = a1 + k + 1 by ring, hT, ihk]
    generalize hQ' : uC r ^ 2 = Q at *
    generalize pk (Q ^ (a1 + 2)) Q k = pa
    generalize pk (Q ^ (-((b1 - a1 : ℕ) : ℤ))) Q k = pb
    generalize pk (Q ^ (-((b2 - a1 : ℕ) : ℤ))) Q k = pc
    generalize pk (Q ^ (-((b3 - a1 : ℕ) : ℤ))) Q k = pd
    generalize pk Q Q k = pe
    generalize pk (Q ^ (a1 + 1 - a2)) Q k = pf
    generalize pk (Q ^ (a1 + 1 - a3)) Q k = pg
    generalize pk (Q ^ (a1 + 1 - a4)) Q k = ph
    generalize (1 - Q ^ (a1 + 2) * Q ^ k) = f0
    generalize (1 - Q ^ (-((b1 - a1 : ℕ) : ℤ)) * Q ^ k) = f1
    generalize (1 - Q ^ (-((b2 - a1 : ℕ) : ℤ)) * Q ^ k) = f2
    generalize (1 - Q ^ (-((b3 - a1 : ℕ) : ℤ)) * Q ^ k) = f3
    generalize (1 - Q * Q ^ k) = d0
    generalize (1 - Q ^ (a1 + 1 - a2) * Q ^ k) = d1
    generalize (1 - Q ^ (a1 + 1 - a3) * Q ^ k) = d2
    generalize (1 - Q ^ (a1 + 1 - a4) * Q ^ k) = d3
    ring


/-- **The q-Racah sum is a balanced `₄φ₃` series.** For `a1` the largest of `a1, ..., a4`, `n = min b_j - a1`,
the balance `b1 + b2 + b3 = a1 + a2 + a3 + a4`, the nonvanishing bounds below, and any `N > a1 + n`, the sum of
`qRacahTerm` over `z < N` is the term at `z = a1` times the `₄φ₃` series with upper parameters `Q^{a1+2}`,
`Q^{-(b_j - a1)}`, lower parameters `Q^{a1+1-a_i}` and argument `Q`, where `Q = uC r ^ 2`. -/
theorem racahSum_eq_phi43 {r : ℕ} (hr : 2 ≤ r) {a1 a2 a3 a4 b1 b2 b3 n N : ℕ}
    (hbal : b1 + b2 + b3 = a1 + a2 + a3 + a4) (h2 : a2 ≤ a1) (h3 : a3 ≤ a1) (h4 : a4 ≤ a1)
    (g1 : a1 + n ≤ b1) (g2 : a1 + n ≤ b2) (g3 : a1 + n ≤ b3)
    (hmin : b1 = a1 + n ∨ b2 = a1 + n ∨ b3 = a1 + n)
    (hn : n < r) (c2 : a1 + n - a2 < r) (c3 : a1 + n - a3 < r) (c4 : a1 + n - a4 < r)
    (d1 : b1 - a1 < r) (d2 : b2 - a1 < r) (d3 : b3 - a1 < r) (hN : a1 + n < N) :
    ((∑ z ∈ range N, qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z : ℝ) : ℂ) =
      ((qRacahTerm r a1 a2 a3 a4 b1 b2 b3 a1 : ℝ) : ℂ) *
        ∑ k ∈ range (n + 1), phi43Term r (a1 + 2) (b1 - a1) (b2 - a1) (b3 - a1) (a1 + 1 - a2)
          (a1 + 1 - a3) (a1 + 1 - a4) k := by
  have hz : ∀ z ∈ range N, z ∉ (range (n + 1)).image (fun k => a1 + k) →
      qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z = 0 := by
    intro z hz hnot
    simp only [mem_image, mem_range, not_exists, not_and] at hnot
    unfold qRacahTerm
    rcases lt_or_ge z a1 with hlt | hge
    · have : invQFact r ((z : ℤ) - a1) = 0 := by unfold invQFact; rw [if_neg (by omega)]
      rw [this]; ring
    · have hgt : a1 + n < z := by
        by_contra hle
        exact hnot (z - a1) (by omega) (by omega)
      have : invQFact r ((b1 : ℤ) - z) = 0 ∨ invQFact r ((b2 : ℤ) - z) = 0 ∨
          invQFact r ((b3 : ℤ) - z) = 0 := by
        rcases hmin with h | h | h
        · left; unfold invQFact; rw [if_neg (by omega)]
        · right; left; unfold invQFact; rw [if_neg (by omega)]
        · right; right; unfold invQFact; rw [if_neg (by omega)]
      rcases this with h | h | h <;> rw [h] <;> ring
  rw [← sum_subset (s₁ := (range (n + 1)).image (fun k => a1 + k)) (s₂ := range N)
    (by intro z hz; simp only [mem_image, mem_range] at hz ⊢; omega) hz]
  rw [sum_image (by intro x _ y _ h; simpa using h)]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  exact racahTerm_eq_phi43 hr hbal h2 h3 h4 g1 g2 g3 hn c2 c3 c4 d1 d2 d3 k (by omega)

end Lightlike.TV.Refl
