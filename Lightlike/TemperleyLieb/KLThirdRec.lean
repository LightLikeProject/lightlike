import Mathlib
import Lightlike.TemperleyLieb.KLThirdBlock
import Lightlike.TemperleyLieb.KLTelescoping

/-!
# The recursion of the Kauffman–Lins coefficient in the third block

`klCoef_third_rec` expresses `klCoef` with a third block of `c + 1` strands through the coefficients with `c` strands
and with one strand. After the sums over the inner channels collapse to at most two terms, the statement compares
three tetrahedral nets; written with the zero-extended summands of `KLTelescoping` they satisfy the telescoped
contiguous relations `tel_lower_sum` and `tel_upper_sum`, and the coefficients of the three nets are proportional to
the coefficients of those relations. At the boundary of the recursion one of the three nets is absent, and its
zero-extended sum vanishes.
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- The q-number `qz q n` does not vanish for `1 ≤ n ≤ M` when `q^{2x} ≠ 1` for `1 ≤ x ≤ M`. -/
lemma qz_ne_of_pow (q : kˣ) {M : ℕ} (hq2 : ∀ x, 1 ≤ x → x ≤ M → (q : k) ^ (2 * x) ≠ 1) :
    ∀ n : ℤ, 1 ≤ n → n ≤ M → qz q n ≠ 0 := by
  intro n h1 h2
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  rw [← qb_eq_qz]
  exact qb_ne q hD m (hq2 m (by omega) (by omega))

/-- **A tetrahedral net as a zero-extended sum** over any `range N` past its range. -/
lemma tetKL_eq_hat (q : kˣ) {a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ N : ℕ}
    (h1 : (a + b + i) / 2 = F₁) (h2 : (i + c + D) / 2 = F₂) (h3 : (b + c + j) / 2 = F₃) (h4 : (a + j + D) / 2 = F₄)
    (g1 : (b + D + i + j) / 2 = B₁) (g2 : (a + c + i + j) / 2 = B₂) (g3 : (a + b + c + D) / 2 = B₃)
    (hN : B₁ < N) :
    tetKL q a b c D i j =
      tetPre q a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ * ∑ z ∈ range N, tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  unfold tetKL
  simp only [h1, h2, h3, h4, g1, g2, g3]
  have hN' : min B₁ (min B₂ B₃) < N := lt_of_le_of_lt (min_le_left _ _) hN
  rw [sum_tetTerm_eq_sum_tetHat q hN']

/-- **An admissible coefficient as a zero-extended tetrahedral sum**, with the factor
`δ(i)/θ(a,b,i)` of the first two blocks separated. -/
lemma klCoef_eq_hat (q : kˣ) {a b c e d f d' i D j F₁ F₂ F₃ F₄ B₁ B₂ B₃ N : ℕ} (h : KLAdm a b c e d f d')
    (hi : a + b - 2 * e = i) (hD : i + c - 2 * d = D) (hj : b + c - 2 * f = j)
    (h1 : (a + b + i) / 2 = F₁) (h2 : (i + c + D) / 2 = F₂) (h3 : (b + c + j) / 2 = F₃) (h4 : (a + j + D) / 2 = F₄)
    (g1 : (b + D + i + j) / 2 = B₁) (g2 : (a + c + i + j) / 2 = B₂) (g3 : (a + b + c + D) / 2 = B₃)
    (hN : B₁ < N) :
    klCoef q a b c e d f d' = deltaKL q i / thetaKL q a b i *
      (tetPre q a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ / thetaKL q i c D) *
        ∑ z ∈ range N, tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  unfold klCoef
  rw [ite_eq_left_iff.mpr (fun hn => absurd h hn), hi, hD, hj, tetKL_eq_hat q h1 h2 h3 h4 g1 g2 g3 hN]
  ring

/-- One step of the q-factorial, with the argument named: `[Y]! = [X]! [Y]` when `X + 1 = Y`. -/
lemma qfac_of_succ (q : kˣ) {X Y : ℕ} (h : X + 1 = Y) : qfac q Y = qfac q X * qb q Y := by
  subst h; rfl

/-- **The coefficient of a tetrahedral net over the theta net of its second channel.** With `s` the face sum of the
triangle `(i, c, D)`, three of the twelve factorials of `tetPre` cancel against the theta net. -/
lemma tetPre_div_theta (q : kˣ) {a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ K : ℕ}
    {x₁₁ x₁₂ x₁₃ x₁₄ x₂₁ x₂₂ x₂₃ x₂₄ x₃₁ x₃₂ x₃₃ x₃₄ : ℕ}
    (h2 : (i + c + D) / 2 = F₂)
    (k11 : B₁ - F₁ = x₁₁) (k12 : B₁ - F₂ = x₁₂) (k13 : B₁ - F₃ = x₁₃) (k14 : B₁ - F₄ = x₁₄)
    (k21 : B₂ - F₁ = x₂₁) (k22 : B₂ - F₂ = x₂₂) (k23 : B₂ - F₃ = x₂₃) (k24 : B₂ - F₄ = x₂₄)
    (k31 : B₃ - F₁ = x₃₁) (k32 : B₃ - F₂ = x₃₂) (k33 : B₃ - F₃ = x₃₃) (k34 : B₃ - F₄ = x₃₄)
    (hu : F₂ - D = x₂₄) (hv : F₂ - i = x₃₁) (hw : F₂ - c = x₁₃)
    (hnz : ∀ n, n ≤ K → qfac q n ≠ 0)
    (hK : a ≤ K ∧ b ≤ K ∧ c ≤ K ∧ D ≤ K ∧ i ≤ K ∧ j ≤ K ∧ F₂ + 1 ≤ K) :
    tetPre q a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ / thetaKL q i c D =
      qfac q x₁₁ * qfac q x₁₂ * qfac q x₁₄ * qfac q x₂₁ * qfac q x₂₂ * qfac q x₂₃ * qfac q x₃₂ * qfac q x₃₃ *
          qfac q x₃₄ /
        ((-1) ^ F₂ * qfac q a * qfac q b * qfac q j * qfac q (F₂ + 1)) := by
  obtain ⟨ka, kb, kc, kD, ki, kj, kF⟩ := hK
  unfold tetPre
  rw [thetaKL_eval q h2 hu hv hw, k11, k12, k13, k14, k21, k22, k23, k24, k31, k32, k33, k34]
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz c (by omega)
  have n4 := hnz D (by omega)
  have n5 := hnz i (by omega)
  have n6 := hnz j (by omega)
  have n7 := hnz (F₂ + 1) (by omega)
  have n8 := hnz x₂₄ (by omega)
  have n9 := hnz x₃₁ (by omega)
  have n10 := hnz x₁₃ (by omega)
  have n11 : ((-1 : k)) ^ F₂ ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- A zero-extended tetrahedral sum vanishes when at every index some face sum exceeds it or some opposite-edge sum
falls below it. -/
lemma sum_tetHat_eq_zero (q : kˣ) {F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℤ} (N : ℕ)
    (h : ∀ z : ℕ, (z : ℤ) < F₁ ∨ (z : ℤ) < F₂ ∨ (z : ℤ) < F₃ ∨ (z : ℤ) < F₄ ∨ B₁ < z ∨ B₂ < z ∨ B₃ < z) :
    ∑ z ∈ range N, tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z = 0 :=
  sum_eq_zero fun z _ => tetHat_eq_zero q (h z)

/-- **Combining proportional coefficients**: if the coefficients `C_x` of three sums are proportional to the
coefficients `λ_x` of a vanishing combination wherever the sum `S_x` does not vanish (with a reference `p`,
`λ_p ≠ 0`), the combination with the coefficients `C_x` vanishes too. -/
lemma comb_of_prop {Cc C₀ C₁ Sc S₀ S₁ lc l₀ l₁ Cp lp : k} (hlp : lp ≠ 0)
    (htel : lc * Sc - l₀ * S₀ - l₁ * S₁ = 0)
    (hc : lp * Cc * Sc = Cp * lc * Sc) (h0 : lp * C₀ * S₀ = Cp * l₀ * S₀) (h1 : lp * C₁ * S₁ = Cp * l₁ * S₁) :
    Cc * Sc - C₀ * S₀ - C₁ * S₁ = 0 := by
  have : lp * (Cc * Sc - C₀ * S₀ - C₁ * S₁) = 0 := by linear_combination hc - h0 - h1 + Cp * htel
  exact (mul_eq_zero.mp this).resolve_left hlp

set_option maxHeartbeats 1000000 in
/-- **The coefficient relation for `g₀ = 1`**: the raised third block against the term `h = 1`, `C_x λ_p = C_p λ_x`. -/
theorem kl_rel_lower_c1 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hnz : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0)
    (hqb : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0) (hi : e₀ + d₀ + 1 = m + i) (hia : i ≤ a)
    (hv : ValidA a b c 1 e₀ d₀ 1) (hc : KLAdm a b (c + 1) e₀ (d₀ + 1) m i) (hcY : KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1)) (h1A : KLAdm b c 1 (m - 1) 1 0 m) (h1T : KLAdm a b c e₀ d₀ (m - 1) i) (hm : 1 ≤ m) :
    (qb q (d₀ + 1) / qb q (c + 1)) * (tetPre q (a) (b) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1)) * (qb q (b - e₀ + c - d₀ + 1 - m) * qb q (b + 1 - m)) =
      (qb q m / qb q (c + 1)) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m) (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (d₀ + 1) * qb q (b + c + 2 - 2 * m)) := by
  simp only [KLAdm, ValidA, le_min_iff] at hv hc hcY h1A h1T
  have Px := tetPre_div_theta q (a := a) (b := b) (c := c + 1) (D := a + b - 2 * e₀ + c - 2 * d₀ - 1) (i := a + b - 2 * e₀) (j := b + c + 1 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c + 1 - m) (F₄ := a + b + c - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ - m) (B₂ := a + b + c - e₀ + 1 - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀ - 1) (x₁₄ := b - e₀) (x₂₁ := c + 1 - m) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀ + 1) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Pp := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c + 2 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c + 1 - m) (F₄ := a + b + c + 1 - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ + 1 - m) (B₂ := a + b + c - e₀ + 1 - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ + 1 - m) (x₁₂ := b + 1 - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c + 1 - m) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [Px, Pp]
  rw [qfac_of_succ q (show b - e₀ + c - d₀ - m + 1 = b - e₀ + c - d₀ + 1 - m by omega)]
  rw [qfac_of_succ q (show b - m + 1 = b + 1 - m by omega)]
  rw [qfac_of_succ q (show m - 1 + 1 = m by omega)]
  rw [qfac_of_succ q (show b + c + 1 - 2 * m + 1 = b + c + 2 - 2 * m by omega)]
  have hs : ((-1 : k)) ^ (a + b - 2 * e₀ + c - d₀) ≠ 0 := pow_ne_zero _ (by norm_num)
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz (a + b - 2 * e₀ + c - d₀ + 1) (by omega)
  have j0 := hnz (b + c - 2 * m) (by omega)
  have j1 := hnz (b + c + 1 - 2 * m) (by omega)
  have j2 := hnz (b + c + 2 - 2 * m) (by omega)
  have q0 : qb q (c + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q1 : qb q (b - e₀ + c - d₀ + 1 - m) ≠ 0 := hqb _ (by omega) (by omega)
  have q2 : qb q (b + 1 - m) ≠ 0 := hqb _ (by omega) (by omega)
  have q3 : qb q (m) ≠ 0 := hqb _ (by omega) (by omega)
  have q4 : qb q (b + c + 2 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  field_simp

set_option maxHeartbeats 500000 in
/-- **The coefficient relation for `g₀ = 1`**: the term `h = 0` against the term `h = 1`, `C_x λ_p = C_p λ_x`. -/
theorem kl_rel_lower_01 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hnz : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0)
    (hqb : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0) (hi : e₀ + d₀ + 1 = m + i) (hia : i ≤ a)
    (hv : ValidA a b c 1 e₀ d₀ 1) (h0A : KLAdm b c 1 m 0 0 m) (h0T : KLAdm a b c e₀ d₀ m (i - 1)) (hi1 : 1 ≤ i) (h1A : KLAdm b c 1 (m - 1) 1 0 m) (h1T : KLAdm a b c e₀ d₀ (m - 1) i) (hm : 1 ≤ m) :
    (qb q (b + c - m + 2) * qb q (c - m + 1) / (qb q (c + 1) * qb q (b + c - 2 * m + 2)) * (qb q i / qb q (b + c - 2 * m + 1))) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (b - e₀ + c - d₀ + 1 - m) * qb q (b + 1 - m)) =
      (qb q m / qb q (c + 1)) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m) (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (b + c - m + 2) * qb q (a - i + 1)) := by
  simp only [KLAdm, ValidA, le_min_iff] at hv h0A h0T h1A h1T
  have Px := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c - m) (F₄ := a + b + c - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ - m) (B₂ := a + b + c - e₀ - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c - m) (x₂₂ := i - 1) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i + 1) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Pp := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c + 2 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c + 1 - m) (F₄ := a + b + c + 1 - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ + 1 - m) (B₂ := a + b + c - e₀ + 1 - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ + 1 - m) (x₁₂ := b + 1 - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c - m + 1) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [Px, Pp]
  rw [show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega]
  rw [show b + c - 2 * m + 2 = b + c + 2 - 2 * m by omega]
  rw [qfac_of_succ q (show b - e₀ + c - d₀ - m + 1 = b - e₀ + c - d₀ + 1 - m by omega)]
  rw [qfac_of_succ q (show b - m + 1 = b + 1 - m by omega)]
  rw [qfac_of_succ q (show c - m + 1 = c - m + 1 by omega)]
  rw [qfac_of_succ q (show i - 1 + 1 = i by omega)]
  rw [qfac_of_succ q (show a - i + 1 = a - i + 1 by omega)]
  rw [qfac_of_succ q (show m - 1 + 1 = m by omega)]
  rw [qfac_of_succ q (show b + c + 1 - 2 * m + 1 = b + c + 2 - 2 * m by omega)]
  rw [qfac_of_succ q (show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega)]
  have hs : ((-1 : k)) ^ (a + b - 2 * e₀ + c - d₀) ≠ 0 := pow_ne_zero _ (by norm_num)
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz (a + b - 2 * e₀ + c - d₀ + 1) (by omega)
  have j0 := hnz (b + c - 2 * m) (by omega)
  have j1 := hnz (b + c + 1 - 2 * m) (by omega)
  have j2 := hnz (b + c + 2 - 2 * m) (by omega)
  have q0 : qb q (c + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q1 : qb q (b - e₀ + c - d₀ + 1 - m) ≠ 0 := hqb _ (by omega) (by omega)
  have q2 : qb q (b + 1 - m) ≠ 0 := hqb _ (by omega) (by omega)
  have q3 : qb q (c - m + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q4 : qb q (i) ≠ 0 := hqb _ (by omega) (by omega)
  have q5 : qb q (a - i + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q6 : qb q (m) ≠ 0 := hqb _ (by omega) (by omega)
  have q7 : qb q (b + c + 2 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  have q8 : qb q (b + c + 1 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  ring

set_option maxHeartbeats 1500000 in
/-- **The coefficient relation for `g₀ = 1`**: the raised third block against the term `h = 0`, `C_x λ_p = C_p λ_x`. -/
theorem kl_rel_lower_c0 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hnz : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0)
    (hqb : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0) (hi : e₀ + d₀ + 1 = m + i) (hia : i ≤ a)
    (hv : ValidA a b c 1 e₀ d₀ 1) (hc : KLAdm a b (c + 1) e₀ (d₀ + 1) m i) (hcY : KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1)) (h0A : KLAdm b c 1 m 0 0 m) (h0T : KLAdm a b c e₀ d₀ m (i - 1)) (hi1 : 1 ≤ i) :
    (qb q (d₀ + 1) / qb q (c + 1)) * (tetPre q (a) (b) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1)) * (qb q (b + c - m + 2) * qb q (a - i + 1)) =
      (qb q (b + c - m + 2) * qb q (c - m + 1) / (qb q (c + 1) * qb q (b + c - 2 * m + 2)) * (qb q i / qb q (b + c - 2 * m + 1))) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (d₀ + 1) * qb q (b + c + 2 - 2 * m)) := by
  simp only [KLAdm, ValidA, le_min_iff] at hv hc hcY h0A h0T
  have Px := tetPre_div_theta q (a := a) (b := b) (c := c + 1) (D := a + b - 2 * e₀ + c - 2 * d₀ - 1) (i := a + b - 2 * e₀) (j := b + c + 1 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c + 1 - m) (F₄ := a + b + c - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ - m) (B₂ := a + b + c - e₀ + 1 - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀ - 1) (x₁₄ := b - e₀) (x₂₁ := c - m + 1) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀ + 1) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Pp := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c - m) (F₄ := a + b + c - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ - m) (B₂ := a + b + c - e₀ - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c - m) (x₂₂ := i - 1) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i + 1) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [Px, Pp]
  rw [show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega]
  rw [show b + c - 2 * m + 2 = b + c + 2 - 2 * m by omega]
  rw [qfac_of_succ q (show c - m + 1 = c - m + 1 by omega)]
  rw [qfac_of_succ q (show i - 1 + 1 = i by omega)]
  rw [qfac_of_succ q (show a - i + 1 = a - i + 1 by omega)]
  rw [qfac_of_succ q (show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega)]
  have hs : ((-1 : k)) ^ (a + b - 2 * e₀ + c - d₀) ≠ 0 := pow_ne_zero _ (by norm_num)
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz (a + b - 2 * e₀ + c - d₀ + 1) (by omega)
  have j0 := hnz (b + c - 2 * m) (by omega)
  have j1 := hnz (b + c + 1 - 2 * m) (by omega)
  have j2 := hnz (b + c + 2 - 2 * m) (by omega)
  have q0 : qb q (c + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q1 : qb q (c - m + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q2 : qb q (i) ≠ 0 := hqb _ (by omega) (by omega)
  have q3 : qb q (a - i + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q4 : qb q (b + c + 1 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  have q5 : qb q (b + c + 2 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  field_simp

set_option maxHeartbeats 4300000 in
/-- **The coefficient relation for `g₀ = 0`**: the term `h = 0` against the raised third block, `C_x λ_p = C_p λ_x`. -/
theorem kl_rel_upper_0c (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hnz : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0)
    (hqb : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0) (hi : e₀ + d₀ = m + i) (hia : i ≤ a)
    (hv : ValidA a b c 1 e₀ d₀ 0) (h0A : KLAdm b c 1 m 0 0 m) (h0T : KLAdm a b c e₀ d₀ m i) (hc : KLAdm a b (c + 1) e₀ d₀ m i) (hcY : KLAdm (a + b - 2 * e₀) c 1 d₀ 0 0 d₀) :
    (qb q (b + c - m + 2) * qb q (c - m + 1) / (qb q (c + 1) * qb q (b + c + 2 - 2 * m)) * (qb q (a + b + c - 2 * m - i + 2) * qb q (b + c - 2 * m - i + 1) / (qb q (b + c + 1 - 2 * m) * qb q (a + b + c - 2 * m - 2 * i + 2)))) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (c - d₀ + 1) * qb q (b + c + 2 - 2 * m)) =
      (qb q (a + b - 2 * e₀ + c - d₀ + 2) * qb q (c - d₀ + 1) / (qb q (c + 1) * qb q (a + b - 2 * e₀ + c - 2 * d₀ + 2))) * (tetPre q (a) (b) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀ + 1) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c + 1 - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1)) * (-(qb q (b + c - m + 2) * qb q (a + b + c - 2 * m - i + 2))) := by
  simp only [KLAdm, ValidA, le_min_iff] at hv h0A h0T hc hcY
  have Px := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c - m) (F₄ := a + b + c - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c - d₀ - m) (B₂ := a + b + c - e₀ - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c - m) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Pp := tetPre_div_theta q (a := a) (b := b) (c := c + 1) (D := a + b - 2 * e₀ + c - 2 * d₀ + 1) (i := a + b - 2 * e₀) (j := b + c + 1 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀ + 1) (F₃ := b + c + 1 - m) (F₄ := a + b + c + 1 - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (B₂ := a + b + c + 1 - e₀ - m) (B₃ := a + b + c + 1 - e₀ - d₀) (x₁₁ := b - e₀ + c - d₀ - m + 1) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c - m + 1) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c + 1 - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [Px, Pp]
  rw [pow_succ (-1 : k) (a + b - 2 * e₀ + c - d₀)]
  rw [show a + b + c - 2 * m - 2 * i + 2 = a + b - 2 * e₀ + c - 2 * d₀ + 2 by omega]
  rw [show b + c - 2 * m - i + 1 = b - e₀ + c - d₀ - m + 1 by omega]
  rw [show a + b - 2 * e₀ + c - d₀ + 1 + 1 = a + b - 2 * e₀ + c - d₀ + 2 by omega]
  rw [qfac_of_succ q (show b - e₀ + c - d₀ - m + 1 = b - e₀ + c - d₀ - m + 1 by omega)]
  rw [qfac_of_succ q (show c - m + 1 = c - m + 1 by omega)]
  rw [qfac_of_succ q (show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega)]
  rw [qfac_of_succ q (show a + b - 2 * e₀ + c - d₀ + 1 + 1 = a + b - 2 * e₀ + c - d₀ + 2 by omega)]
  have hs : ((-1 : k)) ^ (a + b - 2 * e₀ + c - d₀) ≠ 0 := pow_ne_zero _ (by norm_num)
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz (a + b - 2 * e₀ + c - d₀ + 1) (by omega)
  have j0 := hnz (b + c - 2 * m) (by omega)
  have j1 := hnz (b + c + 1 - 2 * m) (by omega)
  have q0 : qb q (c + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q1 : qb q (a + b - 2 * e₀ + c - 2 * d₀ + 2) ≠ 0 := hqb _ (by omega) (by omega)
  have q2 : qb q (b + c + 2 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  have q3 : qb q (b - e₀ + c - d₀ - m + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q4 : qb q (c - m + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q5 : qb q (b + c + 1 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  have q6 : qb q (a + b - 2 * e₀ + c - d₀ + 2) ≠ 0 := hqb _ (by omega) (by omega)
  field_simp

set_option maxHeartbeats 1500000 in
/-- **The coefficient relation for `g₀ = 0`**: the term `h = 1` against the raised third block, `C_x λ_p = C_p λ_x`. -/
theorem kl_rel_upper_1c (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hnz : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0)
    (hqb : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0) (hi : e₀ + d₀ = m + i) (_hia : i ≤ a)
    (hv : ValidA a b c 1 e₀ d₀ 0) (h1A : KLAdm b c 1 (m - 1) 1 0 m) (h1T : KLAdm a b c e₀ d₀ (m - 1) (i + 1)) (hm : 1 ≤ m) (hc : KLAdm a b (c + 1) e₀ d₀ m i) (hcY : KLAdm (a + b - 2 * e₀) c 1 d₀ 0 0 d₀) :
    (qb q m / qb q (c + 1) * -(qb q (a - i) / qb q (a + b + c + 2 - 2 * m - 2 * i))) * (tetPre q (a) (b) (c) (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c) (a + b - 2 * e₀ + c - 2 * d₀)) * (qb q (c - d₀ + 1) * qb q (b + c + 2 - 2 * m)) =
      (qb q (a + b - 2 * e₀ + c - d₀ + 2) * qb q (c - d₀ + 1) / (qb q (c + 1) * qb q (a + b - 2 * e₀ + c - 2 * d₀ + 2))) * (tetPre q (a) (b) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀ + 1) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c + 1 - e₀ - d₀) / thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1)) * (qb q (b + 1 - m) * qb q (i + 1)) := by
  simp only [KLAdm, ValidA, le_min_iff] at hv h1A h1T hc hcY
  have Px := tetPre_div_theta q (a := a) (b := b) (c := c) (D := a + b - 2 * e₀ + c - 2 * d₀) (i := a + b - 2 * e₀) (j := b + c + 2 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀) (F₃ := b + c + 1 - m) (F₄ := a + b + c + 1 - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (B₂ := a + b + c + 1 - e₀ - m) (B₃ := a + b + c - e₀ - d₀) (x₁₁ := b - e₀ + c + 1 - d₀ - m) (x₁₂ := b + 1 - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c + 1 - m) (x₂₂ := i + 1) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c - d₀) (x₃₂ := e₀) (x₃₃ := a - i - 1) (x₃₄ := m - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have Pp := tetPre_div_theta q (a := a) (b := b) (c := c + 1) (D := a + b - 2 * e₀ + c - 2 * d₀ + 1) (i := a + b - 2 * e₀) (j := b + c + 1 - 2 * m) (F₁ := a + b - e₀) (F₂ := a + b - 2 * e₀ + c - d₀ + 1) (F₃ := b + c + 1 - m) (F₄ := a + b + c + 1 - m - e₀ - d₀) (B₁ := a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (B₂ := a + b + c + 1 - e₀ - m) (B₃ := a + b + c + 1 - e₀ - d₀) (x₁₁ := b - e₀ + c + 1 - d₀ - m) (x₁₂ := b - m) (x₁₃ := a + b - 2 * e₀ - d₀) (x₁₄ := b - e₀) (x₂₁ := c + 1 - m) (x₂₂ := i) (x₂₃ := a - e₀) (x₂₄ := d₀) (x₃₁ := c + 1 - d₀) (x₃₂ := e₀) (x₃₃ := a - i) (x₃₄ := m)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnz ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  rw [Px, Pp]
  rw [pow_succ (-1 : k) (a + b - 2 * e₀ + c - d₀)]
  rw [show a + b + c + 2 - 2 * m - 2 * i = a + b - 2 * e₀ + c - 2 * d₀ + 2 by omega]
  rw [show a + b - 2 * e₀ + c - d₀ + 1 + 1 = a + b - 2 * e₀ + c - d₀ + 2 by omega]
  rw [qfac_of_succ q (show b - m + 1 = b + 1 - m by omega)]
  rw [qfac_of_succ q (show i + 1 = i + 1 by omega)]
  rw [qfac_of_succ q (show a - i - 1 + 1 = a - i by omega)]
  rw [qfac_of_succ q (show m - 1 + 1 = m by omega)]
  rw [qfac_of_succ q (show b + c + 1 - 2 * m + 1 = b + c + 2 - 2 * m by omega)]
  rw [qfac_of_succ q (show a + b - 2 * e₀ + c - d₀ + 1 + 1 = a + b - 2 * e₀ + c - d₀ + 2 by omega)]
  have hs : ((-1 : k)) ^ (a + b - 2 * e₀ + c - d₀) ≠ 0 := pow_ne_zero _ (by norm_num)
  have n1 := hnz a (by omega)
  have n2 := hnz b (by omega)
  have n3 := hnz (a + b - 2 * e₀ + c - d₀ + 1) (by omega)
  have j0 := hnz (b + c - 2 * m) (by omega)
  have j1 := hnz (b + c + 1 - 2 * m) (by omega)
  have q0 : qb q (c + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q1 : qb q (a + b - 2 * e₀ + c - 2 * d₀ + 2) ≠ 0 := hqb _ (by omega) (by omega)
  have q2 : qb q (b + c + 2 - 2 * m) ≠ 0 := hqb _ (by omega) (by omega)
  have q3 : qb q (b + 1 - m) ≠ 0 := hqb _ (by omega) (by omega)
  have q4 : qb q (i + 1) ≠ 0 := hqb _ (by omega) (by omega)
  have q5 : qb q (a - i) ≠ 0 := hqb _ (by omega) (by omega)
  have q6 : qb q (m) ≠ 0 := hqb _ (by omega) (by omega)
  have q7 : qb q (a + b - 2 * e₀ + c - d₀ + 2) ≠ 0 := hqb _ (by omega) (by omega)
  field_simp

end Lightlike.TemperleyLieb
