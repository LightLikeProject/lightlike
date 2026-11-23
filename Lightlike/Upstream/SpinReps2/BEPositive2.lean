module

public import Lightlike.Upstream.SpinReps2.BEPositive

/-!
# Biedenharn–Elliott for positive structural spins, part 2

The three-move side of the pentagon is `C · σ · beLHS`, and combining it with the two-move side
(`be_rhs_side`) and the pentagon identity gives `beLHS = beRHS` when the six spins
`a, b, c, e, p, r` are positive.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace PhyslibAlpha.Sl2.Pentagon

/-- Product of three factors is zero if the product of the 6j parts is. -/
lemma zero_aux (x y z u v w : ℝ) (h : u * v * w = 0) : x * u * (y * v * (z * w * 1)) = 0 := by
  rw [show x * u * (y * v * (z * w * 1)) = x * y * z * (u * v * w) by ring, h, mul_zero]

/-- Signs and square roots of one term. -/
lemma term_aux (sA sB sC sL1 sL2 sS j1 j2 j3 X P F D R xr : ℝ)
    (hsign : sA * sB * sC = sL1 * sL2 * sS) (hX : X = xr + 1) (hX0 : 0 ≤ X) (hF0 : 0 ≤ F)
    (hR0 : 0 ≤ R) :
    sA * Real.sqrt (X * P) * j1 * (sB * Real.sqrt (F * D) * j2 *
        (sC * Real.sqrt (R * X) * j3 * 1)) =
      Real.sqrt (R * D) * Real.sqrt (F * P) * (sL1 * sL2) * (sS * (xr + 1) * (j1 * j2 * j3)) := by
  have hXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  simp only [Real.sqrt_mul hX0, Real.sqrt_mul hF0, Real.sqrt_mul hR0]
  linear_combination (Real.sqrt P * Real.sqrt F * Real.sqrt D * Real.sqrt R * j1 * j2 * j3 *
      Real.sqrt X * Real.sqrt X) * hsign +
    (Real.sqrt P * Real.sqrt F * Real.sqrt D * Real.sqrt R * j1 * j2 * j3 * sL1 * sL2 * sS) * hXX +
    (Real.sqrt P * Real.sqrt F * Real.sqrt D * Real.sqrt R * j1 * j2 * j3 * sL1 * sL2 * sS) * hX

set_option maxHeartbeats 1000000 in
/-- **One term of the three-move side** equals `C · σ ·` the corresponding Biedenharn–Elliott term
at `x = a + b - 2n`. -/
lemma be_term {a b c d e f p q r k₁₂ k₃₄ k₁₂₃ k₄ k₂ k₁ : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (e12 : e + a = r + 2 * k₁₂) (e34 : b + c = p + 2 * k₃₄)
    (e123 : r + b = f + 2 * k₁₂₃) (e4 : f + c = q + 2 * k₄) (e2 : a + p = d + 2 * k₂)
    (e1 : e + d = q + 2 * k₁) (t1 : Triad e a r) (t2 : Triad b c p) (t3 : Triad r b f)
    (t4 : Triad f c q) (t5 : Triad a p d) (t6 : Triad e d q) {n : ℕ} (hna : n ≤ a) (hnb : n ≤ b) :
    rc a b c (k₃₄ + k₂) 0 n k₃₄ *
      ∑ k₁' : Fin (min e (a + b - 2 * n) + 1),
        rc e (a + b - 2 * n) c (k₃₄ + k₂ - n + k₁) 0 k₁' (k₃₄ + k₂ - n) *
          (rc e a b (n + k₁') 0 k₁₂ n *
            (if k₁₂₃ = n + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - n + k₁ - k₁' then 1 else 0)) =
      (Real.sqrt (((r + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) *
        Real.sqrt (((f + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))) *
      ((-1) ^ ((e + a + p + q) / 2) * (-1) ^ ((r + b + c + q) / 2)) *
      ((-1) ^ ((a + b + c + d + e + f + p + q + r + (a + b - 2 * n)) / 2) *
        (((a + b - 2 * n : ℕ) : ℝ) + 1) *
        (sixJSym a b (a + b - 2 * n) c d p * sixJSym c d (a + b - 2 * n) e f q *
          sixJSym e f (a + b - 2 * n) b a r)) := by
  -- only the triangle inequalities: the parities already follow from the label relations
  obtain ⟨-, t1a, t1b, t1c⟩ := t1
  obtain ⟨-, t2a, t2b, t2c⟩ := t2
  obtain ⟨-, t3a, t3b, t3c⟩ := t3
  obtain ⟨-, t4a, t4b, t4c⟩ := t4
  obtain ⟨-, t5a, t5b, t5c⟩ := t5
  obtain ⟨-, t6a, t6b, t6c⟩ := t6
  rw [rc_eq_coef_mul ha hc (Nat.zero_le _)]
  simp only [show a + b + c - 2 * (k₃₄ + k₂) = d by omega, show b + c - 2 * k₃₄ = p by omega]
  rw [mul_sum]
  by_cases hH : sixJSym a b (a + b - 2 * n) c d p * sixJSym c d (a + b - 2 * n) e f q *
      sixJSym e f (a + b - 2 * n) b a r = 0
  · rw [hH, mul_zero, mul_zero]
    refine sum_eq_zero fun m _ => ?_
    obtain ⟨hme, hmx⟩ := Nat.le_min.mp (Nat.lt_succ_iff.mp m.isLt)
    rw [rc_eq_coef_mul he hc (Nat.zero_le _), rc_eq_coef_mul he hb (Nat.zero_le _)]
    generalize (m : ℕ) = mv at hme hmx ⊢
    by_cases hK3 : n ≤ k₃₄ + k₂
    · by_cases hi : k₁₂₃ = n + mv - k₁₂ ∧ k₄ = k₃₄ + k₂ - n + k₁ - mv
      · by_cases hk : k₁₂ ≤ n + mv
        · rw [ite_eq_left hi]
          simp only [show e + (a + b - 2 * n) - 2 * mv = f by omega,
            show e + (a + b - 2 * n) + c - 2 * (k₃₄ + k₂ - n + k₁) = q by omega,
            show a + b - 2 * n + c - 2 * (k₃₄ + k₂ - n) = d by omega,
            show e + a - 2 * k₁₂ = r by omega, show e + a + b - 2 * (n + mv) = f by omega]
          rw [← sixJSym_P2 c d (a + b - 2 * n) e f q, ← sixJSym_P3 e f (a + b - 2 * n) b a r]
          exact zero_aux _ _ _ _ _ _ hH
        · rw [ite_eq_right (fun h : (_ ∧ _ ∧ ValidA e a b (n + mv) k₁₂ ∧ _) => hk h.2.2.1.1)]
          ring
      · rw [ite_eq_right hi]
        ring
    · rw [ite_eq_right (fun h : (_ ∧ _ ∧ ValidA a b c (k₃₄ + k₂) n ∧ _) => hK3 h.2.2.1.1)]
      ring
  · obtain ⟨h12, h3⟩ := mul_ne_zero_iff.mp hH
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
    obtain ⟨-, -, -, ⟨-, x1, x2, x3⟩⟩ := triad_of_sixJSym_ne_zero h1
    obtain ⟨-, -, -, ⟨-, y1, y2, y3⟩⟩ := triad_of_sixJSym_ne_zero h2
    clear h1 h2 h3 h12 hH
    rw [sum_eq_single ⟨k₁₂ + k₁₂₃ - n, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩]
    · rw [rc_eq_coef_mul he hc (Nat.zero_le _), rc_eq_coef_mul he hb (Nat.zero_le _)]
      rw [ite_eq_left, ite_eq_left, ite_eq_left, ite_eq_left]
      · rw [show e + (a + b - 2 * n) - 2 * (k₁₂ + k₁₂₃ - n) = f by omega,
          show e + (a + b - 2 * n) + c - 2 * (k₃₄ + k₂ - n + k₁) = q by omega,
          show a + b - 2 * n + c - 2 * (k₃₄ + k₂ - n) = d by omega,
          show e + a - 2 * k₁₂ = r by omega,
          show e + a + b - 2 * (n + (k₁₂ + k₁₂₃ - n)) = f by omega,
          ← sixJSym_P2 c d (a + b - 2 * n) e f q, ← sixJSym_P3 e f (a + b - 2 * n) b a r]
        refine term_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ (Nat.cast_succ _) (Nat.cast_nonneg _)
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        rw [show a + b + c - (k₃₄ + k₂) = (a + b + c + d) / 2 by omega,
          show e + (a + b - 2 * n) + c - (k₃₄ + k₂ - n + k₁) = (e + (a + b - 2 * n) + c + q) / 2 by
            omega,
          show e + a + b - (n + (k₁₂ + k₁₂₃ - n)) = (e + a + b + f) / 2 by omega,
          ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        apply neg_one_pow_eq_of_mod
        have hx : a + b = (a + b - 2 * n) + 2 * n := by omega
        generalize a + b - 2 * n = x at hx ⊢
        omega
      all_goals (try simp only []); first | cond_tac | omega
    · intro m _ hne
      have hne' : (m : ℕ) ≠ k₁₂ + k₁₂₃ - n := fun h => hne (Fin.ext h)
      rw [rc_eq_coef_mul he hb (Nat.zero_le _)]
      generalize (m : ℕ) = mv at hne' ⊢
      by_cases hi : k₁₂₃ = n + mv - k₁₂ ∧ k₄ = k₃₄ + k₂ - n + k₁ - mv
      · by_cases hk : k₁₂ ≤ n + mv
        · exact absurd (by omega) hne'
        · rw [ite_eq_right (fun h : (_ ∧ _ ∧ ValidA e a b (n + mv) k₁₂ ∧ _) => hk h.2.2.1.1)]
          ring
      · rw [ite_eq_right hi]
        ring
    · intro h
      exact absurd (mem_univ _) h

/-- **The three-move side** of the pentagon, in Biedenharn–Elliott's letters: `C · σ · beLHS`. -/
lemma be_lhs_side {a b c d e f p q r k₁₂ k₃₄ k₁₂₃ k₄ k₂ k₁ : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (he : 0 < e) (e12 : e + a = r + 2 * k₁₂) (e34 : b + c = p + 2 * k₃₄)
    (e123 : r + b = f + 2 * k₁₂₃) (e4 : f + c = q + 2 * k₄) (e2 : a + p = d + 2 * k₂)
    (e1 : e + d = q + 2 * k₁) (t1 : Triad e a r) (t2 : Triad b c p) (t3 : Triad r b f)
    (t4 : Triad f c q) (t5 : Triad a p d) (t6 : Triad e d q) :
    ∑ k₂₃ : Fin (min a b + 1), rc a b c (k₃₄ + k₂) 0 k₂₃ k₃₄ *
      ∑ k₁' : Fin (min e (a + b - 2 * (k₂₃ : ℕ)) + 1),
        rc e (a + b - 2 * (k₂₃ : ℕ)) c (k₃₄ + k₂ - k₂₃ + k₁) 0 k₁' (k₃₄ + k₂ - k₂₃) *
          (rc e a b (k₂₃ + k₁') 0 k₁₂ k₂₃ *
            (if k₁₂₃ = k₂₃ + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - k₂₃ + k₁ - k₁' then 1 else 0)) =
      (Real.sqrt (((r + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) *
        Real.sqrt (((f + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))) *
      ((-1) ^ ((e + a + p + q) / 2) * (-1) ^ ((r + b + c + q) / 2)) *
      beLHS a b c d e f p q r := by
  rw [beLHS, sum_range_eq_sum_fin a b, mul_sum]
  · refine sum_congr rfl fun k₂₃ _ => ?_
    obtain ⟨h1, h2⟩ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂₃.isLt)
    exact be_term ha hb hc he e12 e34 e123 e4 e2 e1 t1 t2 t3 t4 t5 t6 h1 h2
  · intro x hx
    have h0 : sixJSym a b x c d p = 0 := by
      by_contra h
      exact hx (triad_of_sixJSym_ne_zero h).1
    rw [h0]
    ring

/-- **The Biedenharn–Elliott identity, for positive `a, b, c, e, p, r`** (the six spins that play
`j₂, j₃, j₄, j₁, J₃₄, J₁₂` in the pentagon, where the recoupling theory needs positivity). -/
theorem biedenharnElliott_pos {a b c d e f p q r : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hp : 0 < p) (hr : 0 < r) :
    beLHS a b c d e f p q r = beRHS a b c d e f p q r := by
  by_cases h6 : Triad e a r ∧ Triad b c p ∧ Triad r b f ∧ Triad f c q ∧ Triad a p d ∧
      Triad e d q
  swap
  · exact be_of_not_six h6
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := h6
  have u1 := t1
  have u2 := t2
  have u3 := t3
  have u4 := t4
  have u5 := t5
  have u6 := t6
  obtain ⟨-, u1a, u1b, u1c⟩ := u1
  obtain ⟨-, u2a, u2b, u2c⟩ := u2
  obtain ⟨-, u3a, u3b, u3c⟩ := u3
  obtain ⟨-, u4a, u4b, u4c⟩ := u4
  obtain ⟨-, u5a, u5b, u5c⟩ := u5
  obtain ⟨-, u6a, u6b, u6c⟩ := u6
  obtain ⟨k₁₂, e12⟩ : ∃ k, e + a = r + 2 * k := ⟨(e + a - r) / 2, by unfold Triad at t1; omega⟩
  obtain ⟨k₃₄, e34⟩ : ∃ k, b + c = p + 2 * k := ⟨(b + c - p) / 2, by unfold Triad at t2; omega⟩
  obtain ⟨k₁₂₃, e123⟩ : ∃ k, r + b = f + 2 * k := ⟨(r + b - f) / 2, by unfold Triad at t3; omega⟩
  obtain ⟨k₄, e4⟩ : ∃ k, f + c = q + 2 * k := ⟨(f + c - q) / 2, by unfold Triad at t4; omega⟩
  obtain ⟨k₂, e2⟩ : ∃ k, a + p = d + 2 * k := ⟨(a + p - d) / 2, by unfold Triad at t5; omega⟩
  obtain ⟨k₁, e1⟩ : ∃ k, e + d = q + 2 * k := ⟨(e + d - q) / 2, by unfold Triad at t6; omega⟩
  have hP := pentagon_rc (a := e) (b := a) (c := b) (d := c) he ha hb hc
    ⟨k₁₂, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩
    (by show 0 < e + a - 2 * k₁₂; omega)
    ⟨k₃₄, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩
    (by show 0 < b + c - 2 * k₃₄; omega)
    ⟨k₁₂₃, by
      show k₁₂₃ < min (e + a - 2 * k₁₂) b + 1
      exact Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩
    (k₄ := k₄) (by show k₄ ≤ e + a - 2 * k₁₂ + b - 2 * k₁₂₃ ∧ k₄ ≤ c; omega)
    ⟨k₂, by
      show k₂ < min a (b + c - 2 * k₃₄) + 1
      exact Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩
    (k₁ := k₁) (by show k₁ ≤ e ∧ k₁ ≤ a + (b + c - 2 * k₃₄) - 2 * k₂; omega)
    (L := 0) (Nat.zero_le _) (Nat.zero_le _)
  simp only [] at hP
  simp only [show e + a - 2 * k₁₂ = r by omega, show b + c - 2 * k₃₄ = p by omega] at hP
  rw [be_rhs_side hc he hp hr e12 e34 e123 e4 e2 e1 t1 t2 t3 t4 t5 t6,
    be_lhs_side ha hb hc he e12 e34 e123 e4 e2 e1 t1 t2 t3 t4 t5 t6] at hP
  have hC : (Real.sqrt (((r + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) *
        Real.sqrt (((f + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))) *
      ((-1 : ℝ) ^ ((e + a + p + q) / 2) * (-1) ^ ((r + b + c + q) / 2)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne'
      (Real.sqrt_pos.mpr (by positivity)).ne')
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
  exact (mul_left_cancel₀ hC hP).symm

end PhyslibAlpha.Sl2.Pentagon
