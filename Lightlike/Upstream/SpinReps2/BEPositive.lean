module

public import Lightlike.Upstream.SpinReps2.BEPentagon3
public import Lightlike.Upstream.SpinReps2.BEDefs

/-!
# Biedenharn–Elliott for positive structural spins, part 1

Translation of `PhyslibAlpha.Sl2.Pentagon.pentagon_rc` (recoupling coefficients) into
`beLHS = beRHS` (Physlib's `sixJSym`). The pentagon spins `(j1, j2, j3, j4, J12, J34, J123, J234,
J, J23)` correspond to the Biedenharn–Elliott letters `(e, a, b, c, r, p, f, d, q, x)`.

This file: the two-move side of the pentagon is `C · σ · beRHS`.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace PhyslibAlpha.Sl2.Pentagon

/-- Prove a `ValidA`/`ValidB` admissibility condition by unfolding and `omega`. (Anonymous
constructors against these abbreviations time out in `whnf`.) -/
macro "valid_tac" : tactic =>
  `(tactic| first
    | (unfold ValidA; refine ⟨?_, ?_, ?_⟩ <;> omega)
    | (unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> omega))

/-- The full side condition of `rc_eq_coef_mul`. -/
macro "cond_tac" : tactic =>
  `(tactic| (refine ⟨Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩),
      Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩), ?_, ?_⟩ <;> valid_tac))

lemma neg_one_pow_eq_of_mod {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div n 2, pow_add, pow_add, pow_mul, pow_mul, h]
  simp

/-- `rc` as a coefficient times its 6j symbol (no `if` around the 6j). -/
lemma rc_eq_coef_mul {x y z K l k₁ k₃ : ℕ} (hx : 0 < x) (hz : 0 < z)
    (hl : l ≤ x + y + z - 2 * K) :
    rc x y z K l k₁ k₃ =
      (if k₁ < min x y + 1 ∧ k₃ < min y z + 1 ∧ ValidA x y z K k₁ ∧ ValidB x y z K k₃ then
        (-1) ^ (x + y + z - K) *
          Real.sqrt (((x + y - 2 * k₁ + 1 : ℕ) : ℝ) * ((y + z - 2 * k₃ + 1 : ℕ) : ℝ)) else 0) *
        sixJSym x y (x + y - 2 * k₁) z (x + y + z - 2 * K) (y + z - 2 * k₃) := by
  rw [rc_eq_sixJSym hx hz hl]
  split_ifs <;> ring

/-- If one of the six triads needed to build the pentagon labels fails, both sides of
Biedenharn–Elliott vanish. -/
lemma be_of_not_six {a b c d e f p q r : ℕ}
    (h : ¬(Triad e a r ∧ Triad b c p ∧ Triad r b f ∧ Triad f c q ∧ Triad a p d ∧ Triad e d q)) :
    beLHS a b c d e f p q r = beRHS a b c d e f p q r := by
  have hR : beRHS a b c d e f p q r = 0 := by
    unfold beRHS
    by_contra hne
    have hA := triad_of_sixJSym_ne_zero (left_ne_zero_of_mul hne)
    have hB := triad_of_sixJSym_ne_zero (right_ne_zero_of_mul hne)
    apply h
    unfold Triad at *
    omega
  have hL : beLHS a b c d e f p q r = 0 := by
    unfold beLHS
    refine sum_eq_zero fun x _ => ?_
    by_contra hne
    have hprod := right_ne_zero_of_mul hne
    have h1 := triad_of_sixJSym_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hprod))
    have h2 := triad_of_sixJSym_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hprod))
    have h3 := triad_of_sixJSym_ne_zero (right_ne_zero_of_mul hprod)
    apply h
    unfold Triad at *
    omega
  rw [hL, hR]

/-- **The two-move side** of the pentagon, in Biedenharn–Elliott's letters: it is
`C · σ · beRHS` with `C = √((r+1)(d+1)) √((f+1)(p+1))` and a sign `σ`. -/
lemma be_rhs_side {a b c d e f p q r k₁₂ k₃₄ k₁₂₃ k₄ k₂ k₁ : ℕ} (hc : 0 < c) (he : 0 < e)
    (hp : 0 < p) (hr : 0 < r) (e12 : e + a = r + 2 * k₁₂) (e34 : b + c = p + 2 * k₃₄)
    (e123 : r + b = f + 2 * k₁₂₃) (e4 : f + c = q + 2 * k₄) (e2 : a + p = d + 2 * k₂)
    (e1 : e + d = q + 2 * k₁) (t1 : Triad e a r) (t2 : Triad b c p) (t3 : Triad r b f)
    (t4 : Triad f c q) (t5 : Triad a p d) (t6 : Triad e d q) :
    rc e a p (k₂ + k₁) 0 k₁₂ k₂ * (rc r b c (k₂ + k₁ - k₁₂ + k₃₄) 0 k₁₂₃ k₃₄ *
        (if k₄ = k₂ + k₁ - k₁₂ + k₃₄ - k₁₂₃ then 1 else 0)) =
      (Real.sqrt (((r + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) *
        Real.sqrt (((f + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ))) *
      ((-1) ^ ((e + a + p + q) / 2) * (-1) ^ ((r + b + c + q) / 2)) *
      beRHS a b c d e f p q r := by
  unfold Triad at t1 t2 t3 t4 t5 t6
  rw [rc_eq_coef_mul he hp (Nat.zero_le _), rc_eq_coef_mul hr hc (Nat.zero_le _), beRHS]
  by_cases hpqr : q ≤ p + r ∧ p ≤ q + r ∧ r ≤ p + q
  · rw [ite_eq_left, ite_eq_left, ite_eq_left]
    · rw [show e + a + p - (k₂ + k₁) = (e + a + p + q) / 2 by omega,
        show r + b + c - (k₂ + k₁ - k₁₂ + k₃₄) = (r + b + c + q) / 2 by omega,
        show e + a - 2 * k₁₂ = r by omega,
        show a + p - 2 * k₂ = d by omega, show e + a + p - 2 * (k₂ + k₁) = q by omega,
        show r + b - 2 * k₁₂₃ = f by omega, show b + c - 2 * k₃₄ = p by omega,
        show r + b + c - 2 * (k₂ + k₁ - k₁₂ + k₃₄) = q by omega,
        ← sixJSym_R1 p q r e a d, ← sixJSym_R2 p q r f b c]
      ring
    all_goals first | cond_tac | omega
  · have h0 : sixJSym p q r e a d = 0 := by
      by_contra h
      have := (triad_of_sixJSym_ne_zero h).1
      unfold Triad at this
      exact hpqr ⟨by omega, by omega, by omega⟩
    have c1 : ¬(k₁₂ < min e a + 1 ∧ k₂ < min a p + 1 ∧ ValidA e a p (k₂ + k₁) k₁₂ ∧
        ValidB e a p (k₂ + k₁) k₂) := fun h => by
      obtain ⟨-, -, ⟨h1, h2, h3⟩, -⟩ := h
      exact hpqr ⟨by omega, by omega, by omega⟩
    rw [ite_eq_right c1, h0]
    ring

end PhyslibAlpha.Sl2.Pentagon
