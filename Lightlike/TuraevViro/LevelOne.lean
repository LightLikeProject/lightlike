import Lightlike.TuraevViro.TuraevViro

/-!
# Turaev–Viro at `r = 3`: unconditional invariance

At `q = e^{iπ/3}` the colours are `0, 1` (spins `0, ½`). Both quantum dimensions are `[1] = [2] = 1`,
and `[3] = 0`. The quantum 6j symbol is `1` on the all-zero tetrahedron, `-1` on the other seven
admissible ones, and `0` otherwise (`qSixJ_three`).

So q-Biedenharn–Elliott and q-orthogonality reduce to finite integer identities, checked by the
kernel (`decide`, no `native_decide`). This gives the **unconditional** invariance of the `r = 3`
Turaev–Viro state sum under both moves (`turaevViro3_move23`, `turaevViro3_move14`). It is also
a non-vacuity check: the hypotheses of `turaevViro_move23/14` hold for an actual Turaev–Viro
model.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

lemma qnum3_one : qnum 3 1 = 1 := qnum_one (by norm_num)

lemma qnum3_two : qnum 3 2 = 1 := by
  have := qnum_sub (r := 3) (n := 1) (by norm_num) (by norm_num)
  rw [show 3 - 1 = 2 from rfl] at this
  rw [this, qnum3_one]

lemma qnum3_three : qnum 3 3 = 0 := qnum_self (by norm_num)

lemma qfact3 (n : ℕ) : qfact 3 n = if n ≤ 2 then 1 else 0 := by
  unfold qfact
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n <;> simp [prod_range_succ, qnum3_one, qnum3_two]
  · rw [ite_eq_right (by omega)]
    exact prod_eq_zero (mem_range.mpr (by omega : 2 < n)) qnum3_three

lemma invQFact3 (u : ℤ) : invQFact 3 u = if 0 ≤ u ∧ u ≤ 2 then 1 else 0 := by
  unfold invQFact
  by_cases h0 : 0 ≤ u
  · rw [ite_eq_left h0, qfact3]
    by_cases h2 : u ≤ 2
    · rw [ite_eq_left (by omega), ite_eq_left ⟨h0, h2⟩, inv_one]
    · rw [ite_eq_right (by omega), ite_eq_right (fun h => h2 h.2), inv_zero]
  · rw [ite_eq_right h0, ite_eq_right (fun h => h0 h.1)]

lemma qAdm3_le {a b c : ℕ} (h : qAdm 3 a b c) : a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 := by
  unfold qAdm Tri at h; omega

lemma qDelta3 {a b c : ℕ} (h : qAdm 3 a b c) : qDelta 3 a b c = 1 := by
  obtain ⟨ha, hb, hc⟩ := qAdm3_le h
  unfold qDelta
  rw [qfact3, qfact3, qfact3, qfact3, ite_eq_left (by omega), ite_eq_left (by omega),
    ite_eq_left (by omega), ite_eq_left (by unfold qAdm Tri at h; omega)]
  norm_num

/-- The `r = 3` quantum 6j symbol as an integer: `1`, `-1` or `0`. -/
def t3 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℤ :=
  if qAdm 3 j₁ j₂ j₃ ∧ qAdm 3 j₁ j₅ j₆ ∧ qAdm 3 j₄ j₂ j₆ ∧ qAdm 3 j₄ j₅ j₃ then
    (if j₁ + j₂ + j₃ + j₄ + j₅ + j₆ = 0 then 1 else -1)
  else 0

/-- **The `r = 3` quantum 6j symbols.** -/
theorem qSixJ_three (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    qSixJ 3 j₁ j₂ j₃ j₄ j₅ j₆ = (t3 j₁ j₂ j₃ j₄ j₅ j₆ : ℝ) := by
  unfold qSixJ t3
  by_cases hc : qAdm 3 j₁ j₂ j₃ ∧ qAdm 3 j₁ j₅ j₆ ∧ qAdm 3 j₄ j₂ j₆ ∧ qAdm 3 j₄ j₅ j₃
  · rw [ite_eq_left hc, ite_eq_left hc, qDelta3 hc.1, qDelta3 hc.2.1, qDelta3 hc.2.2.1,
      qDelta3 hc.2.2.2, one_mul, one_mul, one_mul, one_mul]
    obtain ⟨h1, h2, h3⟩ := qAdm3_le hc.1
    obtain ⟨-, h5, h6⟩ := qAdm3_le hc.2.1
    obtain ⟨h4, -, -⟩ := qAdm3_le hc.2.2.1
    unfold qRacahSum qRacahTerm
    simp only [invQFact3, qfact3]
    interval_cases j₁ <;> interval_cases j₂ <;> interval_cases j₃ <;> interval_cases j₄ <;>
      interval_cases j₅ <;> interval_cases j₆ <;>
      first
        | (exfalso; revert hc; decide)
        | simp [sum_range_succ]
  · rw [ite_eq_right hc, ite_eq_right hc, Int.cast_zero]

lemma t3_le {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : t3 j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    j₁ ≤ 1 ∧ j₂ ≤ 1 ∧ j₃ ≤ 1 ∧ j₄ ≤ 1 ∧ j₅ ≤ 1 ∧ j₆ ≤ 1 := by
  unfold t3 at h
  by_cases hc : qAdm 3 j₁ j₂ j₃ ∧ qAdm 3 j₁ j₅ j₆ ∧ qAdm 3 j₄ j₂ j₆ ∧ qAdm 3 j₄ j₅ j₃
  · obtain ⟨h1, h2, h3⟩ := qAdm3_le hc.1
    obtain ⟨-, h5, h6⟩ := qAdm3_le hc.2.1
    obtain ⟨h4, -, -⟩ := qAdm3_le hc.2.2.1
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rw [ite_eq_right hc] at h
    exact absurd rfl h

/-- The finite Biedenharn–Elliott check over the colours `{0, 1}`. -/
lemma be3_check : ∀ a b c d e f p q r : Fin 2,
    ∑ x ∈ range 2, (-1 : ℤ) ^ ((a.val + b + c + d + e + f + p + q + r + x) / 2) *
      (t3 a b x c d p * t3 c d x e f q * t3 e f x b a r) =
    t3 p q r e a d * t3 p q r f b c := by
  decide

/-- **q-Biedenharn–Elliott at `r = 3`** (proven). -/
theorem qBiedenharnElliott_three : qBiedenharnElliott (r := 3) (by norm_num) := by
  intro a b c d e f p q r
  simp only [tvModel, show (3 : ℕ) - 1 = 2 from rfl, qSixJ_three]
  have hdim : ∀ x ∈ range 2, qnum 3 (x + 1) = 1 := by
    intro x hx
    rcases (show x = 0 ∨ x = 1 by have := mem_range.mp hx; omega) with rfl | rfl
    · exact qnum3_one
    · exact qnum3_two
  rw [sum_congr rfl fun x hx => by rw [hdim x hx, mul_one]]
  by_cases hall : a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 ∧ e ≤ 1 ∧ f ≤ 1 ∧ p ≤ 1 ∧ q ≤ 1 ∧ r ≤ 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hp, hq, hr⟩ := hall
    have := be3_check ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ ⟨e, by omega⟩
      ⟨f, by omega⟩ ⟨p, by omega⟩ ⟨q, by omega⟩ ⟨r, by omega⟩
    exact_mod_cast this
  · have hR : (t3 p q r e a d : ℝ) * t3 p q r f b c = 0 := by
      by_contra h0
      have h1 := t3_le (by exact_mod_cast left_ne_zero_of_mul h0)
      have h2 := t3_le (by exact_mod_cast right_ne_zero_of_mul h0)
      exact hall ⟨h1.2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2, h1.2.2.2.2.2, h1.2.2.2.1, h2.2.2.2.1,
        h1.1, h1.2.1, h1.2.2.1⟩
    rw [hR]
    refine sum_eq_zero fun x _ => ?_
    by_contra h0
    have hz := right_ne_zero_of_mul h0
    have h1 := t3_le (by exact_mod_cast left_ne_zero_of_mul (left_ne_zero_of_mul hz))
    have h2 := t3_le (by exact_mod_cast right_ne_zero_of_mul (left_ne_zero_of_mul hz))
    have h3 := t3_le (by exact_mod_cast right_ne_zero_of_mul hz)
    exact hall ⟨h1.1, h1.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1,
      h1.2.2.2.2.2, h2.2.2.2.2.2, h3.2.2.2.2.2⟩

/-- The finite orthogonality check over the colours `{0, 1}`. -/
lemma orth3_check : ∀ B A E F q : Fin 2,
    ∑ x ∈ range 2, (t3 B A x E F q) ^ 2 =
      if qAdm 3 A E q ∧ qAdm 3 B q F then 1 else 0 := by
  decide

/-- **q-orthogonality at `r = 3`** (proven). -/
theorem qOrthogonality_three : qOrthogonality (r := 3) (by norm_num) := by
  intro B A E F q
  simp only [tvModel, show (3 : ℕ) - 1 = 2 from rfl, qSixJ_three]
  have hdim : ∀ x ∈ range 2, qnum 3 (x + 1) = 1 := by
    intro x hx
    rcases (show x = 0 ∨ x = 1 by have := mem_range.mp hx; omega) with rfl | rfl
    · exact qnum3_one
    · exact qnum3_two
  rw [sum_congr rfl fun x hx => by rw [hdim x hx, one_mul]]
  by_cases hall : B ≤ 1 ∧ A ≤ 1 ∧ E ≤ 1 ∧ F ≤ 1 ∧ q ≤ 1
  · obtain ⟨hB, hA, hE, hF, hq⟩ := hall
    have := orth3_check ⟨B, by omega⟩ ⟨A, by omega⟩ ⟨E, by omega⟩ ⟨F, by omega⟩ ⟨q, by omega⟩
    have hq1 : qnum 3 (q + 1) = 1 := by
      rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
      · exact qnum3_one
      · exact qnum3_two
    rw [hq1, div_one]
    split_ifs at this ⊢ <;> exact_mod_cast this
  · have hR : ¬ (qAdm 3 A E q ∧ qAdm 3 B q F) := fun h => hall
      ⟨(qAdm3_le h.2).1, (qAdm3_le h.1).1, (qAdm3_le h.1).2.1, (qAdm3_le h.2).2.2,
        (qAdm3_le h.1).2.2⟩
    rw [ite_eq_right hR]
    refine sum_eq_zero fun x _ => ?_
    by_contra h0
    have h1 := t3_le (by exact_mod_cast pow_ne_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact hall ⟨h1.1, h1.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2⟩

/-- **Turaev–Viro at `r = 3` is invariant under the 2-3 move** (no hypotheses). -/
theorem turaevViro3_move23 {V : Type*} [DecidableEq V] (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move23 K h) = turaevViro (r := 3) (by norm_num) K :=
  turaevViro_move23 _ qBiedenharnElliott_three K h

/-- **Turaev–Viro at `r = 3` is invariant under the 1-4 move** (no hypotheses). -/
theorem turaevViro3_move14 {V : Type*} [DecidableEq V] (K : Complex3 V) {A B C D E : V}
    (h : IsMove14 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move14 K h) = turaevViro (r := 3) (by norm_num) K :=
  turaevViro_move14 _ qBiedenharnElliott_three qOrthogonality_three K h

end Lightlike.TV
