import Lightlike.TuraevViro.Reflect.OrthConditional
import Lightlike.TuraevViro.Reflect.SixJSingle
import Lightlike.TuraevViro.Reflect.QDougallMap

/-!
# Non-vacuity of the boundary evaluation `QDougall`

The conditional results `sixj_norm_one` and `qOrthogonality_of` assume `QDougall` and `QDougallAll`.
These checks show the hypotheses are satisfiable: `QDougall` at level `2` (all spins `0`) and at
level `3` (spins `1, 1, 1, 1`, where the sum is `(-1)² = 1`), `QDougallAll` at level `2`, and a
control where the evaluation fails (an inadmissible colour). It also checks that the hypotheses
of `Sj_single` (the one-term form of the sum at the lowest sixth colour) hold at level `3`. Not a proof of `QDougall` in general.
-/

namespace Lightlike.TV.Refl
open Lightlike.TV Finset

/-- At level `2`, `[1] = 1`. -/
lemma qnum_two_one : qnum 2 1 = 1 := by
  unfold qnum
  simp

/-- The empty q-factorial is `1`. -/
lemma qfact_zero' (r : ℕ) : qfact r 0 = 1 := by simp [qfact]

/-- At level `2`, `[1]! = 1`. -/
lemma qfact_two_one : qfact 2 1 = 1 := by
  rw [qfact, Finset.prod_range_one]; simpa using qnum_two_one

/-- At level `2`, `Δ(0, 0, 0) = 1`. -/
lemma qDelta_two_zero : qDelta 2 0 0 0 = 1 := by
  simp [qDelta, qfact_zero', qfact_two_one]

/-- Non-vacuity: the boundary evaluation holds at level `2`, all spins `0`. -/
theorem qDougall_two : QDougall 2 0 0 0 0 0 0 0 := by
  unfold QDougall jOmega Sj SR qRacahTerm
  simp [qnum_two_one, qDelta_two_zero, qfact_two_one, qfact_zero', invQFact]

/-- The hypothesis `QDougallAll` holds at level `r = 2`, where the only colour is `0`. -/
lemma qDougallAll_two : QDougallAll 2 := by
  intro B A E F q h1 h2
  have hB : B = 0 := by have := h1.2; omega
  have hA : A = 0 := by have := h2.2; omega
  have hE : E = 0 := by have := h2.2; omega
  have hF : F = 0 := by have := h1.2; omega
  subst hB hA hE hF
  have : QDougall 2 0 0 0 0 0 0 0 := by
    unfold QDougall jOmega Sj SR qRacahTerm
    simp [qnum_two_one, qDelta_two_zero, qfact_two_one, qfact_zero', invQFact]
  simpa [QDougallAt, aLo, aHi] using this

/-- At level `3`, `[1] = 1`. -/
lemma qnum_three_one : qnum 3 1 = 1 := by
  unfold qnum
  have h : Real.sin (Real.pi / 3) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  simp

/-- At level `3`, `[2] = 1` (`sin (2π/3) = sin (π/3)`). -/
lemma qnum_three_two : qnum 3 2 = 1 := by
  unfold qnum
  have h : Real.sin (Real.pi / 3) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  have : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  push_cast
  rw [this, Real.sin_pi_sub]
  exact div_self h

/-- At level `3`, `[3] = 0`. -/
lemma qnum_three_three : qnum 3 3 = 0 := by
  unfold qnum
  push_cast
  have : (3 : ℝ) * Real.pi / 3 = Real.pi := by ring
  rw [this, Real.sin_pi]; simp

/-- At level `3`, `[2]! = 1`. -/
lemma qfact_three_two : qfact 3 2 = 1 := by
  simp [qfact, Finset.prod_range_succ, qnum_three_one, qnum_three_two]

/-- At level `3`, `[3]! = 0`. -/
lemma qfact_three_three : qfact 3 3 = 0 := by
  simp [qfact, Finset.prod_range_succ, qnum_three_one, qnum_three_two, qnum_three_three]

/-- At level `3`, `[1]! = 1`. -/
lemma qfact_three_one : qfact 3 1 = 1 := by
  simp [qfact, qnum_three_one]

/-- Non-vacuity at level `3`, spins `(1, 1, 1, 1)`: the sum is `(-1)² = 1`, a nontrivial value. -/
theorem qDougall_three : QDougall 3 1 1 1 1 0 0 0 := by
  unfold QDougall jOmega Sj SR qRacahTerm qDelta
  norm_num [qnum_three_one, qfact_three_one, qfact_three_two, qfact_three_three, qfact_zero', invQFact, Finset.sum_range_succ]

/-- Wrong-input control: the sixth colour `2` is not admissible at level `3`, and the evaluation fails. -/
theorem not_qDougall_three_bad : ¬ QDougall 3 1 1 1 1 0 0 2 := by
  unfold QDougall jOmega Sj SR qRacahTerm qDelta
  norm_num [qnum_three_one, qnum_three_two, qfact_three_one, qfact_three_two, qfact_three_three, qfact_zero', invQFact, Finset.sum_range_succ, qnum_three_three]

/-- Non-vacuity of `Sj_single`: at spins `(1, 1, 1, 1)`, sixth colour `0 = j₁ - j₅` and third colour
`0`, the hypotheses hold and the sum is a single term. -/
theorem Sj_single_three :
    ∃ z0 : ℕ, Sj 3 1 1 1 1 0 (0 : ℤ) =
      qRacahTerm 3 (((1 : ℤ) + 1 + 0) / 2) (((1 : ℤ) + 1 + 0) / 2) (((1 : ℤ) + 1 + 0) / 2)
        (((1 : ℤ) + 1 + 0) / 2) (((1 : ℤ) + 1 + 1 + 1) / 2) ((0 + 1 + 1 + 0) / 2)
        ((0 + 1 + 0 + 1) / 2) z0 :=
  Sj_single 3 1 1 1 1 0 0 (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
