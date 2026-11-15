import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P1

q-orthogonality of the quantum 6j symbols at r = 4.

The statement is `Lightlike.TV.qOrthogonality_four`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. As `qOrthogonality_three` (`Lightlike/TuraevViro/LevelOne.lean`) with colours `Fin 3`; the
q-numbers involve √2, so evaluate exactly in ℚ(√2) instead of `decide` on reals.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qOrthogonality`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qOrthogonality_three` (`Lightlike/TuraevViro/LevelOne.lean`)
* `TV.Refl.qOrthogonality_of` (`Lightlike/TuraevViro/Reflect/OrthConditional.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.TV.qOrthogonality_four

## References

Milestone QU1 (q-deformed Biedenharn–Elliott identity and orthogonality for `r ≥ 4`), ROADMAP
section "Quantum groups and state-sum TQFTs".
Source: V. G. Turaev, Quantum Invariants of Knots and 3-Manifolds, de Gruyter Studies in Mathematics
18 (1994), Chapter VI. 6j-symbols (`turaev-1994` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- **q-orthogonality at `r = 4`.** -/
theorem qOrthogonality_four : qOrthogonality (r := 4) (by norm_num) := by
  have p2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have q1 : qnum 4 1 = 1 := qnum_one (by norm_num)
  have q2 : qnum 4 2 = Real.sqrt 2 := by
    unfold qnum
    push_cast
    rw [show (2:ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two, Real.sin_pi_div_four]
    have : (0:ℝ) < Real.sqrt 2 := by positivity
    field_simp
    nlinarith [p2]
  have q3 : qnum 4 3 = 1 := by
    have := qnum_sub (r := 4) (n := 1) (by norm_num) (by norm_num)
    rw [show 4 - 1 = 3 from rfl] at this
    rw [this, q1]
  have q4 : qnum 4 4 = 0 := qnum_self (by norm_num)
  have qf : ∀ n, qfact 4 n = if n ≤ 1 then 1 else if n ≤ 3 then Real.sqrt 2 else 0 := by
    intro n
    unfold qfact
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [prod_range_succ, q1, q2, q3]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact prod_eq_zero (mem_range.mpr (by omega : 3 < n)) q4
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have : (0:ℝ) < Real.sqrt 2 := by positivity
    field_simp
    nlinarith [p2]
  have qfn : ∀ n, 0 ≤ qfact 4 n := fun n => by
    rw [qf]; split_ifs <;> positivity
  have dsq : ∀ a b c : ℕ, qDelta 4 a b c ^ 2 =
      qfact 4 ((a + b + c) / 2 - a) * qfact 4 ((a + b + c) / 2 - b) *
        qfact 4 ((a + b + c) / 2 - c) / qfact 4 ((a + b + c) / 2 + 1) := fun a b c => by
    unfold qDelta
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (mul_nonneg (qfn _) (qfn _)) (qfn _)) (qfn _))
  have sq6 : ∀ a b c d e f : ℕ, qSixJ 4 a b c d e f ^ 2 =
      if qAdm 4 a b c ∧ qAdm 4 a e f ∧ qAdm 4 d b f ∧ qAdm 4 d e c then
        (qDelta 4 a b c ^ 2) * (qDelta 4 a e f ^ 2) * (qDelta 4 d b f ^ 2) * (qDelta 4 d e c ^ 2) *
          qRacahSum 4 a b c d e f ^ 2 else 0 := by
    intro a b c d e f
    unfold qSixJ
    split_ifs
    · ring
    · simp
  -- the exact field ℚ(√2) and its real embedding
  obtain ⟨φ, hφ⟩ : ∃ φ : QuadraticAlgebra ℚ 2 0 →ₐ[ℚ] ℝ,
      ∀ x : QuadraticAlgebra ℚ 2 0, φ x = (x.re : ℝ) + (x.im : ℝ) * Real.sqrt 2 := by
    refine ⟨QuadraticAlgebra.lift ⟨Real.sqrt 2, by simp⟩, fun x => ?_⟩
    simp [Rat.smul_def]
  -- exact data in ℚ(√2)
  have hK : ∀ a b : ℚ, φ ⟨a, b⟩ = (a : ℝ) + (b : ℝ) * Real.sqrt 2 := fun a b => hφ ⟨a, b⟩
  -- exact data in ℚ(√2)
  let QF : ℕ → QuadraticAlgebra ℚ 2 0 := fun n => if n ≤ 1 then ⟨1, 0⟩ else if n ≤ 3 then ⟨0, 1⟩ else ⟨0, 0⟩
  let IQ : ℕ → QuadraticAlgebra ℚ 2 0 := fun n =>
    if n ≤ 1 then ⟨1, 0⟩ else if n ≤ 3 then ⟨0, 1 / 2⟩ else ⟨0, 0⟩
  let DM : ℕ → QuadraticAlgebra ℚ 2 0 := fun x => if x = 1 then ⟨0, 1⟩ else ⟨1, 0⟩
  let IDM : ℕ → QuadraticAlgebra ℚ 2 0 := fun x => if x = 1 then ⟨0, 1 / 2⟩ else ⟨1, 0⟩
  let IQZ : ℤ → QuadraticAlgebra ℚ 2 0 := fun u => if 0 ≤ u then IQ u.toNat else 0
  let D2 : ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 2 0 := fun a b c =>
    QF ((a + b + c) / 2 - a) * QF ((a + b + c) / 2 - b) * QF ((a + b + c) / 2 - c) *
      IQ ((a + b + c) / 2 + 1)
  let T : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℕ → QuadraticAlgebra ℚ 2 0 :=
    fun α₁ α₂ α₃ α₄ β₁ β₂ β₃ z =>
      (-1) ^ z * QF (z + 1) *
        (IQZ (z - α₁) * IQZ (z - α₂) * IQZ (z - α₃) * IQZ (z - α₄) *
          (IQZ (β₁ - z) * IQZ (β₂ - z) * IQZ (β₃ - z)))
  let R : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 2 0 := fun j₁ j₂ j₃ j₄ j₅ j₆ =>
    ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
      T (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
        (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z
  let S6 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 2 0 := fun a b c d e f =>
    if qAdm 4 a b c ∧ qAdm 4 a e f ∧ qAdm 4 d b f ∧ qAdm 4 d e c then
      D2 a b c * D2 a e f * D2 d b f * D2 d e c * R a b c d e f ^ 2 else 0
  have hchk : ∀ B A E F q : Fin 3, ∑ x ∈ range 3, DM x * S6 B A x E F q =
      if qAdm 4 A E q ∧ qAdm 4 B q F then IDM q else 0 := by
    decide +kernel
  have hQF : ∀ n, φ (QF n) = qfact 4 n := fun n => by
    rw [qf]
    by_cases h1 : n ≤ 1 <;> by_cases h2 : n ≤ 3 <;>
      simp [QF, h1, h2, hK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hIQ : ∀ n, φ (IQ n) = (qfact 4 n)⁻¹ := fun n => by
    rw [qf]
    by_cases h1 : n ≤ 1 <;> by_cases h2 : n ≤ 3 <;>
      simp [IQ, h1, h2, hK, hinv, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring
  have hDM : ∀ x, x < 3 → φ (DM x) = qnum 4 (x + 1) := fun x hx => by
    interval_cases x <;> simp [DM, hK, q1, q2, q3, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hIDM : ∀ x, x < 3 → φ (IDM x) = 1 / qnum 4 (x + 1) := fun x hx => by
    interval_cases x <;> simp [IDM, hK, q1, q2, q3, hinv, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
    ring
  have hIQZ : ∀ u, φ (IQZ u) = invQFact 4 u := fun u => by
    simp only [IQZ, invQFact]
    split_ifs <;> simp [hIQ]
  have hD2 : ∀ a b c, φ (D2 a b c) = qDelta 4 a b c ^ 2 := fun a b c => by
    rw [dsq]
    simp only [D2, map_mul, hQF, hIQ, div_eq_mul_inv]
  have hR : ∀ a b c d e f, φ (R a b c d e f) = qRacahSum 4 a b c d e f := fun a b c d e f => by
    simp only [R, qRacahSum, map_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [T, qRacahTerm, map_mul, map_pow, map_neg, map_one, hQF, hIQZ]
  have hS6 : ∀ a b c d e f, φ (S6 a b c d e f) = qSixJ 4 a b c d e f ^ 2 := fun a b c d e f => by
    rw [sq6]
    simp only [S6]
    split_ifs
    · simp only [map_mul, map_pow, hD2, hR]
    · simp
  intro B A E F q
  simp only [tvModel, show (4 : ℕ) - 1 = 3 from rfl]
  by_cases hc : qAdm 4 A E q ∧ qAdm 4 B q F
  · rw [ite_eq_left hc]
    have hb : B ≤ 2 ∧ A ≤ 2 ∧ E ≤ 2 ∧ F ≤ 2 ∧ q ≤ 2 := by
      obtain ⟨h1, h2⟩ := hc
      unfold qAdm Tri at h1 h2; omega
    obtain ⟨hB, hA, hE, hF, hq⟩ := hb
    have h := congrArg φ (hchk ⟨B, by omega⟩ ⟨A, by omega⟩ ⟨E, by omega⟩ ⟨F, by omega⟩
      ⟨q, by omega⟩)
    simp only [ite_eq_left hc, map_sum, map_mul] at h
    rw [hIDM q (by omega)] at h
    rw [← h]
    refine sum_congr rfl fun x hx => ?_
    rw [hDM x (mem_range.mp hx), hS6]
  · rw [ite_eq_right hc]
    refine sum_eq_zero fun x _ => ?_
    have h0 : qSixJ 4 B A x E F q = 0 := by
      by_contra h
      obtain ⟨-, h2, h3, -⟩ := qSixJ_ok h
      exact hc ⟨qAdm_swap12 h3, qAdm_swap23 h2⟩
    rw [h0]; ring

end Lightlike.TV
