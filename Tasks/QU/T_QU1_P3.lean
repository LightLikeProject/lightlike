import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P3

q-orthogonality of the quantum 6j symbols at r = 5.

The statement is `Lightlike.TV.qOrthogonality_five`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. As T-QU1-P1 with colours `Fin 4`; sin(π/5) involves the golden ratio, so work in ℚ(√5).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qOrthogonality`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qOrthogonality_three` (`Lightlike/TuraevViro/LevelOne.lean`)
* `TV.Refl.qOrthogonality_of` (`Lightlike/TuraevViro/Reflect/OrthConditional.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.TV.qOrthogonality_five

## References

Milestone QU1 (q-deformed Biedenharn–Elliott identity and orthogonality for `r ≥ 4`), ROADMAP
section "Quantum groups and state-sum TQFTs".
Source: V. G. Turaev, Quantum Invariants of Knots and 3-Manifolds, de Gruyter Studies in Mathematics
18 (1994), Chapter VI. 6j-symbols; R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (3.2.1); R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (3.2.2); R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (0.5.11) (`turaev-1994`, `koekoek-swarttouw-1996`,
`koekoek-swarttouw-1996`, `koekoek-swarttouw-1996` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- **q-orthogonality at `r = 5`.** -/
theorem qOrthogonality_five : qOrthogonality (r := 5) (by norm_num) := by
  have p5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s5 : (0:ℝ) < Real.sqrt 5 := by positivity
  have q1 : qnum 5 1 = 1 := qnum_one (by norm_num)
  have q2 : qnum 5 2 = (1 + Real.sqrt 5) / 2 := by
    unfold qnum
    push_cast
    have hs := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 5) (by positivity)
      (by linarith [Real.pi_pos])
    rw [show (2:ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.sin_two_mul,
      Real.cos_pi_div_five]
    field_simp
    norm_num
  have q3 : qnum 5 3 = (1 + Real.sqrt 5) / 2 := by
    have := qnum_sub (r := 5) (n := 2) (by norm_num) (by norm_num)
    rw [show 5 - 2 = 3 from rfl] at this
    rw [this, q2]
  have q4 : qnum 5 4 = 1 := by
    have := qnum_sub (r := 5) (n := 1) (by norm_num) (by norm_num)
    rw [show 5 - 1 = 4 from rfl] at this
    rw [this, q1]
  have q5 : qnum 5 5 = 0 := qnum_self (by norm_num)
  have qf : ∀ n, qfact 5 n = if n ≤ 1 then 1 else if n = 2 then (1 + Real.sqrt 5) / 2
      else if n ≤ 4 then (3 + Real.sqrt 5) / 2 else 0 := by
    intro n
    unfold qfact
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> simp [prod_range_succ, q1, q2, q3, q4] <;> nlinarith [p5]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact prod_eq_zero (mem_range.mpr (by omega : 4 < n)) q5
  have hinv : ((1 + Real.sqrt 5) / 2)⁻¹ = (-1 + Real.sqrt 5) / 2 := by
    field_simp
    nlinarith [p5]
  have hinv2 : ((3 + Real.sqrt 5) / 2)⁻¹ = (3 - Real.sqrt 5) / 2 := by
    field_simp
    nlinarith [p5]
  have qfn : ∀ n, 0 ≤ qfact 5 n := fun n => by
    rw [qf]; split_ifs <;> positivity
  have dsq : ∀ a b c : ℕ, qDelta 5 a b c ^ 2 =
      qfact 5 ((a + b + c) / 2 - a) * qfact 5 ((a + b + c) / 2 - b) *
        qfact 5 ((a + b + c) / 2 - c) / qfact 5 ((a + b + c) / 2 + 1) := fun a b c => by
    unfold qDelta
    exact Real.sq_sqrt (div_nonneg (mul_nonneg (mul_nonneg (qfn _) (qfn _)) (qfn _)) (qfn _))
  have sq6 : ∀ a b c d e f : ℕ, qSixJ 5 a b c d e f ^ 2 =
      if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then
        (qDelta 5 a b c ^ 2) * (qDelta 5 a e f ^ 2) * (qDelta 5 d b f ^ 2) * (qDelta 5 d e c ^ 2) *
          qRacahSum 5 a b c d e f ^ 2 else 0 := by
    intro a b c d e f
    unfold qSixJ
    split_ifs
    · ring
    · simp
  -- the exact field ℚ(√5) and its real embedding
  obtain ⟨φ, hφ⟩ : ∃ φ : QuadraticAlgebra ℚ 5 0 →ₐ[ℚ] ℝ,
      ∀ x : QuadraticAlgebra ℚ 5 0, φ x = (x.re : ℝ) + (x.im : ℝ) * Real.sqrt 5 := by
    refine ⟨QuadraticAlgebra.lift ⟨Real.sqrt 5, by simp⟩, fun x => ?_⟩
    simp [Rat.smul_def]
  -- exact data in ℚ(√5)
  have hK : ∀ a b : ℚ, φ ⟨a, b⟩ = (a : ℝ) + (b : ℝ) * Real.sqrt 5 := fun a b => hφ ⟨a, b⟩
  -- exact data in ℚ(√5)
  let QF : ℕ → QuadraticAlgebra ℚ 5 0 := fun n =>
    if n ≤ 1 then ⟨1, 0⟩ else if n = 2 then ⟨1 / 2, 1 / 2⟩ else if n ≤ 4 then ⟨3 / 2, 1 / 2⟩ else ⟨0, 0⟩
  let IQ : ℕ → QuadraticAlgebra ℚ 5 0 := fun n =>
    if n ≤ 1 then ⟨1, 0⟩ else if n = 2 then ⟨-1 / 2, 1 / 2⟩ else if n ≤ 4 then ⟨3 / 2, -1 / 2⟩
      else ⟨0, 0⟩
  let DM : ℕ → QuadraticAlgebra ℚ 5 0 := fun x => if x = 1 ∨ x = 2 then ⟨1 / 2, 1 / 2⟩ else ⟨1, 0⟩
  let IDM : ℕ → QuadraticAlgebra ℚ 5 0 := fun x =>
    if x = 1 ∨ x = 2 then ⟨-1 / 2, 1 / 2⟩ else ⟨1, 0⟩
  let IQZ : ℤ → QuadraticAlgebra ℚ 5 0 := fun u => if 0 ≤ u then IQ u.toNat else 0
  let D2 : ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 5 0 := fun a b c =>
    QF ((a + b + c) / 2 - a) * QF ((a + b + c) / 2 - b) * QF ((a + b + c) / 2 - c) *
      IQ ((a + b + c) / 2 + 1)
  let T : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℕ → QuadraticAlgebra ℚ 5 0 :=
    fun α₁ α₂ α₃ α₄ β₁ β₂ β₃ z =>
      (-1) ^ z * QF (z + 1) *
        (IQZ (z - α₁) * IQZ (z - α₂) * IQZ (z - α₃) * IQZ (z - α₄) *
          (IQZ (β₁ - z) * IQZ (β₂ - z) * IQZ (β₃ - z)))
  let R : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 5 0 := fun j₁ j₂ j₃ j₄ j₅ j₆ =>
    ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
      T (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
        (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z
  let S6 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 5 0 := fun a b c d e f =>
    if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then
      D2 a b c * D2 a e f * D2 d b f * D2 d e c * R a b c d e f ^ 2 else 0
  have hchk : ∀ B A E F q : Fin 4, ∑ x ∈ range 4, DM x * S6 B A x E F q =
      if qAdm 5 A E q ∧ qAdm 5 B q F then IDM q else 0 := by
    decide +kernel
  have hQF : ∀ n, φ (QF n) = qfact 5 n := fun n => by
    rw [qf]
    by_cases h1 : n ≤ 1 <;> by_cases h2 : n = 2 <;> by_cases h3 : n ≤ 4 <;>
      simp [QF, h1, h2, h3, hK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> ring
  have hIQ : ∀ n, φ (IQ n) = (qfact 5 n)⁻¹ := fun n => by
    rw [qf]
    by_cases h1 : n ≤ 1 <;> by_cases h2 : n = 2 <;> by_cases h3 : n ≤ 4 <;>
      simp [IQ, h1, h2, h3, hK, hinv, hinv2, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;>
      ring
  have hDM : ∀ x, x < 4 → φ (DM x) = qnum 5 (x + 1) := fun x hx => by
    interval_cases x <;> simp [DM, hK, q1, q2, q3, q4, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one] <;> ring
  have hIDM : ∀ x, x < 4 → φ (IDM x) = 1 / qnum 5 (x + 1) := fun x hx => by
    interval_cases x <;> simp [IDM, hK, q1, q2, q3, q4, hinv, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one] <;> ring
  have hIQZ : ∀ u, φ (IQZ u) = invQFact 5 u := fun u => by
    simp only [IQZ, invQFact]
    split_ifs <;> simp [hIQ]
  have hD2 : ∀ a b c, φ (D2 a b c) = qDelta 5 a b c ^ 2 := fun a b c => by
    rw [dsq]
    simp only [D2, map_mul, hQF, hIQ, div_eq_mul_inv]
  have hR : ∀ a b c d e f, φ (R a b c d e f) = qRacahSum 5 a b c d e f := fun a b c d e f => by
    simp only [R, qRacahSum, map_sum]
    refine sum_congr rfl fun z _ => ?_
    simp only [T, qRacahTerm, map_mul, map_pow, map_neg, map_one, hQF, hIQZ]
  have hS6 : ∀ a b c d e f, φ (S6 a b c d e f) = qSixJ 5 a b c d e f ^ 2 := fun a b c d e f => by
    rw [sq6]
    simp only [S6]
    split_ifs
    · simp only [map_mul, map_pow, hD2, hR]
    · simp
  intro B A E F q
  simp only [tvModel, show (5 : ℕ) - 1 = 4 from rfl]
  by_cases hc : qAdm 5 A E q ∧ qAdm 5 B q F
  · rw [ite_eq_left hc]
    have hb : B ≤ 3 ∧ A ≤ 3 ∧ E ≤ 3 ∧ F ≤ 3 ∧ q ≤ 3 := by
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
    have h0 : qSixJ 5 B A x E F q = 0 := by
      by_contra h
      obtain ⟨-, h2, h3, -⟩ := qSixJ_ok h
      exact hc ⟨qAdm_swap12 h3, qAdm_swap23 h2⟩
    rw [h0]; ring

end Lightlike.TV
