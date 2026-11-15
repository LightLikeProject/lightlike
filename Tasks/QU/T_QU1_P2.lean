import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P2

q-Biedenharn–Elliott identity at r = 4.

The statement is `Lightlike.TV.qBiedenharnElliott_four`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. As `qBiedenharnElliott_three` with colours `Fin 3`, exact arithmetic in ℚ(√2).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qBiedenharnElliott`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.turaevViro_move23` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qBiedenharnElliott_three` (`Lightlike/TuraevViro/LevelOne.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.TV.qBiedenharnElliott_four

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

/-- **q-Biedenharn–Elliott at `r = 4`.** -/
theorem qBiedenharnElliott_four : qBiedenharnElliott (r := 4) (by norm_num) := by
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
  let G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℚ 2 0 := fun a b c d e f =>
    if qAdm 4 a b c ∧ qAdm 4 a e f ∧ qAdm 4 d b f ∧ qAdm 4 d e c then R a b c d e f else 0
  have hchk : ∀ a b c d e f p q r : Fin 3,
      (qAdm 4 a d p ∧ qAdm 4 c b p ∧ qAdm 4 c f q ∧ qAdm 4 e d q ∧ qAdm 4 e a r ∧ qAdm 4 b f r) →
      ∑ x ∈ range 3, (-1 : QuadraticAlgebra ℚ 2 0) ^ ((a.val + b + c + d + e + f + p + q + r + x) / 2) *
        DM x * (D2 a b x * D2 c d x * D2 e f x) *
        (G a b x c d p * G c d x e f q * G e f x b a r) =
      D2 p q r * (G p q r e a d * G p q r f b c) := by
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
  have hG : ∀ a b c d e f, φ (G a b c d e f) =
      if qAdm 4 a b c ∧ qAdm 4 a e f ∧ qAdm 4 d b f ∧ qAdm 4 d e c then
        qRacahSum 4 a b c d e f else 0 := fun a b c d e f => by
    simp only [G]
    split_ifs
    · exact hR _ _ _ _ _ _
    · simp
  have dsym : ∀ a b c, qDelta 4 a b c = qDelta 4 b c a := fun a b c => by
    unfold qDelta
    rw [show b + c + a = a + b + c by ring]
    congr 1
    ring
  have hf : ∀ a b c d e f, qSixJ 4 a b c d e f =
      if qAdm 4 a b c ∧ qAdm 4 a e f ∧ qAdm 4 d b f ∧ qAdm 4 d e c then
        qDelta 4 a b c * qDelta 4 a e f * qDelta 4 d b f * qDelta 4 d e c *
          qRacahSum 4 a b c d e f else 0 := fun _ _ _ _ _ _ => rfl
  have hle : ∀ a b c, qAdm 4 a b c → a ≤ 2 ∧ b ≤ 2 ∧ c ≤ 2 := fun a b c ⟨⟨_, h1, h2, h3⟩, h4⟩ => by
    have h5 : a + b + c ≤ 4 := h4
    omega
  have adm_cyc : ∀ a b c, qAdm 4 a b c → qAdm 4 b c a := fun a b c ⟨⟨h0, h1, h2, h3⟩, h4⟩ =>
    ⟨⟨by rw [show b + c + a = a + b + c by ring]; exact h0, by omega, by omega, by omega⟩,
      by rw [show b + c + a = a + b + c by ring]; exact h4⟩
  have adm_swap : ∀ a b c, qAdm 4 a b c → qAdm 4 b a c := fun a b c ⟨⟨h0, h1, h2, h3⟩, h4⟩ =>
    ⟨⟨by rw [show b + a + c = a + b + c by ring]; exact h0, by omega, by omega, by omega⟩,
      by rw [show b + a + c = a + b + c by ring]; exact h4⟩
  intro a b c d e f p q r
  simp only [tvModel, show (4 : ℕ) - 1 = 3 from rfl]
  by_cases hY : qAdm 4 a d p ∧ qAdm 4 c b p ∧ qAdm 4 c f q ∧ qAdm 4 e d q ∧ qAdm 4 e a r ∧
      qAdm 4 b f r
  · obtain ⟨hY1, hY2, hY3, hY4, hY5, hY6⟩ := hY
    have hb : a ≤ 2 ∧ b ≤ 2 ∧ c ≤ 2 ∧ d ≤ 2 ∧ e ≤ 2 ∧ f ≤ 2 ∧ p ≤ 2 ∧ q ≤ 2 ∧ r ≤ 2 := by
      have l1 := hle _ _ _ hY1; have l2 := hle _ _ _ hY2; have l3 := hle _ _ _ hY3
      have l4 := hle _ _ _ hY4; have l5 := hle _ _ _ hY5; have l6 := hle _ _ _ hY6
      exact ⟨l1.1, l2.2.1, l2.1, l1.2.1, l4.1, l3.2.1, l1.2.2, l3.2.2, l5.2.2⟩
    obtain ⟨ha, hb', hc', hd, he, hf', hp, hq, hr⟩ := hb
    have h := congrArg φ (hchk ⟨a, Nat.lt_succ_of_le ha⟩ ⟨b, Nat.lt_succ_of_le hb'⟩
      ⟨c, Nat.lt_succ_of_le hc'⟩ ⟨d, Nat.lt_succ_of_le hd⟩ ⟨e, Nat.lt_succ_of_le he⟩
      ⟨f, Nat.lt_succ_of_le hf'⟩ ⟨p, Nat.lt_succ_of_le hp⟩ ⟨q, Nat.lt_succ_of_le hq⟩
      ⟨r, Nat.lt_succ_of_le hr⟩ ⟨hY1, hY2, hY3, hY4, hY5, hY6⟩)
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, hD2, hG] at h
    have hY1' : qAdm 4 p a d := adm_cyc _ _ _ (adm_cyc _ _ _ hY1)
    have hY2' : qAdm 4 p b c := qAdm_swap23 (adm_cyc _ _ _ (adm_cyc _ _ _ hY2))
    have hY3' : qAdm 4 f q c := adm_cyc _ _ _ hY3
    have hY4' : qAdm 4 e q d := qAdm_swap23 hY4
    have hY6' : qAdm 4 f b r := adm_swap _ _ _ hY6
    refine (Eq.trans ?_ (congrArg (fun t => qDelta 4 a d p * qDelta 4 c b p * qDelta 4 c f q *
      qDelta 4 e d q * qDelta 4 e a r * qDelta 4 b f r * t) h)).trans ?_
    · rw [mul_sum]
      refine sum_congr rfl fun x hx => ?_
      rw [hDM x (mem_range.mp hx), hf, hf, hf]
      by_cases hx3 : qAdm 4 a b x ∧ qAdm 4 c d x ∧ qAdm 4 e f x
      · obtain ⟨k1, k2, k3⟩ := hx3
        have k1' : qAdm 4 b a x := adm_swap _ _ _ k1
        simp only [k1, k2, k3, k1', hY1, hY2, hY3, hY4, hY5, hY6, and_self, ↓reduceIte]
        rw [qDelta_swap12 4 a b x]
        ring
      · by_cases k1 : qAdm 4 a b x
        · by_cases k2 : qAdm 4 c d x
          · have k3 : ¬ qAdm 4 e f x := fun k3 => hx3 ⟨k1, k2, k3⟩
            simp [k3]
          · simp [k2]
        · simp [k1]
    · rw [hf, hf]
      by_cases hpqr : qAdm 4 p q r
      · simp only [hpqr, hY1', hY2', hY3', hY4', hY5, hY6', and_self, ↓reduceIte]
        rw [dsym p a d, qDelta_swap23 4 e d q, dsym p b c, qDelta_swap12 4 c b p, dsym f q c,
          dsym q c f, qDelta_swap12 4 b f r]
        ring
      · simp [hpqr]
  · have z4 : qSixJ 4 p q r e a d * qSixJ 4 p q r f b c = 0 := by
      by_contra hne
      obtain ⟨n4, n5⟩ := mul_ne_zero_iff.mp hne
      obtain ⟨_, k1, k4, k5⟩ := qSixJ_ok n4
      obtain ⟨_, k2, k3, k6⟩ := qSixJ_ok n5
      exact hY ⟨adm_cyc _ _ _ k1, adm_cyc _ _ _ (qAdm_swap23 k2),
        adm_cyc _ _ _ (adm_cyc _ _ _ k3), qAdm_swap23 k4, k5, adm_swap _ _ _ k6⟩
    rw [z4]
    refine sum_eq_zero fun x _ => ?_
    by_contra hne
    obtain ⟨_, h3⟩ := mul_ne_zero_iff.mp hne
    obtain ⟨h12, h3'⟩ := mul_ne_zero_iff.mp h3
    obtain ⟨n1, n2⟩ := mul_ne_zero_iff.mp h12
    exact hY ⟨(qSixJ_ok n1).2.1, (qSixJ_ok n1).2.2.1, (qSixJ_ok n2).2.1, (qSixJ_ok n2).2.2.1,
      (qSixJ_ok h3').2.1, (qSixJ_ok h3').2.2.1⟩

end Lightlike.TV
