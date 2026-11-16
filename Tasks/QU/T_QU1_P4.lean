import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P4

q-Biedenharn–Elliott identity at r = 5.

The statement is `Lightlike.TV.qBiedenharnElliott_five`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. As T-QU1-P2 with colours `Fin 4`, exact arithmetic in ℚ(√5).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qBiedenharnElliott`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.turaevViro_move23` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qBiedenharnElliott_three` (`Lightlike/TuraevViro/LevelOne.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.TV.qBiedenharnElliott_five

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

/-- **q-Biedenharn–Elliott at `r = 5`.** -/
theorem qBiedenharnElliott_five : qBiedenharnElliott (r := 5) (by norm_num) := by
  have p5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s5 : (0:ℝ) < Real.sqrt 5 := by positivity
  have q1 : qnum 5 1 = 1 := qnum_one (by norm_num)
  obtain ⟨g, hgd⟩ : ∃ g : ℝ, g = (1 + Real.sqrt 5) / 2 := ⟨_, rfl⟩
  have g2 : g ^ 2 = g + 1 := by rw [hgd]; nlinarith [p5]
  have g0 : 0 < g := by rw [hgd]; positivity
  have q2 : qnum 5 2 = g := by
    unfold qnum
    push_cast
    have hs := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 5) (by positivity)
      (by linarith [Real.pi_pos])
    rw [show (2:ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.sin_two_mul,
      Real.cos_pi_div_five, hgd]
    field_simp
    norm_num
  have q3 : qnum 5 3 = g := by
    have := qnum_sub (r := 5) (n := 2) (by norm_num) (by norm_num)
    rw [show 5 - 2 = 3 from rfl] at this
    rw [this, q2]
  have q4 : qnum 5 4 = 1 := by
    have := qnum_sub (r := 5) (n := 1) (by norm_num) (by norm_num)
    rw [show 5 - 1 = 4 from rfl] at this
    rw [this, q1]
  have q5 : qnum 5 5 = 0 := qnum_self (by norm_num)
  have qf : ∀ n, qfact 5 n = if n ≤ 1 then 1 else if n = 2 then g
      else if n ≤ 4 then g + 1 else 0 := by
    intro n
    unfold qfact
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> simp [prod_range_succ, q1, q2, q3, q4] <;> nlinarith [g2]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact prod_eq_zero (mem_range.mpr (by omega : 4 < n)) q5
  have hinv : g⁻¹ = g - 1 := by
    field_simp
    nlinarith [g2]
  have hinv2 : (g + 1)⁻¹ = 2 - g := by
    field_simp
    nlinarith [g2]
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
  -- the exact ring ℤ[golden ratio] and its real embedding
  obtain ⟨φ, hφ⟩ : ∃ φ : QuadraticAlgebra ℤ 1 1 →ₐ[ℤ] ℝ,
      ∀ x : QuadraticAlgebra ℤ 1 1, φ x = (x.re : ℝ) + (x.im : ℝ) * g := by
    refine ⟨QuadraticAlgebra.lift ⟨g, by simp [← sq, g2] <;> ring⟩, fun x => ?_⟩
    simp
  have hK : ∀ a b : ℤ, φ ⟨a, b⟩ = (a : ℝ) + (b : ℝ) * g := fun a b => hφ ⟨a, b⟩
  let QF : ℕ → QuadraticAlgebra ℤ 1 1 := fun n =>
    if n ≤ 1 then ⟨1, 0⟩ else if n = 2 then ⟨0, 1⟩ else if n ≤ 4 then ⟨1, 1⟩ else ⟨0, 0⟩
  let IQ : ℕ → QuadraticAlgebra ℤ 1 1 := fun n =>
    if n ≤ 1 then ⟨1, 0⟩ else if n = 2 then ⟨-1, 1⟩ else if n ≤ 4 then ⟨2, -1⟩ else ⟨0, 0⟩
  let DM : ℕ → QuadraticAlgebra ℤ 1 1 := fun x => if x = 1 ∨ x = 2 then ⟨0, 1⟩ else ⟨1, 0⟩
  let IDM : ℕ → QuadraticAlgebra ℤ 1 1 := fun x => if x = 1 ∨ x = 2 then ⟨-1, 1⟩ else ⟨1, 0⟩
  let IQZ : ℤ → QuadraticAlgebra ℤ 1 1 := fun u => if 0 ≤ u then IQ u.toNat else 0
  let D2 : ℕ → ℕ → ℕ → QuadraticAlgebra ℤ 1 1 := fun a b c =>
    QF ((a + b + c) / 2 - a) * QF ((a + b + c) / 2 - b) * QF ((a + b + c) / 2 - c) *
      IQ ((a + b + c) / 2 + 1)
  let T : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℕ → QuadraticAlgebra ℤ 1 1 :=
    fun α₁ α₂ α₃ α₄ β₁ β₂ β₃ z =>
      if 0 ≤ (z : ℤ) - α₁ ∧ 0 ≤ (z : ℤ) - α₂ ∧ 0 ≤ (z : ℤ) - α₃ ∧ 0 ≤ (z : ℤ) - α₄ ∧
          0 ≤ β₁ - z ∧ 0 ≤ β₂ - z ∧ 0 ≤ β₃ - z then
        (-1) ^ z * QF (z + 1) *
          (IQZ (z - α₁) * IQZ (z - α₂) * IQZ (z - α₃) * IQZ (z - α₄) *
            (IQZ (β₁ - z) * IQZ (β₂ - z) * IQZ (β₃ - z)))
      else 0
  let R : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℤ 1 1 := fun j₁ j₂ j₃ j₄ j₅ j₆ =>
    ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
      T (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
        (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
        (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z
  let S6 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℤ 1 1 := fun a b c d e f =>
    if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then
      D2 a b c * D2 a e f * D2 d b f * D2 d e c * R a b c d e f ^ 2 else 0
  let G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → QuadraticAlgebra ℤ 1 1 := fun a b c d e f =>
    if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then R a b c d e f else 0
  have hchk : ∀ a d p : Fin 4, qAdm 5 a d p →
      ∀ c b : Fin 4, qAdm 5 c b p → ∀ f q : Fin 4, qAdm 5 c f q →
      ∀ e : Fin 4, qAdm 5 e d q → ∀ r : Fin 4, qAdm 5 e a r → qAdm 5 b f r →
      ∑ x ∈ range 4, (-1 : QuadraticAlgebra ℤ 1 1) ^ ((a.val + b + c + d + e + f + p + q + r + x) / 2) *
        DM x * (D2 a b x * D2 c d x * D2 e f x) *
        (G a b x c d p * G c d x e f q * G e f x b a r) =
      D2 p q r * (G p q r e a d * G p q r f b c) := by
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
    have hz : ∀ u : ℤ, ¬ 0 ≤ u → invQFact 5 u = 0 := fun u h => ite_eq_right_iff.mpr fun h' => absurd h' h
    simp only [T]
    split_ifs with hg
    · simp only [qRacahTerm, map_mul, map_pow, map_neg, map_one, hQF, hIQZ]
    · rw [map_zero]
      simp only [not_and_or] at hg
      unfold qRacahTerm
      rcases hg with h | h | h | h | h | h | h <;> rw [hz _ h] <;> ring
  have hG : ∀ a b c d e f, φ (G a b c d e f) =
      if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then
        qRacahSum 5 a b c d e f else 0 := fun a b c d e f => by
    simp only [G]
    split_ifs
    · exact hR _ _ _ _ _ _
    · simp
  have dsym : ∀ a b c, qDelta 5 a b c = qDelta 5 b c a := fun a b c => by
    unfold qDelta
    rw [show b + c + a = a + b + c by ring]
    congr 1
    ring
  have hf : ∀ a b c d e f, qSixJ 5 a b c d e f =
      if qAdm 5 a b c ∧ qAdm 5 a e f ∧ qAdm 5 d b f ∧ qAdm 5 d e c then
        qDelta 5 a b c * qDelta 5 a e f * qDelta 5 d b f * qDelta 5 d e c *
          qRacahSum 5 a b c d e f else 0 := fun _ _ _ _ _ _ => rfl
  have hle : ∀ a b c, qAdm 5 a b c → a ≤ 3 ∧ b ≤ 3 ∧ c ≤ 3 := fun a b c ⟨⟨_, h1, h2, h3⟩, h4⟩ => by
    have h5 : a + b + c ≤ 6 := h4
    omega
  have adm_cyc : ∀ a b c, qAdm 5 a b c → qAdm 5 b c a := fun a b c ⟨⟨h0, h1, h2, h3⟩, h4⟩ =>
    ⟨⟨by rw [show b + c + a = a + b + c by ring]; exact h0, by omega, by omega, by omega⟩,
      by rw [show b + c + a = a + b + c by ring]; exact h4⟩
  have adm_swap : ∀ a b c, qAdm 5 a b c → qAdm 5 b a c := fun a b c ⟨⟨h0, h1, h2, h3⟩, h4⟩ =>
    ⟨⟨by rw [show b + a + c = a + b + c by ring]; exact h0, by omega, by omega, by omega⟩,
      by rw [show b + a + c = a + b + c by ring]; exact h4⟩
  intro a b c d e f p q r
  simp only [tvModel, show (5 : ℕ) - 1 = 4 from rfl]
  by_cases hY : qAdm 5 a d p ∧ qAdm 5 c b p ∧ qAdm 5 c f q ∧ qAdm 5 e d q ∧ qAdm 5 e a r ∧
      qAdm 5 b f r
  · obtain ⟨hY1, hY2, hY3, hY4, hY5, hY6⟩ := hY
    have hb : a ≤ 3 ∧ b ≤ 3 ∧ c ≤ 3 ∧ d ≤ 3 ∧ e ≤ 3 ∧ f ≤ 3 ∧ p ≤ 3 ∧ q ≤ 3 ∧ r ≤ 3 := by
      have l1 := hle _ _ _ hY1; have l2 := hle _ _ _ hY2; have l3 := hle _ _ _ hY3
      have l4 := hle _ _ _ hY4; have l5 := hle _ _ _ hY5; have l6 := hle _ _ _ hY6
      exact ⟨l1.1, l2.2.1, l2.1, l1.2.1, l4.1, l3.2.1, l1.2.2, l3.2.2, l5.2.2⟩
    obtain ⟨ha, hb', hc', hd, he, hf', hp, hq, hr⟩ := hb
    have h := congrArg φ (hchk ⟨a, Nat.lt_succ_of_le ha⟩ ⟨d, Nat.lt_succ_of_le hd⟩
      ⟨p, Nat.lt_succ_of_le hp⟩ hY1 ⟨c, Nat.lt_succ_of_le hc'⟩ ⟨b, Nat.lt_succ_of_le hb'⟩ hY2
      ⟨f, Nat.lt_succ_of_le hf'⟩ ⟨q, Nat.lt_succ_of_le hq⟩ hY3 ⟨e, Nat.lt_succ_of_le he⟩ hY4
      ⟨r, Nat.lt_succ_of_le hr⟩ hY5 hY6)
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, hD2, hG] at h
    have hY1' : qAdm 5 p a d := adm_cyc _ _ _ (adm_cyc _ _ _ hY1)
    have hY2' : qAdm 5 p b c := qAdm_swap23 (adm_cyc _ _ _ (adm_cyc _ _ _ hY2))
    have hY3' : qAdm 5 f q c := adm_cyc _ _ _ hY3
    have hY4' : qAdm 5 e q d := qAdm_swap23 hY4
    have hY6' : qAdm 5 f b r := adm_swap _ _ _ hY6
    refine (Eq.trans ?_ (congrArg (fun t => qDelta 5 a d p * qDelta 5 c b p * qDelta 5 c f q *
      qDelta 5 e d q * qDelta 5 e a r * qDelta 5 b f r * t) h)).trans ?_
    · rw [mul_sum]
      refine sum_congr rfl fun x hx => ?_
      rw [hDM x (mem_range.mp hx), hf, hf, hf]
      by_cases hx3 : qAdm 5 a b x ∧ qAdm 5 c d x ∧ qAdm 5 e f x
      · obtain ⟨k1, k2, k3⟩ := hx3
        have k1' : qAdm 5 b a x := adm_swap _ _ _ k1
        simp only [k1, k2, k3, k1', hY1, hY2, hY3, hY4, hY5, hY6, and_self, ↓reduceIte]
        rw [qDelta_swap12 5 a b x]
        ring
      · by_cases k1 : qAdm 5 a b x
        · by_cases k2 : qAdm 5 c d x
          · have k3 : ¬ qAdm 5 e f x := fun k3 => hx3 ⟨k1, k2, k3⟩
            simp [k3]
          · simp [k2]
        · simp [k1]
    · rw [hf, hf]
      by_cases hpqr : qAdm 5 p q r
      · simp only [hpqr, hY1', hY2', hY3', hY4', hY5, hY6', and_self, ↓reduceIte]
        rw [dsym p a d, qDelta_swap23 5 e d q, dsym p b c, qDelta_swap12 5 c b p, dsym f q c,
          dsym q c f, qDelta_swap12 5 b f r]
        ring
      · simp [hpqr]
  · have z4 : qSixJ 5 p q r e a d * qSixJ 5 p q r f b c = 0 := by
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
