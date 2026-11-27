import Mathlib
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TemperleyLieb.OneStrand

/-!
# The Kauffman–Lins coefficient with a third block of one strand

The values of `klCoef q a b 1 e d f d'` (third block of one strand) in the four admissible cases, in the
indexing of `Fc` (`E = e` or `e + 1`, `X = a + b - 2E`):

* `klCoef_one_00`: `klCoef q a b 1 E 0 0 E = [a+b-E+2][b-E+1] / ([b+1][X+2])`;
* `klCoef_one_01`: `klCoef q a b 1 E 0 1 (E-1) = -[a-E+1] / [X+2]`;
* `klCoef_one_10`: `klCoef q a b 1 (E-1) 1 0 E = [E] / [b+1]`;
* `klCoef_one_11`: `klCoef q a b 1 (E-1) 1 1 (E-1) = 1`.

In each case the tetrahedral sum has a single term (the largest face sum equals the smallest sum of opposite
edges). Numerical evidence (not proof): the four formulas agree with `klCoef` in exact rational arithmetic at
`q = 3/2` for `a, b ≤ 5`.
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- **A tetrahedral net with a single term**: when the largest face sum equals the smallest sum of opposite edges. -/
lemma tetKL_eq_single (q : kˣ) {a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ}
    (h1 : (a + b + i) / 2 = F₁) (h2 : (i + c + D) / 2 = F₂) (h3 : (b + c + j) / 2 = F₃) (h4 : (a + j + D) / 2 = F₄)
    (g1 : (b + D + i + j) / 2 = B₁) (g2 : (a + c + i + j) / 2 = B₂) (g3 : (a + b + c + D) / 2 = B₃)
    (hmax : max (max F₁ F₂) (max F₃ F₄) = z) (hmin : min B₁ (min B₂ B₃) = z) :
    tetKL q a b c D i j = tetPre q a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ * tetTerm q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  unfold tetKL
  simp only [h1, h2, h3, h4, g1, g2, g3, hmax, hmin, Icc_self, sum_singleton]

/-- **A single-term tetrahedral net, evaluated**: the differences of face sums and opposite-edge sums are given as
explicit numbers (to be supplied by `omega`). -/
lemma tetKL_eval (q : kˣ) {a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ}
    (h1 : (a + b + i) / 2 = F₁) (h2 : (i + c + D) / 2 = F₂) (h3 : (b + c + j) / 2 = F₃) (h4 : (a + j + D) / 2 = F₄)
    (g1 : (b + D + i + j) / 2 = B₁) (g2 : (a + c + i + j) / 2 = B₂) (g3 : (a + b + c + D) / 2 = B₃)
    (hmax : max (max F₁ F₂) (max F₃ F₄) = z) (hmin : min B₁ (min B₂ B₃) = z)
    {x₁₁ x₁₂ x₁₃ x₁₄ x₂₁ x₂₂ x₂₃ x₂₄ x₃₁ x₃₂ x₃₃ x₃₄ y₁ y₂ y₃ y₄ w₁ w₂ w₃ : ℕ}
    (k11 : B₁ - F₁ = x₁₁) (k12 : B₁ - F₂ = x₁₂) (k13 : B₁ - F₃ = x₁₃) (k14 : B₁ - F₄ = x₁₄)
    (k21 : B₂ - F₁ = x₂₁) (k22 : B₂ - F₂ = x₂₂) (k23 : B₂ - F₃ = x₂₃) (k24 : B₂ - F₄ = x₂₄)
    (k31 : B₃ - F₁ = x₃₁) (k32 : B₃ - F₂ = x₃₂) (k33 : B₃ - F₃ = x₃₃) (k34 : B₃ - F₄ = x₃₄)
    (l1 : z - F₁ = y₁) (l2 : z - F₂ = y₂) (l3 : z - F₃ = y₃) (l4 : z - F₄ = y₄)
    (m1 : B₁ - z = w₁) (m2 : B₂ - z = w₂) (m3 : B₃ - z = w₃) :
    tetKL q a b c D i j =
      (qfac q x₁₁ * qfac q x₁₂ * qfac q x₁₃ * qfac q x₁₄) * (qfac q x₂₁ * qfac q x₂₂ * qfac q x₂₃ * qfac q x₂₄) *
          (qfac q x₃₁ * qfac q x₃₂ * qfac q x₃₃ * qfac q x₃₄) /
        (qfac q a * qfac q b * qfac q c * qfac q D * qfac q i * qfac q j) *
      ((-1) ^ z * qfac q (z + 1) /
        (qfac q y₁ * qfac q y₂ * qfac q y₃ * qfac q y₄ * (qfac q w₁ * qfac q w₂ * qfac q w₃))) := by
  rw [tetKL_eq_single q h1 h2 h3 h4 g1 g2 g3 hmax hmin]
  unfold tetPre tetTerm
  rw [k11, k12, k13, k14, k21, k22, k23, k24, k31, k32, k33, k34, l1, l2, l3, l4, m1, m2, m3]

/-- **A theta net, evaluated**: `θ(a, b, c)` with the half-perimeter and its differences given as explicit numbers. -/
lemma thetaKL_eval (q : kˣ) {a b c s u v w : ℕ} (hs : (a + b + c) / 2 = s) (hu : s - c = u) (hv : s - a = v)
    (hw : s - b = w) :
    thetaKL q a b c = (-1) ^ s * qfac q (s + 1) * qfac q u * qfac q v * qfac q w / (qfac q a * qfac q b * qfac q c) := by
  unfold thetaKL
  rw [hs, hu, hv, hw]

/-- `[0]! = 1`. -/
lemma qfac_zero (q : kˣ) : qfac q 0 = 1 := rfl

/-- `[1]! = 1` when it does not vanish (so that `q ≠ q⁻¹`). -/
lemma qfac_one_eq (q : kˣ) (h : qfac q 1 ≠ 0) : qfac q 1 = 1 := by
  have h1 : qfac q 1 = qb q 1 := by simp [qfac]
  rw [h1] at h ⊢
  unfold qb at h ⊢
  have hd : (q : k) - (q : k)⁻¹ ≠ 0 := by
    intro hd; apply h; rw [pow_one, pow_one, hd, div_zero]
  rw [pow_one, pow_one, div_self hd]

/-- The single term of `klCoef q a b 1 e 1 1 e` (both channels lowered). -/
theorem klCoef_one_11' (q : kˣ) {a b e : ℕ} (h : KLAdm a b 1 e 1 1 e)
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) : klCoef q a b 1 e 1 1 e = 1 := by
  have hadm := h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  simp only [le_min_iff] at h1 h2 h3 h4
  unfold klCoef
  rw [ite_eq_left_iff.mpr (fun hn => absurd hadm hn)]
  rw [tetKL_eq_single q (F₁ := a + b - e) (F₂ := a + b - 2 * e) (F₃ := b) (F₄ := a + b - e - 1)
    (B₁ := a + 2 * b - 2 * e - 1) (B₂ := a + b - e) (B₃ := a + b - e) (z := a + b - e)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨a', rfl⟩ : ∃ a', a = e + a' := ⟨a - e, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = e + 1 + b' := ⟨b - e - 1, by omega⟩
  unfold tetPre tetTerm thetaKL deltaKL
  simp only [show e + a' + (e + 1 + b') - 2 * e = a' + b' + 1 by omega,
    show a' + b' + 1 + 1 - 2 * 1 = a' + b' by omega, show e + 1 + b' + 1 - 2 * 1 = e + b' by omega,
    show e + a' + (e + 1 + b') - e = e + a' + b' + 1 by omega,
    show e + a' + 2 * (e + 1 + b') - 2 * e - 1 = e + a' + 2 * b' + 1 by omega]
  simp only [show e + a' + 2 * b' + 1 - (e + a' + b' + 1) = b' by omega,
    show e + a' + 2 * b' + 1 - (a' + b' + 1) = e + b' by omega,
    show e + a' + 2 * b' + 1 - (e + 1 + b') = a' + b' by omega,
    show e + a' + 2 * b' + 1 - (e + a' + b' + 1 - 1) = b' + 1 by omega,
    show e + a' + b' + 1 - (e + a' + b' + 1) = 0 by omega,
    show e + a' + b' + 1 - (a' + b' + 1) = e by omega,
    show e + a' + b' + 1 - (e + 1 + b') = a' by omega,
    show e + a' + b' + 1 - (e + a' + b' + 1 - 1) = 1 by omega,
    show (e + a' + (e + 1 + b') + (a' + b' + 1)) / 2 = e + a' + b' + 1 by omega,
    show e + a' + b' + 1 - (e + a') = b' + 1 by omega,
    show (a' + b' + 1 + 1 + (a' + b')) / 2 = a' + b' + 1 by omega,
    show a' + b' + 1 - (a' + b') = 1 by omega, show a' + b' + 1 - 1 = a' + b' by omega, Nat.sub_self]
  have hq1 : qfac q 1 = 1 := qfac_one_eq q (hnz 1 (by omega))
  have e1 : qfac q (a' + b' + 1 + 1) = qfac q (a' + b' + 1) * qb q (a' + b' + 1 + 1) := rfl
  have e2 : qfac q (a' + b' + 1) = qfac q (a' + b') * qb q (a' + b' + 1) := rfl
  have n1 := hnz (e + a') (by omega); have n2 := hnz (e + 1 + b') (by omega); have n3 := hnz (a' + b') (by omega)
  have n4 := hnz (e + b') (by omega); have n5 := hnz e (by omega); have n6 := hnz a' (by omega)
  have n7 := hnz b' (by omega); have n8 := hnz (b' + 1) (by omega); have n9 := hnz (e + a' + b' + 1 + 1) (by omega)
  have n10 := hnz (a' + b' + 1 + 1) (by omega)
  have m1 : qb q (a' + b' + 1) ≠ 0 := fun h0 => (hnz (a' + b' + 1) (by omega)) (by rw [e2, h0, mul_zero])
  have m2 : qb q (a' + b' + 1 + 1) ≠ 0 := fun h0 => n10 (by rw [e1, h0, mul_zero])
  rw [e1, e2]
  simp only [qfac_zero, hq1, one_mul, mul_one]
  rw [show (-1 : k) ^ (e + a' + b' + 1) = (-1) ^ (e + a' + b' + 1) from rfl]
  field_simp


/-- The single term of `klCoef q a b 1 e 1 0 (e+1)` (channel lowered, second bracketing raised): `[e+1]/[b+1]`. -/
theorem klCoef_one_10' (q : kˣ) {a b e : ℕ} (h : KLAdm a b 1 e 1 0 (e + 1))
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) : klCoef q a b 1 e 1 0 (e + 1) = qb q (e + 1) / qb q (b + 1) := by
  have hadm := h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  simp only [le_min_iff] at h1 h2 h3 h4
  unfold klCoef
  rw [ite_eq_left_iff.mpr (fun hn => absurd hadm hn)]
  obtain ⟨a', rfl⟩ : ∃ a', a = e + 1 + a' := ⟨a - e - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = e + b' := ⟨b - e, by omega⟩
  rw [show e + 1 + a' + (e + b') - 2 * e = a' + b' + 1 by omega, show a' + b' + 1 + 1 - 2 * 1 = a' + b' by omega,
    show e + b' + 1 - 2 * 0 = e + b' + 1 by omega]
  rw [tetKL_eval q (F₁ := e + a' + b' + 1) (F₂ := a' + b' + 1) (F₃ := e + b' + 1) (F₄ := e + a' + b' + 1)
    (B₁ := e + a' + 2 * b' + 1) (B₂ := e + a' + b' + 2) (B₃ := e + a' + b' + 1) (z := e + a' + b' + 1)
    (x₁₁ := b') (x₁₂ := e + b') (x₁₃ := a' + b') (x₁₄ := b') (x₂₁ := 1) (x₂₂ := e + 1) (x₂₃ := a' + 1) (x₂₄ := 1)
    (x₃₁ := 0) (x₃₂ := e) (x₃₃ := a') (x₃₄ := 0) (y₁ := 0) (y₂ := e) (y₃ := a') (y₄ := 0) (w₁ := b') (w₂ := 1) (w₃ := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := e + a' + b' + 1) (u := e) (v := b') (w := a' + 1) (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := a' + b' + 1) (u := 1) (v := 0) (w := a' + b') (by omega) (by omega) (by omega) (by omega)]
  unfold deltaKL
  have hq1 : qfac q 1 = 1 := qfac_one_eq q (hnz 1 (by omega))
  have r1 : qfac q (e + 1) = qfac q e * qb q (e + 1) := rfl
  have r2 : qfac q (a' + 1) = qfac q a' * qb q (a' + 1) := rfl
  have r3 : qfac q (e + b' + 1) = qfac q (e + b') * qb q (e + b' + 1) := rfl
  have r4 : qfac q (a' + b' + 1) = qfac q (a' + b') * qb q (a' + b' + 1) := rfl
  have r5 : qfac q (a' + b' + 1 + 1) = qfac q (a' + b' + 1) * qb q (a' + b' + 1 + 1) := rfl
  have n1 := hnz e (by omega); have n2 := hnz a' (by omega); have n3 := hnz b' (by omega)
  have n4 := hnz (e + b') (by omega); have n5 := hnz (a' + b') (by omega); have n6 := hnz (e + 1 + a') (by omega)
  have n7 := hnz (e + a' + b' + 1 + 1) (by omega)
  have p1 : qb q (e + 1) ≠ 0 := fun h0 => hnz (e + 1) (by omega) (by rw [r1, h0, mul_zero])
  have p2 : qb q (a' + 1) ≠ 0 := fun h0 => hnz (a' + 1) (by omega) (by rw [r2, h0, mul_zero])
  have p3 : qb q (e + b' + 1) ≠ 0 := fun h0 => hnz (e + b' + 1) (by omega) (by rw [r3, h0, mul_zero])
  have p4 : qb q (a' + b' + 1) ≠ 0 := fun h0 => hnz (a' + b' + 1) (by omega) (by rw [r4, h0, mul_zero])
  have p5 : qb q (a' + b' + 1 + 1) ≠ 0 := fun h0 => hnz (a' + b' + 1 + 1) (by omega) (by rw [r5, h0, mul_zero])
  rw [r1, r2, r3, r5, r4]
  simp only [qfac_zero, hq1, one_mul, mul_one]
  field_simp

/-- The single term of `klCoef q a b 1 (e+1) 0 1 e` (channel raised, second bracketing lowered): `-[a-e]/[a+b-2e]`. -/
theorem klCoef_one_01' (q : kˣ) {a b e : ℕ} (h : KLAdm a b 1 (e + 1) 0 1 e)
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) :
    klCoef q a b 1 (e + 1) 0 1 e = -(qb q (a - e) / qb q (a + b - 2 * e)) := by
  have hadm := h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  simp only [le_min_iff] at h1 h2 h3 h4
  unfold klCoef
  rw [ite_eq_left_iff.mpr (fun hn => absurd hadm hn)]
  obtain ⟨a', rfl⟩ : ∃ a', a = e + 1 + a' := ⟨a - e - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = e + 1 + b' := ⟨b - e - 1, by omega⟩
  rw [show e + 1 + a' + (e + 1 + b') - 2 * (e + 1) = a' + b' by omega, show a' + b' + 1 - 2 * 0 = a' + b' + 1 by omega,
    show e + 1 + b' + 1 - 2 * 1 = e + b' by omega, show e + 1 + a' - e = a' + 1 by omega,
    show e + 1 + a' + (e + 1 + b') - 2 * e = a' + b' + 1 + 1 by omega]
  rw [tetKL_eval q (F₁ := e + a' + b' + 1) (F₂ := a' + b' + 1) (F₃ := e + b' + 1) (F₄ := e + a' + b' + 1)
    (B₁ := e + a' + 2 * b' + 1) (B₂ := e + a' + b' + 1) (B₃ := e + a' + b' + 2) (z := e + a' + b' + 1)
    (x₁₁ := b') (x₁₂ := e + b') (x₁₃ := a' + b') (x₁₄ := b') (x₂₁ := 0) (x₂₂ := e) (x₂₃ := a') (x₂₄ := 0)
    (x₃₁ := 1) (x₃₂ := e + 1) (x₃₃ := a' + 1) (x₃₄ := 1) (y₁ := 0) (y₂ := e) (y₃ := a') (y₄ := 0) (w₁ := b') (w₂ := 0) (w₃ := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := e + a' + b' + 1) (u := e + 1) (v := b') (w := a') (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := a' + b' + 1) (u := 0) (v := 1) (w := a' + b') (by omega) (by omega) (by omega) (by omega)]
  unfold deltaKL
  have hq1 : qfac q 1 = 1 := qfac_one_eq q (hnz 1 (by omega))
  have r1 : qfac q (e + 1) = qfac q e * qb q (e + 1) := rfl
  have r2 : qfac q (a' + 1) = qfac q a' * qb q (a' + 1) := rfl
  have r3 : qfac q (e + 1 + b') = qfac q (e + b') * qb q (e + b' + 1) := by
    rw [show e + 1 + b' = e + b' + 1 by omega]; rfl
  have r4 : qfac q (a' + b' + 1) = qfac q (a' + b') * qb q (a' + b' + 1) := rfl
  have r5 : qfac q (a' + b' + 1 + 1) = qfac q (a' + b' + 1) * qb q (a' + b' + 1 + 1) := rfl
  have n1 := hnz e (by omega); have n2 := hnz a' (by omega); have n3 := hnz b' (by omega)
  have n4 := hnz (e + b') (by omega); have n5 := hnz (a' + b') (by omega); have n6 := hnz (e + 1 + a') (by omega)
  have n7 := hnz (e + a' + b' + 1 + 1) (by omega)
  have p1 : qb q (e + 1) ≠ 0 := fun h0 => hnz (e + 1) (by omega) (by rw [r1, h0, mul_zero])
  have p2 : qb q (a' + 1) ≠ 0 := fun h0 => hnz (a' + 1) (by omega) (by rw [r2, h0, mul_zero])
  have p3 : qb q (e + b' + 1) ≠ 0 := fun h0 => hnz (e + 1 + b') (by omega) (by rw [r3, h0, mul_zero])
  have p4 : qb q (a' + b' + 1) ≠ 0 := fun h0 => hnz (a' + b' + 1) (by omega) (by rw [r4, h0, mul_zero])
  have p5 : qb q (a' + b' + 1 + 1) ≠ 0 := fun h0 => hnz (a' + b' + 1 + 1) (by omega) (by rw [r5, h0, mul_zero])
  simp only [r1, r2, r3, r5, r4]
  simp only [qfac_zero, hq1, one_mul, mul_one]
  field_simp
  ring

/-- The single term of `klCoef q a b 1 e 0 0 e` (both channels raised):
`[a+b-e+2][b-e+1] / ([b+1][a+b-2e+2])`. -/
theorem klCoef_one_00' (q : kˣ) {a b e : ℕ} (h : KLAdm a b 1 e 0 0 e)
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) :
    klCoef q a b 1 e 0 0 e = qb q (a + b - e + 2) * qb q (b - e + 1) / (qb q (b + 1) * qb q (a + b - 2 * e + 2)) := by
  have hadm := h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  simp only [le_min_iff] at h1 h2 h3 h4
  unfold klCoef
  rw [ite_eq_left_iff.mpr (fun hn => absurd hadm hn)]
  obtain ⟨a', rfl⟩ : ∃ a', a = e + a' := ⟨a - e, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = e + b' := ⟨b - e, by omega⟩
  rw [show e + a' + (e + b') - 2 * e = a' + b' by omega, show a' + b' + 1 - 2 * 0 = a' + b' + 1 by omega,
    show e + b' + 1 - 2 * 0 = e + b' + 1 by omega, show e + a' + (e + b') - e + 2 = e + a' + b' + 1 + 1 by omega,
    show e + b' - e + 1 = b' + 1 by omega, show a' + b' + 2 = a' + b' + 1 + 1 by omega]
  rw [tetKL_eval q (F₁ := e + a' + b') (F₂ := a' + b' + 1) (F₃ := e + b' + 1) (F₄ := e + a' + b' + 1)
    (B₁ := e + a' + 2 * b' + 1) (B₂ := e + a' + b' + 1) (B₃ := e + a' + b' + 1) (z := e + a' + b' + 1)
    (x₁₁ := b' + 1) (x₁₂ := e + b') (x₁₃ := a' + b') (x₁₄ := b') (x₂₁ := 1) (x₂₂ := e) (x₂₃ := a') (x₂₄ := 0)
    (x₃₁ := 1) (x₃₂ := e) (x₃₃ := a') (x₃₄ := 0) (y₁ := 1) (y₂ := e) (y₃ := a') (y₄ := 0) (w₁ := b') (w₂ := 0) (w₃ := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := e + a' + b') (u := e) (v := b') (w := a') (by omega) (by omega) (by omega) (by omega),
    thetaKL_eval q (s := a' + b' + 1) (u := 0) (v := 1) (w := a' + b') (by omega) (by omega) (by omega) (by omega)]
  unfold deltaKL
  have hq1 : qfac q 1 = 1 := qfac_one_eq q (hnz 1 (by omega))
  have r2 : qfac q (b' + 1) = qfac q b' * qb q (b' + 1) := rfl
  have r3 : qfac q (e + b' + 1) = qfac q (e + b') * qb q (e + b' + 1) := rfl
  have r4 : qfac q (a' + b' + 1) = qfac q (a' + b') * qb q (a' + b' + 1) := rfl
  have r5 : qfac q (a' + b' + 1 + 1) = qfac q (a' + b' + 1) * qb q (a' + b' + 1 + 1) := rfl
  have r6 : qfac q (e + a' + b' + 1) = qfac q (e + a' + b') * qb q (e + a' + b' + 1) := rfl
  have r7 : qfac q (e + a' + b' + 1 + 1) = qfac q (e + a' + b' + 1) * qb q (e + a' + b' + 1 + 1) := rfl
  have n1 := hnz e (by omega); have n2 := hnz a' (by omega); have n3 := hnz b' (by omega)
  have n4 := hnz (e + b') (by omega); have n5 := hnz (a' + b') (by omega); have n6 := hnz (e + a') (by omega)
  have n7 := hnz (e + a' + b') (by omega)
  have p2 : qb q (b' + 1) ≠ 0 := fun h0 => hnz (b' + 1) (by omega) (by rw [r2, h0, mul_zero])
  have p3 : qb q (e + b' + 1) ≠ 0 := fun h0 => hnz (e + b' + 1) (by omega) (by rw [r3, h0, mul_zero])
  have p4 : qb q (a' + b' + 1) ≠ 0 := fun h0 => hnz (a' + b' + 1) (by omega) (by rw [r4, h0, mul_zero])
  have p6 : qb q (e + a' + b' + 1) ≠ 0 := fun h0 => hnz (e + a' + b' + 1) (by omega) (by rw [r6, h0, mul_zero])
  have p7 : qb q (e + a' + b' + 1 + 1) ≠ 0 := fun h0 => hnz (e + a' + b' + 1 + 1) (by omega)
    (by rw [r7, h0, mul_zero])
  have p8 : qb q (a' + b' + 1 + 1) ≠ 0 := by
    intro h0
    have : qfac q (a' + b' + 1 + 1) = 0 := by
      show qfac q (a' + b' + 1) * qb q (a' + b' + 1 + 1) = 0
      rw [h0, mul_zero]
    exact hnz (a' + b' + 1 + 1) (by omega) this
  simp only [r7, r6, r3, r2, r5, r4]
  simp only [qfac_zero, hq1, one_mul, mul_one]
  field_simp
  ring


/-! ## The four entries in the indexing of `Fc` (`E ≥ 1`) -/

/-- **`F00`**: `klCoef q a b 1 E 0 0 E = [a+b-E+2][b-E+1] / ([b+1][a+b-2E+2])`. -/
theorem klCoef_one_00 (q : kˣ) {a b E : ℕ} (h : KLAdm a b 1 E 0 0 E) (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) :
    klCoef q a b 1 E 0 0 E = qb q (a + b - E + 2) * qb q (b - E + 1) / (qb q (b + 1) * qb q (a + b - 2 * E + 2)) :=
  klCoef_one_00' q h hnz

/-- **`F01`**: `klCoef q a b 1 E 0 1 (E-1) = -[a-E+1] / [a+b-2E+2]`. -/
theorem klCoef_one_01 (q : kˣ) {a b E : ℕ} (hE : 1 ≤ E) (h : KLAdm a b 1 E 0 1 (E - 1))
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) :
    klCoef q a b 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + b - 2 * E + 2)) := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  have hEa : e + 1 ≤ a := h.1.trans (min_le_left _ _)
  have hEb : e + 1 ≤ b := h.1.trans (min_le_right _ _)
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [klCoef_one_01' q h hnz, show a - (e + 1) + 1 = a - e by omega,
    show a + b - 2 * (e + 1) + 2 = a + b - 2 * e by omega]

/-- **`F10`**: `klCoef q a b 1 (E-1) 1 0 E = [E] / [b+1]`. -/
theorem klCoef_one_10 (q : kˣ) {a b E : ℕ} (hE : 1 ≤ E) (h : KLAdm a b 1 (E - 1) 1 0 E)
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) : klCoef q a b 1 (E - 1) 1 0 E = qb q E / qb q (b + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  exact klCoef_one_10' q h hnz

/-- **`F11`**: `klCoef q a b 1 (E-1) 1 1 (E-1) = 1`. -/
theorem klCoef_one_11 (q : kˣ) {a b E : ℕ} (h : KLAdm a b 1 (E - 1) 1 1 (E - 1))
    (hnz : ∀ n, n ≤ a + b + 2 → qfac q n ≠ 0) : klCoef q a b 1 (E - 1) 1 1 (E - 1) = 1 :=
  klCoef_one_11' q h hnz

end Lightlike.TemperleyLieb
