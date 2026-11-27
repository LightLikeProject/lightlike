import Mathlib
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TemperleyLieb.KLCertificate

/-!
# Zero-extended tetrahedral summands and the telescoping of the third-block recursion

The summand `tetTerm` of the tetrahedral net is a ratio of q-factorials of `z - F_k` and `B_l - z`; outside its range
the truncated subtraction of `ℕ` gives it junk values. This file works instead with reciprocal q-factorials of integers,
`rqf q n = 1/[n]!` for `n ≥ 0` and `0` for `n < 0`, which satisfy `rqf q (n - 1) = [n] rqf q n` for every integer
`n` (`rqf_pred`), and with the zero-extended summand `tetHat` built from them (`tetHat_eq_tetTerm` on the range,
`tetHat_eq_zero` off it), so that a tetrahedral sum is a sum of `tetHat` over any `range N` past its range
(`sum_tetTerm_eq_sum_tetHat`).

With the q-number identities of `KLCertificate`, the three tetrahedral summands of each case of the third-block
recursion combine termwise into a difference `G (z + 1) - G z` (`tel_lower_term` for a fourth block meeting the total
channel, `tel_upper_term` for one not meeting it), and the sums telescope to zero (`tel_lower_sum`, `tel_upper_sum`).
Numerical evidence (not proof): the coefficient ratios used here were checked against the tetrahedral sums of
`klCoef` in exact arithmetic at `q = 3/2` on all instances with `a, b, c ≤ 4`.
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- The reciprocal q-factorial of an integer: `1/[n]!` for `n ≥ 0` and `0` for `n < 0`. -/
noncomputable def rqf (q : kˣ) (n : ℤ) : k := if n < 0 then 0 else (qfac q n.toNat)⁻¹

/-- `rqf` of a natural number. -/
lemma rqf_natCast (q : kˣ) (n : ℕ) : rqf q n = (qfac q n)⁻¹ := by
  unfold rqf
  simp

/-- `rqf` vanishes at negative arguments. -/
lemma rqf_of_neg (q : kˣ) {n : ℤ} (hn : n < 0) : rqf q n = 0 := by
  unfold rqf
  simp [hn]

/-- **The shift of the reciprocal q-factorial**: `rqf q (n - 1) = [n] rqf q n` for every integer `n`, when `[n] ≠ 0`
for `n ≥ 1`. -/
lemma rqf_pred (q : kˣ) (n : ℤ) (hn : 1 ≤ n → qz q n ≠ 0) : rqf q (n - 1) = qz q n * rqf q n := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [rqf_of_neg q (by omega), rqf_of_neg q h, mul_zero]
  · subst h
    rw [rqf_of_neg q (by norm_num)]
    simp [qz]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨n.toNat - 1, by omega⟩
    rw [show (m : ℤ) + 1 - 1 = (m : ℤ) by ring, show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      rqf_natCast, rqf_natCast, ← qb_eq_qz]
    have h1 : qb q (m + 1) ≠ 0 := by
      rw [qb_eq_qz]; exact hn (by omega)
    show (qfac q m)⁻¹ = qb q (m + 1) * (qfac q m * qb q (m + 1))⁻¹
    by_cases h0 : qfac q m = 0
    · simp [h0]
    · field_simp


/-- **The zero-extended summand of a tetrahedral net** with integer face sums `F_k` and opposite-edge sums `B_l`. -/
noncomputable def tetHat (q : kˣ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℤ) (z : ℕ) : k :=
  (-1) ^ z * qfac q (z + 1) * (rqf q (z - F₁) * rqf q (z - F₂) * rqf q (z - F₃) * rqf q (z - F₄)) *
    (rqf q (B₁ - z) * rqf q (B₂ - z) * rqf q (B₃ - z))

/-- On its range the zero-extended summand is `tetTerm`. -/
lemma tetHat_eq_tetTerm (q : kˣ) {F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ} (h1 : F₁ ≤ z) (h2 : F₂ ≤ z) (h3 : F₃ ≤ z)
    (h4 : F₄ ≤ z) (g1 : z ≤ B₁) (g2 : z ≤ B₂) (g3 : z ≤ B₃) :
    tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z = tetTerm q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  unfold tetHat tetTerm
  rw [show (z : ℤ) - F₁ = ((z - F₁ : ℕ) : ℤ) by omega, show (z : ℤ) - F₂ = ((z - F₂ : ℕ) : ℤ) by omega,
    show (z : ℤ) - F₃ = ((z - F₃ : ℕ) : ℤ) by omega, show (z : ℤ) - F₄ = ((z - F₄ : ℕ) : ℤ) by omega,
    show (B₁ : ℤ) - z = ((B₁ - z : ℕ) : ℤ) by omega, show (B₂ : ℤ) - z = ((B₂ - z : ℕ) : ℤ) by omega,
    show (B₃ : ℤ) - z = ((B₃ - z : ℕ) : ℤ) by omega]
  simp only [rqf_natCast, div_eq_mul_inv, mul_inv]
  ring

/-- Off its range the zero-extended summand vanishes. -/
lemma tetHat_eq_zero (q : kˣ) {F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℤ} {z : ℕ}
    (h : (z : ℤ) < F₁ ∨ (z : ℤ) < F₂ ∨ (z : ℤ) < F₃ ∨ (z : ℤ) < F₄ ∨ B₁ < z ∨ B₂ < z ∨ B₃ < z) :
    tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z = 0 := by
  unfold tetHat
  rcases h with h | h | h | h | h | h | h
  · rw [rqf_of_neg q (by omega)]; ring
  · rw [rqf_of_neg q (show (z : ℤ) - F₂ < 0 by omega)]; ring
  · rw [rqf_of_neg q (show (z : ℤ) - F₃ < 0 by omega)]; ring
  · rw [rqf_of_neg q (show (z : ℤ) - F₄ < 0 by omega)]; ring
  · rw [rqf_of_neg q (show B₁ - (z : ℤ) < 0 by omega)]; ring
  · rw [rqf_of_neg q (show B₂ - (z : ℤ) < 0 by omega)]; ring
  · rw [rqf_of_neg q (show B₃ - (z : ℤ) < 0 by omega)]; ring

/-- **A tetrahedral sum as a sum of the zero-extended summand** over `range N`, for any `N` past the range. -/
lemma sum_tetTerm_eq_sum_tetHat (q : kˣ) {F₁ F₂ F₃ F₄ B₁ B₂ B₃ N : ℕ} (hN : min B₁ (min B₂ B₃) < N) :
    ∑ z ∈ Icc (max (max F₁ F₂) (max F₃ F₄)) (min B₁ (min B₂ B₃)), tetTerm q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z =
      ∑ z ∈ range N, tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  symm
  rw [← sum_subset (s₁ := Icc (max (max F₁ F₂) (max F₃ F₄)) (min B₁ (min B₂ B₃))) (s₂ := range N)]
  · refine sum_congr rfl fun z hz => ?_
    simp only [mem_Icc, max_le_iff, le_min_iff] at hz
    exact tetHat_eq_tetTerm q hz.1.1.1 hz.1.1.2 hz.1.2.1 hz.1.2.2 hz.2.1 hz.2.2.1 hz.2.2.2
  · intro z hz; simp only [mem_Icc, mem_range] at hz ⊢; omega
  · intro z _ hz
    simp only [mem_Icc, max_le_iff, le_min_iff, not_and_or, not_le] at hz
    apply tetHat_eq_zero
    omega


/-- **The termwise certificate for `g₀ = 1`**: with `G(z) = [z-F₁][z-F₂] T₁(z)`,
`[B₂-F₄+1][F₃+F₄-B₃] T_{c+1}(z) - [F₃+1][B₃-F₃+1] T₀(z) - [B₁-F₁][B₁-F₂] T₁(z) = G(z+1) - G(z)` for the zero-extended
summands, where `T₁` has the data `(F, B)`, `T_{c+1}` has `F₄ - 1, B₁ - 1`, and `T₀` has `F₃ - 1, F₄ - 1, B₁ - 1, B₂ - 1`
(`B₃ = F₁ + F₂ + F₃ + F₄ - B₁ - B₂`). -/
theorem tel_lower_term (q : kˣ) (hq : (q : k) - (q : k)⁻¹ ≠ 0) {M : ℤ} (hnz : ∀ n : ℤ, 1 ≤ n → n ≤ M → qz q n ≠ 0)
    (z : ℕ) (F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) (hF : 0 ≤ F₁ ∧ 0 ≤ F₂ ∧ 0 ≤ F₃ ∧ 0 ≤ F₄)
    (hM : (z : ℤ) + 2 ≤ M ∧ B₁ ≤ M ∧ B₂ ≤ M ∧ F₁ + F₂ + F₃ + F₄ - B₁ - B₂ ≤ M) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    let G : ℕ → k := fun w => qz q (w - F₁) * qz q (w - F₂) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ w
    qz q (B₂ - F₄ + 1) * qz q (F₃ + F₄ - B₃) * tetHat q F₁ F₂ F₃ (F₄ - 1) (B₁ - 1) B₂ B₃ z -
        qz q (F₃ + 1) * qz q (B₃ - F₃ + 1) * tetHat q F₁ F₂ (F₃ - 1) (F₄ - 1) (B₁ - 1) (B₂ - 1) B₃ z -
        qz q (B₁ - F₁) * qz q (B₁ - F₂) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z = G (z + 1) - G z := by
  intro B₃ G
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hz, hB1, hB2, hB3⟩ := hM
  have P : ∀ n : ℤ, n ≤ M → rqf q (n - 1) = qz q n * rqf q n := fun n hn =>
    rqf_pred q n fun h1 => hnz n h1 hn
  have eF : ∀ F : ℤ, 0 ≤ F → rqf q ((z : ℤ) - F) = qz q (z + 1 - F) * rqf q (z + 1 - F) := fun F hF0 => by
    rw [← P _ (by omega)]; congr 1; ring
  have eB : ∀ B : ℤ, B ≤ M → rqf q (B - 1 - z) = qz q (B - z) * rqf q (B - z) := fun B hB0 => by
    rw [← P _ (by omega)]; congr 1; ring
  have eB' : ∀ B : ℤ, B ≤ M → rqf q (B - ((z + 1 : ℕ) : ℤ)) = qz q (B - z) * rqf q (B - z) := fun B hB0 => by
    rw [← P _ (by omega)]; congr 1; push_cast; ring
  have e4 : ∀ F : ℤ, rqf q ((z : ℤ) - (F - 1)) = rqf q (z + 1 - F) := fun F => by congr 1; ring
  have eF1 : ∀ F : ℤ, rqf q (((z + 1 : ℕ) : ℤ) - F) = rqf q (z + 1 - F) := fun F => by rw [Nat.cast_add, Nat.cast_one]
  have eq1 : ∀ F : ℤ, qz q (((z + 1 : ℕ) : ℤ) - F) = qz q (z + 1 - F) := fun F => by rw [Nat.cast_add, Nat.cast_one]
  have hfac : qfac q (z + 1 + 1) = qfac q (z + 1) * qz q (z + 2) := by
    rw [show (z : ℤ) + 2 = ((z + 2 : ℕ) : ℤ) by push_cast; ring, ← qb_eq_qz]; rfl
  have core := kl_cert_lower q hq (z : ℤ) F₁ F₂ F₃ F₄ B₁ B₂
  simp only at core
  simp only [G, tetHat]
  rw [eF F₁ hF1, eF F₂ hF2, eF F₃ hF3, eF F₄ hF4, e4 F₃, e4 F₄, eB B₁ hB1, eB B₂ hB2, eF1, eF1, eF1, eF1,
    eB' B₁ hB1, eB' B₂ hB2, eB' B₃ hB3, eq1, eq1, hfac]
  linear_combination
    ((-1) ^ z * qfac q (z + 1) *
        (rqf q (z + 1 - F₁) * rqf q (z + 1 - F₂) * rqf q (z + 1 - F₃) * rqf q (z + 1 - F₄)) *
        (rqf q (B₁ - z) * rqf q (B₂ - z) * rqf q (B₃ - z)) * qz q (z + 1 - F₁) * qz q (z + 1 - F₂)) * core

/-- **The telescoped recursion for `g₀ = 1`**: summed over `range N` past the range of the summands,
`[B₂-F₄+1][F₃+F₄-B₃] Σ T_{c+1} - [F₃+1][B₃-F₃+1] Σ T₀ - [B₁-F₁][B₁-F₂] Σ T₁ = 0`. -/
theorem tel_lower_sum (q : kˣ) (hq : (q : k) - (q : k)⁻¹ ≠ 0) {M : ℤ} (hnz : ∀ n : ℤ, 1 ≤ n → n ≤ M → qz q n ≠ 0)
    (N : ℕ) (F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) (hF : 0 ≤ F₁ ∧ 0 ≤ F₂ ∧ 0 ≤ F₃ ∧ 0 ≤ F₄)
    (hM : (N : ℤ) + 1 ≤ M ∧ B₁ ≤ M ∧ B₂ ≤ M ∧ F₁ + F₂ + F₃ + F₄ - B₁ - B₂ ≤ M) (hN : B₁ < N) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    ∑ z ∈ range N, (qz q (B₂ - F₄ + 1) * qz q (F₃ + F₄ - B₃) * tetHat q F₁ F₂ F₃ (F₄ - 1) (B₁ - 1) B₂ B₃ z -
        qz q (F₃ + 1) * qz q (B₃ - F₃ + 1) * tetHat q F₁ F₂ (F₃ - 1) (F₄ - 1) (B₁ - 1) (B₂ - 1) B₃ z -
        qz q (B₁ - F₁) * qz q (B₁ - F₂) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z) = 0 := by
  intro B₃
  obtain ⟨hN1, hB1, hB2, hB3⟩ := hM
  set G : ℕ → k := fun w => qz q (w - F₁) * qz q (w - F₂) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ w with hG
  rw [sum_congr rfl fun z hz => tel_lower_term q hq hnz z F₁ F₂ F₃ F₄ B₁ B₂ hF
    ⟨by rw [mem_range] at hz; omega, hB1, hB2, hB3⟩, sum_range_sub (f := G)]
  have hGN : G N = 0 := by
    simp only [hG]
    rw [tetHat_eq_zero q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hN))))), mul_zero]
  have hG0 : G 0 = 0 := by
    simp only [hG]
    by_cases h0 : F₁ = 0
    · rw [h0]; simp [qz]
    · rw [tetHat_eq_zero q (Or.inl (by push_cast; omega)), mul_zero]
  rw [hGN, hG0, sub_zero]

/-- **The termwise certificate for `g₀ = 0`**: with `j₁ = F₃ + F₄ - B₃` and `G(z) = -[z-F₁][F₃+F₄+1-z] T_{c+1}(z)`,
`[B₃-F₁][j₁+1] T_{c+1}(z) + [F₃+1][F₄+1] T₀(z) - [B₁-F₂+1][B₂-F₂+1] T₁(z) = G(z+1) - G(z)`, where `T_{c+1}` has the
data `(F, B)`, `T₀` has `F₂ - 1, F₃ - 1, F₄ - 1, B₁ - 1, B₂ - 1, B₃ - 1`, and `T₁` has `F₂ - 1, B₃ - 1`. -/
theorem tel_upper_term (q : kˣ) (hq : (q : k) - (q : k)⁻¹ ≠ 0) {M : ℤ} (hnz : ∀ n : ℤ, 1 ≤ n → n ≤ M → qz q n ≠ 0)
    (z : ℕ) (F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) (hF : 0 ≤ F₁ ∧ 0 ≤ F₂ ∧ 0 ≤ F₃ ∧ 0 ≤ F₄)
    (hM : (z : ℤ) + 2 ≤ M ∧ B₁ ≤ M ∧ B₂ ≤ M ∧ F₁ + F₂ + F₃ + F₄ - B₁ - B₂ ≤ M) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    let G : ℕ → k := fun w => -(qz q (w - F₁) * qz q (F₃ + F₄ + 1 - w) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ w)
    qz q (B₃ - F₁) * qz q (F₃ + F₄ - B₃ + 1) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z +
        qz q (F₃ + 1) * qz q (F₄ + 1) * tetHat q F₁ (F₂ - 1) (F₃ - 1) (F₄ - 1) (B₁ - 1) (B₂ - 1) (B₃ - 1) z -
        qz q (B₁ - F₂ + 1) * qz q (B₂ - F₂ + 1) * tetHat q F₁ (F₂ - 1) F₃ F₄ B₁ B₂ (B₃ - 1) z = G (z + 1) - G z := by
  intro B₃ G
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hz, hB1, hB2, hB3⟩ := hM
  have P : ∀ n : ℤ, n ≤ M → rqf q (n - 1) = qz q n * rqf q n := fun n hn =>
    rqf_pred q n fun h1 => hnz n h1 hn
  have eF : ∀ F : ℤ, 0 ≤ F → rqf q ((z : ℤ) - F) = qz q (z + 1 - F) * rqf q (z + 1 - F) := fun F hF0 => by
    rw [← P _ (by omega)]; congr 1; ring
  have eB : ∀ B : ℤ, B ≤ M → rqf q (B - 1 - z) = qz q (B - z) * rqf q (B - z) := fun B hB0 => by
    rw [← P _ (by omega)]; congr 1; ring
  have eB' : ∀ B : ℤ, B ≤ M → rqf q (B - ((z + 1 : ℕ) : ℤ)) = qz q (B - z) * rqf q (B - z) := fun B hB0 => by
    rw [← P _ (by omega)]; congr 1; push_cast; ring
  have e4 : ∀ F : ℤ, rqf q ((z : ℤ) - (F - 1)) = rqf q (z + 1 - F) := fun F => by congr 1; ring
  have eF1 : ∀ F : ℤ, rqf q (((z + 1 : ℕ) : ℤ) - F) = rqf q (z + 1 - F) := fun F => by rw [Nat.cast_add, Nat.cast_one]
  have eq1 : ∀ F : ℤ, qz q (((z + 1 : ℕ) : ℤ) - F) = qz q (z + 1 - F) := fun F => by rw [Nat.cast_add, Nat.cast_one]
  have hfac : qfac q (z + 1 + 1) = qfac q (z + 1) * qz q (z + 2) := by
    rw [show (z : ℤ) + 2 = ((z + 2 : ℕ) : ℤ) by push_cast; ring, ← qb_eq_qz]; rfl
  have eq2 : qz q (F₃ + F₄ + 1 - ((z + 1 : ℕ) : ℤ)) = qz q (F₃ + F₄ - z) := by congr 1; push_cast; ring
  have core := kl_cert_upper q hq (z : ℤ) F₁ F₂ F₃ F₄ B₁ B₂
  simp only at core
  simp only [G, tetHat]
  rw [eF F₁ hF1, eF F₂ hF2, eF F₃ hF3, eF F₄ hF4, e4 F₂, e4 F₃, e4 F₄, eB B₁ hB1, eB B₂ hB2, eB B₃ hB3,
    eF1, eF1, eF1, eF1, eB' B₁ hB1, eB' B₂ hB2, eB' B₃ hB3, eq1, eq2, hfac]
  linear_combination
    ((-1) ^ z * qfac q (z + 1) *
        (rqf q (z + 1 - F₁) * rqf q (z + 1 - F₂) * rqf q (z + 1 - F₃) * rqf q (z + 1 - F₄)) *
        (rqf q (B₁ - z) * rqf q (B₂ - z) * rqf q (B₃ - z)) * qz q (z + 1 - F₁)) * core

/-- **The telescoped recursion for `g₀ = 0`**: summed over `range N` past the range of the summands,
`[B₃-F₁][j₁+1] Σ T_{c+1} + [F₃+1][F₄+1] Σ T₀ - [B₁-F₂+1][B₂-F₂+1] Σ T₁ = 0`. -/
theorem tel_upper_sum (q : kˣ) (hq : (q : k) - (q : k)⁻¹ ≠ 0) {M : ℤ} (hnz : ∀ n : ℤ, 1 ≤ n → n ≤ M → qz q n ≠ 0)
    (N : ℕ) (F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) (hF : 0 ≤ F₁ ∧ 0 ≤ F₂ ∧ 0 ≤ F₃ ∧ 0 ≤ F₄)
    (hM : (N : ℤ) + 1 ≤ M ∧ B₁ ≤ M ∧ B₂ ≤ M ∧ F₁ + F₂ + F₃ + F₄ - B₁ - B₂ ≤ M) (hN : B₁ < N) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    ∑ z ∈ range N, (qz q (B₃ - F₁) * qz q (F₃ + F₄ - B₃ + 1) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z +
        qz q (F₃ + 1) * qz q (F₄ + 1) * tetHat q F₁ (F₂ - 1) (F₃ - 1) (F₄ - 1) (B₁ - 1) (B₂ - 1) (B₃ - 1) z -
        qz q (B₁ - F₂ + 1) * qz q (B₂ - F₂ + 1) * tetHat q F₁ (F₂ - 1) F₃ F₄ B₁ B₂ (B₃ - 1) z) = 0 := by
  intro B₃
  obtain ⟨hN1, hB1, hB2, hB3⟩ := hM
  set G : ℕ → k := fun w => -(qz q (w - F₁) * qz q (F₃ + F₄ + 1 - w) * tetHat q F₁ F₂ F₃ F₄ B₁ B₂ B₃ w)
    with hG
  rw [sum_congr rfl fun z hz => tel_upper_term q hq hnz z F₁ F₂ F₃ F₄ B₁ B₂ hF
    ⟨by rw [mem_range] at hz; omega, hB1, hB2, hB3⟩, sum_range_sub (f := G)]
  have hGN : G N = 0 := by
    simp only [hG]
    rw [tetHat_eq_zero q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hN))))), mul_zero, neg_zero]
  have hG0 : G 0 = 0 := by
    simp only [hG]
    by_cases h0 : F₁ = 0
    · rw [h0]; simp [qz]
    · rw [tetHat_eq_zero q (Or.inl (by push_cast; omega)), mul_zero, neg_zero]
  rw [hGN, hG0, sub_zero]

end Lightlike.TemperleyLieb
