import Mathlib
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TemperleyLieb.TopEntry

/-!
# Base values of the Kauffman–Lins coefficient

With an empty third block the tetrahedral net is a theta net, `tetKL q a b 0 i i b = θ(a, b, i)`
(`tetKL_zero_third`: its sum has the single term `z = (a+b+i)/2`), and `θ(i, 0, i) = Δ_i`
(`thetaKL_zero_mid`), so the Kauffman–Lins coefficient is the identity matrix (`klCoef_zero_third`), as `Fc` is
(`Fc_zero_third`). This is the base `c = 0` of the identification `Fc = klCoef`.
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- `θ(i, 0, i) = Δ_i`. -/
lemma thetaKL_zero_mid (q : kˣ) (i : ℕ) (hi : qfac q i ≠ 0) : thetaKL q i 0 i = deltaKL q i := by
  unfold thetaKL deltaKL
  rw [show (i + 0 + i) / 2 = i by omega, Nat.sub_self, Nat.sub_zero, show qfac q (i + 1) = qfac q i * qb q (i + 1) from rfl]
  simp only [qfac]
  field_simp

/-- With an empty third block the tetrahedral net is the theta net: `tetKL q a b 0 i i b = θ(a, b, i)`. -/
lemma tetKL_zero_third (q : kˣ) {a b e i : ℕ} (hea : e ≤ a) (heb : e ≤ b) (hi : i = a + b - 2 * e)
    (hnz : ∀ n, n ≤ a + b → qfac q n ≠ 0) : tetKL q a b 0 i i b = thetaKL q a b i := by
  have hs : (a + b + i) / 2 = a + b - e := by omega
  have h2 : (i + 0 + i) / 2 = i := by omega
  have h3 : (b + 0 + b) / 2 = b := by omega
  have h5 : (b + i + i + b) / 2 = b + i := by omega
  have h6 : (a + 0 + i + b) / 2 = a + b - e := by omega
  have h7 : (a + b + 0 + i) / 2 = a + b - e := by omega
  have hmax : max (max (a + b - e) i) (max b (a + b - e)) = a + b - e := by omega
  have hmin : min (b + i) (min (a + b - e) (a + b - e)) = a + b - e := by omega
  unfold tetKL tetPre tetTerm thetaKL
  simp only [hs, h2, h3, h5, h6, h7, hmax, hmin, Icc_self, sum_singleton, Nat.sub_self]
  rw [show a + b - e - i = e by omega, show a + b - e - b = a - e by omega, show b + i - (a + b - e) = b - e by omega,
    show b + i - i = b by omega, show b + i - b = i by omega, show a + b - e - a = b - e by omega]
  have := hnz a (by omega); have := hnz b (by omega); have := hnz i (by omega); have := hnz e (by omega)
  have := hnz (a - e) (by omega); have := hnz (b - e) (by omega)
  simp only [qfac]
  field_simp

/-- **The Kauffman–Lins coefficient with an empty third block** is the identity matrix. -/
theorem klCoef_zero_third (q : kˣ) {a b e d' : ℕ} (he : e ≤ min a b) (hnz : ∀ n, n ≤ a + b + 1 → qfac q n ≠ 0)
    (hθ : thetaKL q a b (a + b - 2 * e) ≠ 0) :
    klCoef q a b 0 e 0 0 d' = if d' = e then 1 else 0 := by
  have hea : e ≤ a := he.trans (min_le_left _ _)
  have heb : e ≤ b := he.trans (min_le_right _ _)
  unfold klCoef
  by_cases h : d' = e
  · subst h
    have hadm : KLAdm a b 0 d' 0 0 d' := ⟨he, by simp, by simp, le_min hea (by omega), by omega⟩
    rw [if_pos hadm, if_pos rfl]
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
    rw [tetKL_zero_third q hea heb rfl (fun n hn => hnz n (by omega)),
      thetaKL_zero_mid q _ (hnz _ (by omega))]
    have hΔ : deltaKL q (a + b - 2 * d') ≠ 0 := by
      unfold deltaKL
      have h1 := hnz (a + b - 2 * d' + 1) (by omega)
      have h0 := hnz (a + b - 2 * d') (by omega)
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      intro hq; apply h1; simp only [qfac, hq, mul_zero]
    field_simp
  · rw [if_neg h, ite_eq_right_iff]
    rintro ⟨-, -, -, hd4, ht⟩
    exact absurd (by simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at hd4 ht; omega) h

/-- The quantum factorials up to `N` do not vanish when `q^{2j} ≠ 1` for `1 ≤ j ≤ N`. -/
lemma qfac_ne_of_pow (q : kˣ) {N : ℕ} (hN : 1 ≤ N) (hq2 : ∀ j, 1 ≤ j → j ≤ N → (q : k) ^ (2 * j) ≠ 1) :
    ∀ n, n ≤ N → qfac q n ≠ 0 := by
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl hN
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  exact qfac_ne q N fun j h1 h2 => qb_ne q hD j (hq2 j h1 h2)

lemma thetaKL_ne (q : kˣ) {a b c : ℕ} (hnz : ∀ n, n ≤ a + b + c + 1 → qfac q n ≠ 0) :
    thetaKL q a b c ≠ 0 := by
  unfold thetaKL
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega)))
    (mul_ne_zero (mul_ne_zero (hnz _ (by omega)) (hnz _ (by omega))) (hnz _ (by omega)))

/-- **`Fc = klCoef` with an empty third block** (the base `c = 0` of the identification). -/
theorem Fc_eq_klCoef_zero_third (q : kˣ) (hδ : loopVal q ≠ 0) {a b e d' : ℕ} (he : e ≤ min a b)
    (hd' : d' ≤ min a b) (hN : 1 ≤ a + b) (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ 2 * (a + b) + 2 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 0 e 0 0 d' = klCoef q a b 0 e 0 0 d' := by
  have hnz := qfac_ne_of_pow q (N := 2 * (a + b) + 2) (by omega) hq2
  rw [Fc_zero_third q hδ a b e d' he hd' hN hd (fun j h1 h2 => hq2 j h1 (by omega)),
    klCoef_zero_third q he (fun n hn => hnz n (by omega)) (thetaKL_ne q fun n hn => hnz n (by omega))]

end Lightlike.TemperleyLieb
