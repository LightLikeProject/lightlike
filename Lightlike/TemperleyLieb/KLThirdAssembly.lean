import Mathlib
import Lightlike.TemperleyLieb.KLThirdRec
import Lightlike.TemperleyLieb.Pentagon

/-!
# The Kauffman–Lins third-block recursion: assembly

The recursion `klCoef_third_rec` of the Kauffman–Lins coefficient in the third block (the same identity as
`Fc_third_rec` for `Fc`) is assembled here from the telescoped certificates (`KLTelescoping.lean`) and the
coefficient relations (`KLThirdRec.lean`). This file holds the collapse of its left side to the two terms
`f + h = m` (`klCoef_third_lhs`).
-/
namespace Lightlike.TemperleyLieb
open Finset
variable {k : Type*} [Field k]

lemma klCoef_eq_zero_of_not {q : kˣ} {a b c e d f d' : ℕ} (h : ¬ KLAdm a b c e d f d') :
    klCoef q a b c e d f d' = 0 := by unfold klCoef; rw [if_neg h]

/-- **The left side of the Kauffman–Lins third-block recursion, two terms** (`m ≥ 1`): only `f + h = m` and
`d' = e₀ + d₀ - f` survive. -/
theorem klCoef_third_lhs (q : kˣ) (a b c e₀ d₀ g₀ m i : ℕ) (hm : 1 ≤ m) (hmb : m ≤ b) :
    ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e₀ d₀ f d') =
      klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 (e₀ + d₀ - m) g₀ 0 i *
          klCoef q a b c e₀ d₀ m (e₀ + d₀ - m)) +
        klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 (e₀ + d₀ - (m - 1)) g₀ 1 i *
          klCoef q a b c e₀ d₀ (m - 1) (e₀ + d₀ - (m - 1))) := by
  have hA : ∀ f h, ¬ (f + h = m) → klCoef q b c 1 f h 0 m = 0 := by
    intro f h hfh
    refine klCoef_eq_zero_of_not fun hk => hfh ?_
    obtain ⟨h1, h2, -, -, h5⟩ := hk
    have := h1.trans (min_le_right _ _); have := h2.trans (min_le_right _ _); omega
  have hT : ∀ f d', d' ≠ e₀ + d₀ - f → klCoef q a b c e₀ d₀ f d' = 0 := by
    intro f d' hne
    refine klCoef_eq_zero_of_not fun hk => hne ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := hk
    have := h1.trans (min_le_left _ _); have := h1.trans (min_le_right _ _)
    have := h2.trans (min_le_left _ _); have := h3.trans (min_le_left _ _); have := h3.trans (min_le_right _ _)
    have := h4.trans (min_le_right _ _); omega
  have hTr : ∀ f, a < e₀ + d₀ - f → klCoef q a b c e₀ d₀ f (e₀ + d₀ - f) = 0 := by
    intro f hf
    refine klCoef_eq_zero_of_not fun hk => ?_
    have := hk.2.2.2.1.trans (min_le_left _ _); omega
  have row : ∀ f h, f + h = m → h ≤ 1 → ∑ h' ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
      klCoef q b c 1 f h' 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h' i * klCoef q a b c e₀ d₀ f d') =
      klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 (e₀ + d₀ - f) g₀ h i *
        klCoef q a b c e₀ d₀ f (e₀ + d₀ - f)) := by
    intro f h hfh hh
    rw [sum_eq_single h (fun h' _ hne => by simp [hA f h' (by omega)])
      (fun hm' => absurd (mem_range.mpr (by omega)) hm')]
    rw [sum_eq_single (e₀ + d₀ - f) (fun d' _ hne => by rw [hT f d' hne]; ring)
      (fun hm' => by have := mem_range.not.mp hm'; rw [hTr f (by omega)]; ring)]
  rw [sum_eq_add m (m - 1) (by omega) (fun f _ hf => by
      rw [sum_eq_zero fun h hh => sum_eq_zero fun d' _ => by rw [hA f h (by rw [mem_range] at hh; omega), zero_mul]])
    (fun hm' => absurd (mem_range.mpr (by omega)) hm') (fun hm' => absurd (mem_range.mpr (by omega)) hm'),
    row m 0 (by omega) (by omega), row (m - 1) 1 (by omega) le_rfl]
/-- The `c` term of the `g₀ = 1` recursion as a tetrahedral sum. -/
lemma kl_hat_lower_c (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hc : KLAdm a b (c + 1) e₀ (d₀ + 1) m i) (hi : e₀ + d₀ + 1 = m + i) :
    klCoef q a b (c + 1) e₀ (d₀ + 1) m i = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m)
        (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1)) *
      ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c + 1 - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
        (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z := by
  have hk := hc
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q hc rfl (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The `h = 0` term of the `g₀ = 1` recursion as a tetrahedral sum. -/
lemma kl_hat_lower_0 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (h0 : KLAdm a b c e₀ d₀ m (i - 1)) (hi : e₀ + d₀ + 1 = m + i)
    (hi1 : 1 ≤ i) :
    klCoef q a b c e₀ d₀ m (i - 1) = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m)
        (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)) *
      ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
        (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z := by
  have hk := h0
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q h0 rfl rfl rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The `h = 1` term of the `g₀ = 1` recursion as a tetrahedral sum (the base data). -/
lemma kl_hat_lower_1 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (h1 : KLAdm a b c e₀ d₀ (m - 1) i) (hi : e₀ + d₀ + 1 = m + i)
    (hm : 1 ≤ m) :
    klCoef q a b c e₀ d₀ (m - 1) i = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m)
        (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)) *
      ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ)
        (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z := by
  have hk := h1
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q h1 rfl rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- **The telescoped identity of the `g₀ = 1` recursion** on the three tetrahedral sums. -/
lemma kl_tel_lower (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 1)
    (hi : e₀ + d₀ + 1 = m + i) :
    qb q (d₀ + 1) * qb q (b + c + 2 - 2 * m) *
        ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
          (b + c + 1 - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
          (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z -
      qb q (b + c - m + 2) * qb q (a - i + 1) *
        ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
          (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
          (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z -
      qb q (b - e₀ + c - d₀ + 1 - m) * qb q (b + 1 - m) *
        ∑ z ∈ range (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
          (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ)
          (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z = 0 := by
  obtain ⟨he, hd₀, hg, hg1⟩ := hv
  have he1 := he.trans (min_le_left _ _); have he2 := he.trans (min_le_right _ _)
  have hd1 := hd₀.trans (min_le_left _ _); have hd2 := hd₀.trans (min_le_right _ _)
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := hD_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hnz := qz_ne_of_pow q (M := 2 * (a + b + c) + 6) hq2
  have ht := tel_lower_sum q hD (M := ((2 * (a + b + c) + 6 : ℕ) : ℤ)) hnz (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1)
    (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ)
    (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ) (a + b + c - e₀ + 1 - m : ℕ)
    ⟨by positivity, by positivity, by positivity, by positivity⟩
    ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega, by omega⟩ (by push_cast; omega)
  have hB3 : ((a + b - e₀ : ℕ) : ℤ) + (a + b - 2 * e₀ + c - d₀ : ℕ) + (b + c + 1 - m : ℕ) +
      (a + b + c + 1 - m - e₀ - d₀ : ℕ) - (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ) - (a + b + c - e₀ + 1 - m : ℕ) =
      (a + b + c - e₀ - d₀ : ℕ) := by omega
  simp only [hB3] at ht
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine (sum_congr rfl fun z _ => ?_).trans ht
  rw [show ((a + b + c - e₀ + 1 - m : ℕ) : ℤ) - (a + b + c + 1 - m - e₀ - d₀ : ℕ) + 1 = ((d₀ + 1 : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) + (a + b + c + 1 - m - e₀ - d₀ : ℕ) - (a + b + c - e₀ - d₀ : ℕ) =
      ((b + c + 2 - 2 * m : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) + 1 = ((b + c - m + 2 : ℕ) : ℤ) by omega,
    show ((a + b + c - e₀ - d₀ : ℕ) : ℤ) - (b + c + 1 - m : ℕ) + 1 = ((a - i + 1 : ℕ) : ℤ) by omega,
    show ((a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ) : ℤ) - (a + b - e₀ : ℕ) = ((b - e₀ + c - d₀ + 1 - m : ℕ) : ℤ) by omega,
    show ((a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ) : ℤ) - (a + b - 2 * e₀ + c - d₀ : ℕ) = ((b + 1 - m : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - m - e₀ - d₀ : ℕ) : ℤ) - 1 = ((a + b + c - m - e₀ - d₀ : ℕ) : ℤ) by omega,
    show ((a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ) : ℤ) - 1 = ((a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) - 1 = ((b + c - m : ℕ) : ℤ) by omega,
    show ((a + b + c - e₀ + 1 - m : ℕ) : ℤ) - 1 = ((a + b + c - e₀ - m : ℕ) : ℤ) by omega,
    ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz]
/-- The `c` term of the `g₀ = 1` recursion is present unless `d₀ = a + b - 2e₀`, and then its box is empty. -/
lemma kl_lower_c_present {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 1) (hi : e₀ + d₀ + 1 = m + i)
    (h : ¬ (KLAdm a b (c + 1) e₀ (d₀ + 1) m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1))) :
    a + 2 * b - 2 * e₀ + c - d₀ - m < b + c + 1 - m := by
  by_contra hlt
  apply h
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ ⊢
  omega

/-- The `h = 0` term: present, or its box is empty. -/
lemma kl_lower_0_present {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 1) (hi : e₀ + d₀ + 1 = m + i)
    (h : ¬ (1 ≤ i ∧ KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 (i - 1) 1 0 i ∧ KLAdm a b c e₀ d₀ m (i - 1))) :
    a + b + c - e₀ - m < a + b - e₀ ∨ a + b + c - e₀ - m < a + b - 2 * e₀ + c - d₀ := by
  by_contra hlt
  apply h
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ ⊢
  omega

/-- For `m ≥ 1` the `h = 1` term is present. -/
lemma kl_lower_1_present {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 1) (hi : e₀ + d₀ + 1 = m + i) (hm : 1 ≤ m) :
    KLAdm b c 1 (m - 1) 1 0 m ∧ KLAdm a (b + c - 2 * (m - 1)) 1 i 1 1 i ∧ KLAdm a b c e₀ d₀ (m - 1) i := by
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ ⊢
  omega

/-- For `m = 0` the `h = 0` term forces the `c` term. -/
lemma kl_lower_0_imp_c {a b c e₀ d₀ i : ℕ} (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * 0)
    (hv : ValidA a b c 1 e₀ d₀ 1) (hi : e₀ + d₀ + 1 = 0 + i)
    (h0 : 1 ≤ i ∧ KLAdm b c 1 0 0 0 0 ∧ KLAdm a (b + c - 2 * 0) 1 (i - 1) 1 0 i ∧ KLAdm a b c e₀ d₀ 0 (i - 1)) :
    KLAdm a b (c + 1) e₀ (d₀ + 1) 0 i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1) := by
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ h0 ⊢
  omega
end Lightlike.TemperleyLieb
