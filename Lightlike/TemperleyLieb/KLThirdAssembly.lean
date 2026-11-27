import Mathlib
import Lightlike.TemperleyLieb.KLThirdRec
import Lightlike.TemperleyLieb.Pentagon

/-!
# The Kauffman–Lins third-block recursion: assembly

The recursion `klCoef_third_rec` of the Kauffman–Lins coefficient in the third block (the same identity as
`Fc_third_rec` for `Fc`) is assembled here from the telescoped certificates (`KLTelescoping.lean`) and the
coefficient relations (`KLThirdRec.lean`). The left side collapses to the two terms `f + h = m`
(`klCoef_third_lhs`); each term is a tetrahedral sum (`kl_hat_lower_*`, `kl_hat_upper_*`), the three sums satisfy the
telescoped identity (`kl_tel_lower`, `kl_tel_upper`), the coefficients are proportional to its coefficients wherever
the sums do not vanish (the relations of `KLThirdRec.lean`), and an absent term has an empty box (`kl_lower_*_present`,
`kl_upper_*_present`); `comb_of_prop` combines them for `g₀ = 1` (`kl_third_lower`) and `g₀ = 0` (`kl_third_upper`).
The statement is at generic `q` (`q^{2x} ≠ 1` for `x ≤ 2(a+b+c)+6`), an intermediate step of `Fc = klCoef`.
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
lemma kl_lower_0_imp_c {a b c e₀ d₀ m i : ℕ} (hm0 : m = 0) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m)
    (hv : ValidA a b c 1 e₀ d₀ 1) (hi : e₀ + d₀ + 1 = m + i)
    (h0 : 1 ≤ i ∧ KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 (i - 1) 1 0 i ∧ KLAdm a b c e₀ d₀ m (i - 1)) :
    KLAdm a b (c + 1) e₀ (d₀ + 1) m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1) := by
  subst hm0
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ h0 ⊢
  omega
set_option maxHeartbeats 1000000 in
/-- **The Kauffman–Lins third-block recursion for `g₀ = 1`**, on the two terms of the left side. -/
theorem kl_third_lower (q : kˣ) {a b c e₀ d₀ m i : ℕ}
    (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 1)
    (hi : e₀ + d₀ + 1 = m + i) :
    klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 (i - 1) 1 0 i * klCoef q a b c e₀ d₀ m (i - 1)) +
      klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 i 1 1 i * klCoef q a b c e₀ d₀ (m - 1) i) =
      klCoef q a b (c + 1) e₀ (d₀ + 1) m i * klCoef q (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1) := by
  classical
  have hv' := hv
  obtain ⟨he, hd₀, hg, -⟩ := hv'
  have he1 := he.trans (min_le_left _ _); have he2 := he.trans (min_le_right _ _)
  have hd1 := hd₀.trans (min_le_left _ _); have hd2 := hd₀.trans (min_le_right _ _)
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := hD_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hnz := qfac_ne_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hqb : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  have hnz3 : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0 := fun n hn => hnz n (by omega)
  have hqb3 : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0 := fun n h1 h2 => hqb n h1 (by omega)
  set N := a + 2 * b - 2 * e₀ + c - d₀ + 1 - m + 1
  set δθ := deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀)
  set Sc := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c + 1 - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
        (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z
  set S0 := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ)
        (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z
  set S1 := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ)
        (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m : ℕ)
        (a + b + c - e₀ + 1 - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z
  set Pcp := tetPre q a b (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m)
        (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ - 1)
  set P0p := tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m)
        (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)
  set P1p := tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀)
        (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ + 1 - m)
        (a + b + c - e₀ + 1 - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)
  set lc := qb q (d₀ + 1) * qb q (b + c + 2 - 2 * m)
  set l0 := qb q (b + c - m + 2) * qb q (a - i + 1)
  set l1 := qb q (b - e₀ + c - d₀ + 1 - m) * qb q (b + 1 - m)
  have htel : lc * Sc - l0 * S0 - l1 * S1 = 0 := kl_tel_lower q hq2 hmb hmz hia hiz hv hi
  -- presence
  set Pc : Prop := KLAdm a b (c + 1) e₀ (d₀ + 1) m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1)
  set P0 : Prop := 1 ≤ i ∧ KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 (i - 1) 1 0 i ∧ KLAdm a b c e₀ d₀ m (i - 1)
  set A0v := qb q (b + c - m + 2) * qb q (c - m + 1) / (qb q (c + 1) * qb q (b + c - 2 * m + 2)) *
    (qb q i / qb q (b + c - 2 * m + 1))
  set Cc : k := if Pc then qb q (d₀ + 1) / qb q (c + 1) * Pcp else 0
  set C0 : k := if P0 then A0v * P0p else 0
  set C1 : k := if 1 ≤ m then qb q m / qb q (c + 1) * P1p else 0
  -- the empty boxes
  have hSc : ¬ Pc → Sc = 0 := fun h => by
    have := kl_lower_c_present hmb hmz hia hiz hv hi h
    exact sum_tetHat_eq_zero q N fun z => by omega
  have hS0 : ¬ P0 → S0 = 0 := fun h => by
    have := kl_lower_0_present hmb hmz hia hiz hv hi h
    exact sum_tetHat_eq_zero q N fun z => by omega
  have hS1 : m = 0 → S1 = 0 := fun h => sum_tetHat_eq_zero q N fun z => by omega
  -- the three terms
  have eC : klCoef q a b (c + 1) e₀ (d₀ + 1) m i * klCoef q (a + b - 2 * e₀) c 1 d₀ 1 0 (d₀ + 1) = Cc * (δθ * Sc) := by
    by_cases h : Pc
    · simp only [Cc, if_pos h]
      rw [kl_hat_lower_c q h.1 hi, klCoef_one_10' q h.2 (fun n hn => hnz n (by omega))]
      ring
    · simp only [Cc, if_neg h, zero_mul]
      by_cases h1 : KLAdm a b (c + 1) e₀ (d₀ + 1) m i
      · rw [klCoef_eq_zero_of_not (fun h2 => h ⟨h1, h2⟩), mul_zero]
      · rw [klCoef_eq_zero_of_not h1, zero_mul]
  have e0 : klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 (i - 1) 1 0 i * klCoef q a b c e₀ d₀ m (i - 1)) =
      C0 * (δθ * S0) := by
    by_cases h : P0
    · simp only [C0, if_pos h]
      obtain ⟨hi1, hA, hB, hT⟩ := h
      have hB' : KLAdm a (b + c - 2 * m) 1 (i - 1) 1 0 (i - 1 + 1) := by rwa [Nat.sub_add_cancel hi1]
      rw [kl_hat_lower_0 q hT hi hi1, klCoef_one_00' q hA (fun n hn => hnz n (by omega)),
        show klCoef q a (b + c - 2 * m) 1 (i - 1) 1 0 i = klCoef q a (b + c - 2 * m) 1 (i - 1) 1 0 (i - 1 + 1) by
          rw [Nat.sub_add_cancel hi1],
        klCoef_one_10' q hB' (fun n hn => hnz n (by omega)), Nat.sub_add_cancel hi1]
      simp only [A0v]; ring
    · simp only [C0, if_neg h, zero_mul]
      by_cases hi1 : 1 ≤ i
      · by_cases hA : KLAdm b c 1 m 0 0 m
        · by_cases hB : KLAdm a (b + c - 2 * m) 1 (i - 1) 1 0 i
          · rw [klCoef_eq_zero_of_not (fun hT => h ⟨hi1, hA, hB, hT⟩)]; ring
          · rw [klCoef_eq_zero_of_not hB]; ring
        · rw [klCoef_eq_zero_of_not hA]; ring
      · rw [klCoef_eq_zero_of_not (a := a) (b := b + c - 2 * m) (c := 1) (e := i - 1) (d := 1) (f := 0) (d' := i)
          (fun hk => by simp only [KLAdm, le_min_iff] at hk; omega)]; ring
  have e1 : klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 i 1 1 i * klCoef q a b c e₀ d₀ (m - 1) i) =
      C1 * (δθ * S1) := by
    by_cases hm : 1 ≤ m
    · simp only [C1, if_pos hm]
      obtain ⟨hA, hB, hT⟩ := kl_lower_1_present hmb hmz hia hiz hv hi hm
      have hA' : KLAdm b c 1 (m - 1) 1 0 (m - 1 + 1) := by rwa [Nat.sub_add_cancel hm]
      rw [kl_hat_lower_1 q hT hi hm, klCoef_one_11' q hB (fun n hn => hnz n (by omega)),
        show klCoef q b c 1 (m - 1) 1 0 m = klCoef q b c 1 (m - 1) 1 0 (m - 1 + 1) by rw [Nat.sub_add_cancel hm],
        klCoef_one_10' q hA' (fun n hn => hnz n (by omega)), Nat.sub_add_cancel hm]
      ring
    · simp only [C1, if_neg hm, zero_mul]
      rw [klCoef_eq_zero_of_not (a := b) (b := c) (c := 1) (e := m - 1) (d := 1) (f := 0) (d' := m)
        (fun hk => by simp only [KLAdm, le_min_iff] at hk; omega)]; ring
  -- the combination
  have comb : Cc * Sc - C0 * S0 - C1 * S1 = 0 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · have hlc : lc ≠ 0 := mul_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega))
      refine comb_of_prop (lp := lc) (Cp := Cc) hlc htel (by ring) ?_ ?_
      · by_cases h : P0
        · have hc := kl_lower_0_imp_c hm0 hia hiz hv hi h
          have rel := kl_rel_lower_c0 q hnz3 hqb3 hi hia hv hc.1 hc.2 h.2.1 h.2.2.2 h.1
          simp only [Cc, C0, if_pos h, if_pos (show Pc from hc)]
          linear_combination (-S0) * rel
        · rw [hS0 h]; ring
      · rw [hS1 hm0]; ring
    · have hm1 : 1 ≤ m := hm
      have hl1 : l1 ≠ 0 := mul_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega))
      obtain ⟨hA1, hB1, hT1⟩ := kl_lower_1_present hmb hmz hia hiz hv hi hm1
      refine comb_of_prop (lp := l1) (Cp := C1) hl1 htel ?_ ?_ (by ring)
      · by_cases h : Pc
        · have rel := kl_rel_lower_c1 q hnz3 hqb3 hi hia hv h.1 h.2 hA1 hT1 hm1
          simp only [Cc, C1, if_pos h, if_pos hm1]
          linear_combination Sc * rel
        · rw [hSc h]; ring
      · by_cases h : P0
        · have rel := kl_rel_lower_01 q hnz3 hqb3 hi hia hv h.2.1 h.2.2.2 h.1 hA1 hT1 hm1
          simp only [C0, C1, if_pos h, if_pos hm1]
          linear_combination S0 * rel
        · rw [hS0 h]; ring
  rw [e0, e1, eC]
  linear_combination (-δθ) * comb
/-- The `c` term of the `g₀ = 0` recursion as a tetrahedral sum (the base data). -/
lemma kl_hat_upper_c (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hc : KLAdm a b (c + 1) e₀ d₀ m i) (hi : e₀ + d₀ = m + i)
    (hdc : d₀ ≤ c) :
    klCoef q a b (c + 1) e₀ d₀ m i = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀ + 1) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c + 1 - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1)) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ + 1 : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c + 1 - e₀ - d₀ : ℕ) z := by
  have hk := hc
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q hc rfl (by omega) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The `h = 0` term of the `g₀ = 0` recursion as a tetrahedral sum. -/
lemma kl_hat_upper_0 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (h0 : KLAdm a b c e₀ d₀ m i) (hi : e₀ + d₀ = m + i) :
    klCoef q a b c e₀ d₀ m i = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ) (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z := by
  have hk := h0
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q h0 rfl rfl rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- The `h = 1` term of the `g₀ = 0` recursion as a tetrahedral sum. -/
lemma kl_hat_upper_1 (q : kˣ) {a b c e₀ d₀ m i : ℕ} (h1 : KLAdm a b c e₀ d₀ (m - 1) (i + 1)) (hi : e₀ + d₀ = m + i)
    (hm : 1 ≤ m) :
    klCoef q a b c e₀ d₀ (m - 1) (i + 1) = deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀) *
      (tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z := by
  have hk := h1
  simp only [KLAdm, le_min_iff] at hk
  exact klCoef_eq_hat q h1 rfl rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- **The telescoped identity of the `g₀ = 0` recursion** on the three tetrahedral sums. -/
lemma kl_tel_upper (q : kˣ) {a b c e₀ d₀ m i : ℕ} (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0)
    (hi : e₀ + d₀ = m + i) :
    qb q (c - d₀ + 1) * qb q (b + c + 2 - 2 * m) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ + 1 : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c + 1 - e₀ - d₀ : ℕ) z -
      -(qb q (b + c - m + 2) * qb q (a + b + c - 2 * m - i + 2)) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ) (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z -
      qb q (b + 1 - m) * qb q (i + 1) * ∑ z ∈ range (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1), tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z = 0 := by
  obtain ⟨he, hd₀, hg, hg1⟩ := hv
  have he1 := he.trans (min_le_left _ _); have he2 := he.trans (min_le_right _ _)
  have hd1 := hd₀.trans (min_le_left _ _); have hd2 := hd₀.trans (min_le_right _ _)
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := hD_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hnz := qz_ne_of_pow q (M := 2 * (a + b + c) + 6) hq2
  have ht := tel_upper_sum q hD (M := ((2 * (a + b + c) + 6 : ℕ) : ℤ)) hnz (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1)
    (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ + 1 : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ)
    ⟨by positivity, by positivity, by positivity, by positivity⟩
    ⟨by push_cast; omega, by push_cast; omega, by push_cast; omega, by omega⟩ (by push_cast; omega)
  have hB3 : ((a + b - e₀ : ℕ) : ℤ) + ((a + b - 2 * e₀ + c - d₀ + 1 : ℕ) : ℤ) + ((b + c + 1 - m : ℕ) : ℤ) + ((a + b + c + 1 - m - e₀ - d₀ : ℕ) : ℤ) - ((a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) : ℤ) - ((a + b + c + 1 - e₀ - m : ℕ) : ℤ) =
      ((a + b + c + 1 - e₀ - d₀ : ℕ) : ℤ) := by omega
  simp only [hB3] at ht
  rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine (sum_congr rfl fun z _ => ?_).trans ht
  rw [show ((a + b + c + 1 - e₀ - d₀ : ℕ) : ℤ) - ((a + b - e₀ : ℕ) : ℤ) = ((c - d₀ + 1 : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) + ((a + b + c + 1 - m - e₀ - d₀ : ℕ) : ℤ) - ((a + b + c + 1 - e₀ - d₀ : ℕ) : ℤ) + 1 = ((b + c + 2 - 2 * m : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) + 1 = ((b + c - m + 2 : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - m - e₀ - d₀ : ℕ) : ℤ) + 1 = ((a + b + c - 2 * m - i + 2 : ℕ) : ℤ) by omega,
    show ((a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) : ℤ) - ((a + b - 2 * e₀ + c - d₀ + 1 : ℕ) : ℤ) + 1 = ((b + 1 - m : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - e₀ - m : ℕ) : ℤ) - ((a + b - 2 * e₀ + c - d₀ + 1 : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by omega,
    show ((a + b - 2 * e₀ + c - d₀ + 1 : ℕ) : ℤ) - 1 = ((a + b - 2 * e₀ + c - d₀ : ℕ) : ℤ) by omega,
    show ((b + c + 1 - m : ℕ) : ℤ) - 1 = ((b + c - m : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - m - e₀ - d₀ : ℕ) : ℤ) - 1 = ((a + b + c - m - e₀ - d₀ : ℕ) : ℤ) by omega,
    show ((a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) : ℤ) - 1 = ((a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - e₀ - m : ℕ) : ℤ) - 1 = ((a + b + c - e₀ - m : ℕ) : ℤ) by omega,
    show ((a + b + c + 1 - e₀ - d₀ : ℕ) : ℤ) - 1 = ((a + b + c - e₀ - d₀ : ℕ) : ℤ) by omega,
    ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz, ← qb_eq_qz]
  ring

/-- The `h = 0` term of the `g₀ = 0` recursion forces the `c` term. -/
lemma kl_upper_0_imp_c {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0) (hi : e₀ + d₀ = m + i)
    (h0 : KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 i 0 0 i ∧ KLAdm a b c e₀ d₀ m i) :
    KLAdm a b (c + 1) e₀ d₀ m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 0 0 d₀ := by
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ h0 ⊢
  omega

/-- The `h = 1` term of the `g₀ = 0` recursion forces the `c` term. -/
lemma kl_upper_1_imp_c {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0) (hi : e₀ + d₀ = m + i)
    (h1 : 1 ≤ m ∧ KLAdm b c 1 (m - 1) 1 0 m ∧ KLAdm a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i ∧
      KLAdm a b c e₀ d₀ (m - 1) (i + 1)) :
    KLAdm a b (c + 1) e₀ d₀ m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 0 0 d₀ := by
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ h1 ⊢
  omega

/-- The `h = 0` term of the `g₀ = 0` recursion: present, or its box is empty. -/
lemma kl_upper_0_present {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0) (hi : e₀ + d₀ = m + i)
    (h : ¬ (KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 i 0 0 i ∧ KLAdm a b c e₀ d₀ m i)) :
    a + 2 * b - 2 * e₀ + c - d₀ - m < a + b - e₀ ∨ a + b + c - e₀ - m < a + b - e₀ := by
  by_contra hlt
  apply h
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ ⊢
  omega

/-- The `h = 1` term of the `g₀ = 0` recursion: present, or its box is empty. -/
lemma kl_upper_1_present {a b c e₀ d₀ m i : ℕ} (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a)
    (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0) (hi : e₀ + d₀ = m + i)
    (h : ¬ (1 ≤ m ∧ KLAdm b c 1 (m - 1) 1 0 m ∧ KLAdm a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i ∧
      KLAdm a b c e₀ d₀ (m - 1) (i + 1))) :
    a + b + c - e₀ - d₀ < a + b + c + 1 - m - e₀ - d₀ ∨ a + b + c - e₀ - d₀ < b + c + 1 - m := by
  by_contra hlt
  apply h
  obtain ⟨he, hd₀, hg, -⟩ := hv
  simp only [KLAdm, le_min_iff] at he hd₀ ⊢
  omega
set_option maxHeartbeats 1000000 in
/-- **The Kauffman–Lins third-block recursion for `g₀ = 0`**, on the two terms of the left side. -/
theorem kl_third_upper (q : kˣ) {a b c e₀ d₀ m i : ℕ}
    (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m) (hv : ValidA a b c 1 e₀ d₀ 0)
    (hi : e₀ + d₀ = m + i) :
    klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 i 0 0 i * klCoef q a b c e₀ d₀ m i) +
      klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i *
        klCoef q a b c e₀ d₀ (m - 1) (i + 1)) =
      klCoef q a b (c + 1) e₀ d₀ m i * klCoef q (a + b - 2 * e₀) c 1 d₀ 0 0 d₀ := by
  classical
  have hv' := hv
  obtain ⟨he, hd₀, hg, -⟩ := hv'
  have he1 := he.trans (min_le_left _ _); have he2 := he.trans (min_le_right _ _)
  have hd1 := hd₀.trans (min_le_left _ _); have hd2 := hd₀.trans (min_le_right _ _)
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := hD_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hnz := qfac_ne_of_pow q (N := 2 * (a + b + c) + 6) (by omega) hq2
  have hqb : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  have hnz3 : ∀ n, n ≤ a + b + c + 3 → qfac q n ≠ 0 := fun n hn => hnz n (by omega)
  have hqb3 : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → qb q n ≠ 0 := fun n h1 h2 => hqb n h1 (by omega)
  set N := a + 2 * b - 2 * e₀ + c + 1 - d₀ - m + 1
  set δθ := deltaKL q (a + b - 2 * e₀) / thetaKL q a b (a + b - 2 * e₀)
  set Sc := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ + 1 : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c + 1 - e₀ - d₀ : ℕ) z
  set S0 := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c - m : ℕ) (a + b + c - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c - d₀ - m : ℕ) (a + b + c - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z
  set S1 := ∑ z ∈ range N, tetHat q (a + b - e₀ : ℕ) (a + b - 2 * e₀ + c - d₀ : ℕ) (b + c + 1 - m : ℕ) (a + b + c + 1 - m - e₀ - d₀ : ℕ) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m : ℕ) (a + b + c + 1 - e₀ - m : ℕ) (a + b + c - e₀ - d₀ : ℕ) z
  set Pcp := tetPre q a b (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1) (a + b - 2 * e₀) (b + c + 1 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀ + 1) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c + 1 - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) (c + 1) (a + b - 2 * e₀ + c - 2 * d₀ + 1)
  set P0p := tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c - m) (a + b + c - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c - d₀ - m) (a + b + c - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)
  set P1p := tetPre q a b c (a + b - 2 * e₀ + c - 2 * d₀) (a + b - 2 * e₀) (b + c + 2 - 2 * m) (a + b - e₀) (a + b - 2 * e₀ + c - d₀) (b + c + 1 - m) (a + b + c + 1 - m - e₀ - d₀) (a + 2 * b - 2 * e₀ + c + 1 - d₀ - m) (a + b + c + 1 - e₀ - m) (a + b + c - e₀ - d₀) /
        thetaKL q (a + b - 2 * e₀) c (a + b - 2 * e₀ + c - 2 * d₀)
  set lc := qb q (c - d₀ + 1) * qb q (b + c + 2 - 2 * m)
  set l0 := -(qb q (b + c - m + 2) * qb q (a + b + c - 2 * m - i + 2))
  set l1 := qb q (b + 1 - m) * qb q (i + 1)
  have htel : lc * Sc - l0 * S0 - l1 * S1 = 0 := kl_tel_upper q hq2 hmb hmz hia hiz hv hi
  set Pc : Prop := KLAdm a b (c + 1) e₀ d₀ m i ∧ KLAdm (a + b - 2 * e₀) c 1 d₀ 0 0 d₀
  set P0 : Prop := KLAdm b c 1 m 0 0 m ∧ KLAdm a (b + c - 2 * m) 1 i 0 0 i ∧ KLAdm a b c e₀ d₀ m i
  set P1 : Prop := 1 ≤ m ∧ KLAdm b c 1 (m - 1) 1 0 m ∧ KLAdm a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i ∧
    KLAdm a b c e₀ d₀ (m - 1) (i + 1)
  set Ccv := qb q (a + b - 2 * e₀ + c - d₀ + 2) * qb q (c - d₀ + 1) / (qb q (c + 1) * qb q (a + b - 2 * e₀ + c - 2 * d₀ + 2))
  set A0v := qb q (b + c - m + 2) * qb q (c - m + 1) / (qb q (c + 1) * qb q (b + c + 2 - 2 * m)) *
    (qb q (a + b + c - 2 * m - i + 2) * qb q (b + c - 2 * m - i + 1) /
      (qb q (b + c + 1 - 2 * m) * qb q (a + b + c - 2 * m - 2 * i + 2)))
  set A1v := qb q m / qb q (c + 1) * -(qb q (a - i) / qb q (a + b + c + 2 - 2 * m - 2 * i))
  set Cc : k := if Pc then Ccv * Pcp else 0
  set C0 : k := if P0 then A0v * P0p else 0
  set C1 : k := if P1 then A1v * P1p else 0
  have hS0 : ¬ P0 → S0 = 0 := fun h => by
    have := kl_upper_0_present hmb hmz hia hiz hv hi h
    exact sum_tetHat_eq_zero q N fun z => by omega
  have hS1 : ¬ P1 → S1 = 0 := fun h => by
    have := kl_upper_1_present hmb hmz hia hiz hv hi h
    exact sum_tetHat_eq_zero q N fun z => by omega
  have eC : klCoef q a b (c + 1) e₀ d₀ m i * klCoef q (a + b - 2 * e₀) c 1 d₀ 0 0 d₀ = Cc * (δθ * Sc) := by
    by_cases h : Pc
    · simp only [Cc, if_pos h]
      rw [kl_hat_upper_c q h.1 hi hd2, klCoef_one_00' q h.2 (fun n hn => hnz n (by omega))]
      simp only [Ccv]; ring
    · simp only [Cc, if_neg h, zero_mul]
      by_cases h1 : KLAdm a b (c + 1) e₀ d₀ m i
      · rw [klCoef_eq_zero_of_not (fun h2 => h ⟨h1, h2⟩), mul_zero]
      · rw [klCoef_eq_zero_of_not h1, zero_mul]
  have e0 : klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 i 0 0 i * klCoef q a b c e₀ d₀ m i) =
      C0 * (δθ * S0) := by
    by_cases h : P0
    · simp only [C0, if_pos h]
      obtain ⟨hA, hB, hT⟩ := h
      have hA' := hA; simp only [KLAdm, le_min_iff] at hA'
      have hB' := hB; simp only [KLAdm, le_min_iff] at hB'
      rw [kl_hat_upper_0 q hT hi, klCoef_one_00' q hA (fun n hn => hnz n (by omega)),
        klCoef_one_00' q hB (fun n hn => hnz n (by omega)),
        show b + c - 2 * m + 2 = b + c + 2 - 2 * m by omega,
        show a + (b + c - 2 * m) - i + 2 = a + b + c - 2 * m - i + 2 by omega,
        show b + c - 2 * m + 1 = b + c + 1 - 2 * m by omega,
        show a + (b + c - 2 * m) - 2 * i + 2 = a + b + c - 2 * m - 2 * i + 2 by omega]
      simp only [A0v]; ring
    · simp only [C0, if_neg h, zero_mul]
      by_cases hA : KLAdm b c 1 m 0 0 m
      · by_cases hB : KLAdm a (b + c - 2 * m) 1 i 0 0 i
        · rw [klCoef_eq_zero_of_not (fun hT => h ⟨hA, hB, hT⟩)]; ring
        · rw [klCoef_eq_zero_of_not hB]; ring
      · rw [klCoef_eq_zero_of_not hA]; ring
  have e1 : klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i *
        klCoef q a b c e₀ d₀ (m - 1) (i + 1)) = C1 * (δθ * S1) := by
    by_cases h : P1
    · simp only [C1, if_pos h]
      obtain ⟨hm, hA, hB, hT⟩ := h
      have hA' : KLAdm b c 1 (m - 1) 1 0 (m - 1 + 1) := by rwa [Nat.sub_add_cancel hm]
      have hB' := hB; simp only [KLAdm, le_min_iff] at hB'
      rw [kl_hat_upper_1 q hT hi hm, klCoef_one_01' q hB (fun n hn => hnz n (by omega)),
        show klCoef q b c 1 (m - 1) 1 0 m = klCoef q b c 1 (m - 1) 1 0 (m - 1 + 1) by rw [Nat.sub_add_cancel hm],
        klCoef_one_10' q hA' (fun n hn => hnz n (by omega)), Nat.sub_add_cancel hm,
        show a + (b + c - 2 * (m - 1)) - 2 * i = a + b + c + 2 - 2 * m - 2 * i by omega]
      simp only [A1v]; ring
    · simp only [C1, if_neg h, zero_mul]
      by_cases hm : 1 ≤ m
      · by_cases hA : KLAdm b c 1 (m - 1) 1 0 m
        · by_cases hB : KLAdm a (b + c - 2 * (m - 1)) 1 (i + 1) 0 1 i
          · rw [klCoef_eq_zero_of_not (fun hT => h ⟨hm, hA, hB, hT⟩)]; ring
          · rw [klCoef_eq_zero_of_not hB]; ring
        · rw [klCoef_eq_zero_of_not hA]; ring
      · rw [klCoef_eq_zero_of_not (a := b) (b := c) (c := 1) (e := m - 1) (d := 1) (f := 0) (d' := m)
          (fun hk => by simp only [KLAdm, le_min_iff] at hk; omega)]; ring
  have comb : Cc * Sc - C0 * S0 - C1 * S1 = 0 := by
    have hlc : lc ≠ 0 := mul_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega))
    refine comb_of_prop (lp := lc) (Cp := Cc) hlc htel (by ring) ?_ ?_
    · by_cases h : P0
      · have hc := kl_upper_0_imp_c hmb hmz hia hiz hv hi h
        have rel := kl_rel_upper_0c q hnz3 hqb3 hi hia hv h.1 h.2.2 hc.1 hc.2
        simp only [Cc, C0, if_pos h, if_pos (show Pc from hc)]
        linear_combination S0 * rel
      · rw [hS0 h]; ring
    · by_cases h : P1
      · have hc := kl_upper_1_imp_c hmb hmz hia hiz hv hi h
        have rel := kl_rel_upper_1c q hnz3 hqb3 hi hia hv h.2.1 h.2.2.2 h.1 hc.1 hc.2
        simp only [Cc, C1, if_pos h, if_pos (show Pc from hc)]
        linear_combination S1 * rel
      · rw [hS1 h]; ring
  rw [e0, e1, eC]
  linear_combination (-δθ) * comb
/-- **The recursion of the Kauffman–Lins coefficient in the third block**: the same identity as `Fc_third_rec` for
`Fc` (the pentagon with a fourth block of one strand and `j = 0`), at every `q` with `q^{2x} ≠ 1` for
`1 ≤ x ≤ 2(a+b+c)+6`. -/
theorem klCoef_third_rec (q : kˣ) (a b c e₀ d₀ g₀ m i : ℕ)
    (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m)
    (h₀ : ValidA a b c 1 e₀ d₀ g₀) :
    ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e₀ d₀ f d') =
      klCoef q a b (c + 1) e₀ (d₀ + g₀) m i * klCoef q (a + b - 2 * e₀) c 1 d₀ g₀ 0 (d₀ + g₀) := by
  have hg1 : g₀ ≤ 1 := h₀.2.2.2
  have hA10 : klCoef q b c 1 0 1 0 0 = 0 :=
    klCoef_eq_zero_of_not fun hk => by simp only [KLAdm, le_min_iff] at hk; omega
  -- the left side in two terms
  have hL : ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e₀ d₀ f d') =
      klCoef q b c 1 m 0 0 m * (klCoef q a (b + c - 2 * m) 1 (e₀ + d₀ - m) g₀ 0 i *
          klCoef q a b c e₀ d₀ m (e₀ + d₀ - m)) +
        klCoef q b c 1 (m - 1) 1 0 m * (klCoef q a (b + c - 2 * (m - 1)) 1 (e₀ + d₀ - (m - 1)) g₀ 1 i *
          klCoef q a b c e₀ d₀ (m - 1) (e₀ + d₀ - (m - 1))) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0
      rw [show (0 : ℕ) - 1 = 0 from rfl, hA10, zero_mul, add_zero]
      have hA : ∀ f h, ¬ (f + h = 0) → klCoef q b c 1 f h 0 0 = 0 := by
        intro f h hfh
        refine klCoef_eq_zero_of_not fun hk => hfh ?_
        simp only [KLAdm, le_min_iff] at hk; omega
      have hT : ∀ d', d' ≠ e₀ + d₀ - 0 → klCoef q a b c e₀ d₀ 0 d' = 0 := by
        intro d' hne
        refine klCoef_eq_zero_of_not fun hk => hne ?_
        simp only [KLAdm, le_min_iff] at hk; omega
      rw [sum_eq_single 0 (fun f _ hf => by
          rw [sum_eq_zero fun h _ => sum_eq_zero fun d' _ => by rw [hA f h (by omega), zero_mul]])
        (fun hm' => absurd (mem_range.mpr (by omega)) hm')]
      rw [sum_eq_single 0 (fun h hh hne => by rw [sum_eq_zero fun d' _ => by rw [hA 0 h (by omega), zero_mul]])
        (fun hm' => absurd (mem_range.mpr (by omega)) hm')]
      rw [← mul_sum, sum_eq_single (e₀ + d₀ - 0) (fun d' _ hne => by rw [hT d' hne]; ring) (fun hm' => by
        rw [klCoef_eq_zero_of_not (a := a) (b := b) (c := c) (e := e₀) (d := d₀) (f := 0) (d' := e₀ + d₀ - 0)
          (fun hk => by simp only [KLAdm, le_min_iff] at hk; have := mem_range.not.mp hm'; omega)]; ring)]
    · exact klCoef_third_lhs q a b c e₀ d₀ g₀ m i hm hmb
  rw [hL]
  -- the terms vanish unless the total channels agree
  by_cases hi : e₀ + d₀ + g₀ = m + i
  · rcases Nat.lt_or_ge g₀ 1 with hg0 | hg
    · obtain rfl : g₀ = 0 := by omega
      have h := kl_third_upper q hq2 hmb hmz hia hiz h₀ (by omega)
      simp only [Nat.add_zero]
      rw [← h, show e₀ + d₀ - m = i by omega]
      congr 1
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · subst hm0; simp only [show (0 : ℕ) - 1 = 0 from rfl, hA10, zero_mul]
      · rw [show e₀ + d₀ - (m - 1) = i + 1 by omega]
    · obtain rfl : g₀ = 1 := by omega
      have h := kl_third_lower q hq2 hmb hmz hia hiz h₀ (by omega)
      rw [← h, show e₀ + d₀ - m = i - 1 by omega]
      congr 1
      rcases Nat.eq_zero_or_pos m with hm0 | hm
      · subst hm0; simp only [show (0 : ℕ) - 1 = 0 from rfl, hA10, zero_mul]
      · rw [show e₀ + d₀ - (m - 1) = i by omega]
  · obtain ⟨he, hd₀, -, -⟩ := h₀
    simp only [le_min_iff] at he hd₀
    have z : ∀ {f h d' : ℕ}, f + h = m → klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e₀ d₀ f d' = 0 := by
      intro f h d' hfh
      by_cases hB : KLAdm a (b + c - 2 * f) 1 d' g₀ h i
      · rw [klCoef_eq_zero_of_not (a := a) (b := b) (c := c) (e := e₀) (d := d₀) (f := f) (d' := d') (fun hT => by
          simp only [KLAdm, le_min_iff] at hB hT; omega), mul_zero]
      · rw [klCoef_eq_zero_of_not hB, zero_mul]
    have zR : klCoef q a b (c + 1) e₀ (d₀ + g₀) m i = 0 :=
      klCoef_eq_zero_of_not fun hk => by simp only [KLAdm, le_min_iff] at hk; omega
    rw [zR, zero_mul]
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0; rw [z (by omega), show (0 : ℕ) - 1 = 0 from rfl, hA10]; ring
    · rw [z (by omega), z (by omega)]; ring
end Lightlike.TemperleyLieb
