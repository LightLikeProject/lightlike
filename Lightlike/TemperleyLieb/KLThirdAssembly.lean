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
end Lightlike.TemperleyLieb
