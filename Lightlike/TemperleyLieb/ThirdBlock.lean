import Mathlib
import Lightlike.TemperleyLieb.Pentagon

/-!
# The recursion of the recoupling coefficient in the third block

The pentagon identity `pentagon` with a fourth block of one strand (`d = 1`) and no arc between the third
and the fourth block (`j = 0`) expresses the recoupling coefficient of the blocks `(a, b, c + 1)` through
those of `(a, b, c)` and of blocks whose third block has one strand: the right side of the pentagon collapses
to the single term `g' = d₀ + g₀` (`Fc_total`). This is the recursion by which `Fc` is identified with the
Kauffman–Lins coefficient (`KLCoef.lean`), the pivot `Fc (a+b-2e₀) c 1 d₀ g₀ 0 (d₀+g₀)` being a coefficient
with a third block of one strand.
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- **The recursion in the third block** (the pentagon with a fourth block of one strand and `j = 0`). -/
theorem Fc_third_rec [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e₀ d₀ g₀ m i : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : ∀ x, x ≤ a + b + c + 1 → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + 1 + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m)
    (h₀ : ValidA a b c 1 e₀ d₀ g₀) :
    ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        Fc q b c 1 f h 0 m * (Fc q a (b + c - 2 * f) 1 d' g₀ h i * Fc q a b c e₀ d₀ f d') =
      Fc q a b (c + 1) e₀ (d₀ + g₀) m i * Fc q (a + b - 2 * e₀) c 1 d₀ g₀ 0 (d₀ + g₀) := by
  have hP := pentagon q hδ a b c 1 e₀ d₀ g₀ 0 m i ha hb hc hd hq2 (Nat.zero_le _) (Nat.zero_le _) hmb
    (by omega) hia (by omega) h₀
  simp only [Nat.mul_zero, Nat.sub_zero] at hP
  rw [hP]
  obtain ⟨he, hd₀, hg₀, hg1⟩ := h₀
  refine sum_eq_single (d₀ + g₀) (fun g' _ hne => ?_) (fun hmem => ?_)
  · by_cases h1 : Fc q a b (c + 1) e₀ g' m i = 0
    · rw [h1, zero_mul]
    · obtain ⟨-, hg'⟩ := Fc_guard h1
      have h2 : Fc q (a + b - 2 * e₀) c 1 d₀ g₀ 0 g' = 0 := by
        by_contra h2
        have := Fc_total q hδ (a + b - 2 * e₀) c 1 d₀ g₀ 0 g' (by omega) (fun x hx => hd x (by omega))
          (Nat.zero_le _) (Nat.zero_le _) (hg'.trans (min_le_left _ _)) (by have := hg'.trans (min_le_right _ _); omega) h2
        omega
      rw [h2, mul_zero]
  · exfalso; apply hmem; rw [mem_range]; have := hd₀.trans (min_le_right _ _); omega

end Lightlike.TemperleyLieb
