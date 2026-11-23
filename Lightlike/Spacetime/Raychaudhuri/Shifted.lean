import Lightlike.Spacetime.RiccatiFocusing
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Focusing from a shifted start, and backward focusing (GE3, Tier 1)

`focusing` starts at parameter `0`. Here: the same statement starting at any `a` (`focusing_shifted`), and the
time-reversed statement: a congruence that is expanding at `s = 0` with `Θ' ≤ -Θ²/m` on `(a, 0]` cannot have been
defined for a past time longer than `m/Θ(0)` (`focusing_backward`): expanding congruences focus in the past.
-/

open Set Filter Topology

namespace Lightlike

/-- **Focusing from a shifted start**: if `Θ' ≤ -Θ²/m` on `[a, L)` and `Θ(a) < 0` then `L ≤ a + m/|Θ(a)|`. -/
theorem focusing_shifted {Θ Θ' : ℝ → ℝ} {a L m : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ico a L, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ico a L, Θ' s ≤ -(Θ s) ^ 2 / m)
    (h0 : Θ a < 0) : L ≤ a + m / |Θ a| := by
  have h := focusing (Θ := fun s => Θ (a + s)) (Θ' := fun s => Θ' (a + s)) (L := L - a) hm
    (fun s hs => HasDerivAt.comp_const_add a s (hd (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩))
    (fun s hs => hle (a + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩) (by simpa using h0)
  simp only [add_zero] at h
  linarith

/-- **Backward focusing**: if `Θ' ≤ -Θ²/m` on `(a, 0]` and `Θ(0) > 0` (expanding), then `-a ≤ m/Θ(0)`: the
congruence cannot extend to the past by more than `m/Θ(0)`. -/
theorem focusing_backward {Θ Θ' : ℝ → ℝ} {a m : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ioc a 0, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ioc a 0, Θ' s ≤ -(Θ s) ^ 2 / m)
    (h0 : 0 < Θ 0) : -a ≤ m / Θ 0 := by
  have h := focusing (Θ := fun s => -Θ (-s)) (Θ' := fun s => Θ' (-s)) (L := -a) hm
    (fun s hs => by
      have h1 := (hd (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).scomp s (hasDerivAt_neg s)
      have h2 := h1.neg
      convert h2 using 1
      · rfl
      · rw [neg_one_smul, neg_neg])
    (fun s hs => by
      have := hle (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simpa using this)
    (by simpa using h0)
  simpa [abs_of_pos h0] using h

end Lightlike
