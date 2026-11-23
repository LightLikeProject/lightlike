import Lightlike.Spacetime.RiccatiFocusing
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Focusing with twist: a positive result (GE3, Tier 1)

`Twist.lean` shows that the twisted Raychaudhuri inequality `Θ' ≤ -Θ²/m + ω²` has solutions defined for all time
when `Θ` is a small negative constant. Here is the complementary positive result: if the congruence is
*sufficiently* converging at the start, `Θ(0) < -b` with `b² = m ω²`, the twist cannot prevent focusing, and
the focal time satisfies `L ≤ m/(-b - Θ(0))`. The proof: `Ψ = Θ + b` satisfies `Ψ' ≤ -Ψ²/m` and stays negative.
-/

open Set Filter Topology

namespace Lightlike

/-- **Focusing with twist.** Let `b ≥ 0` and `Θ' ≤ -(Θ² - b²)/m` on `[0, L)` (for `b = √m·ω` this is
`Θ' ≤ -Θ²/m + ω²`). If `Θ(0) < -b` then `L ≤ m/(-b - Θ(0))`. -/
theorem focusing_twisted {Θ Θ' : ℝ → ℝ} {L m b : ℝ} (hm : 0 < m) (hb : 0 ≤ b)
    (hd : ∀ s ∈ Ico 0 L, HasDerivAt Θ (Θ' s) s)
    (hle : ∀ s ∈ Ico 0 L, Θ' s ≤ -((Θ s) ^ 2 - b ^ 2) / m)
    (h0 : Θ 0 < -b) : L ≤ m / (-b - Θ 0) := by
  have hpos : 0 < -b - Θ 0 := by linarith
  -- Ψ = Θ + b stays below Ψ 0 < 0
  have hbd : ∀ s ∈ Ico 0 L, Θ s + b ≤ Θ 0 + b := by
    intro s hs
    have hcont : ContinuousOn (fun t => Θ t + b) (Icc 0 s) := fun t ht =>
      ((hd t ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩).continuousAt.add continuousAt_const).continuousWithinAt
    have key := image_le_of_deriv_right_lt_deriv_boundary' (f := fun t => Θ t + b) (f' := Θ')
      (a := 0) (b := s) (B := fun _ => Θ 0 + b) (B' := fun _ => (0:ℝ)) hcont
      (fun t ht => ((hd t ⟨ht.1, lt_of_lt_of_le ht.2 hs.2.le⟩).add_const b).hasDerivWithinAt)
      le_rfl continuousOn_const (fun t _ => hasDerivAt_const t _ |>.hasDerivWithinAt)
      (fun t ht heq => by
        have h1 := hle t ⟨ht.1, lt_of_lt_of_le ht.2 hs.2.le⟩
        have hΘ : Θ t = Θ 0 := by simpa using heq
        rw [hΘ] at h1
        have h2 : -((Θ 0) ^ 2 - b ^ 2) / m < 0 := by
          apply div_neg_of_neg_of_pos _ hm
          nlinarith
        linarith)
    exact key ⟨hs.1, le_rfl⟩
  have h := focusing (Θ := fun s => Θ s + b) (Θ' := Θ') (L := L) hm
    (fun s hs => (hd s hs).add_const b)
    (fun s hs => by
      have h1 := hle s hs
      have h2 := hbd s hs
      have h3 : Θ s + b ≤ Θ 0 + b := h2
      have h4 : Θ s + b < 0 := by linarith
      have : -((Θ s) ^ 2 - b ^ 2) / m ≤ -(Θ s + b) ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hm.le
        nlinarith
      exact h1.trans this)
    (by simpa using (by linarith : Θ 0 + b < 0))
  have habs : |Θ 0 + b| = -b - Θ 0 := by
    rw [abs_of_neg (by linarith)]; ring
  simpa [habs] using h

end Lightlike
