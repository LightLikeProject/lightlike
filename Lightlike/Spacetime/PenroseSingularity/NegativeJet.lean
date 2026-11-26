import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# A function with vanishing first jet and negative second derivative is negative (G1-012, step D4)
-/

open Set Filter Topology

namespace Lightlike.Penrose

/-- If `f 0 = 0`, `f' 0 = 0` and `f'' < 0` near `0`, then `f s < 0` for `s ≠ 0` near `0`. -/
theorem neg_of_second_neg {f f' f'' : ℝ → ℝ} {δ : ℝ}
    (hf : ∀ r ∈ Ioo (-δ) δ, HasDerivAt f (f' r) r) (hf' : ∀ r ∈ Ioo (-δ) δ, HasDerivAt f' (f'' r) r)
    (hneg : ∀ r ∈ Ioo (-δ) δ, f'' r < 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (hδ : 0 < δ) :
    ∀ s ∈ Ioo (-δ) δ, s ≠ 0 → f s < 0 := by
  have hcont' : ContinuousOn f' (Ioo (-δ) δ) := fun r hr => (hf' r hr).continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Ioo (-δ) δ) := fun r hr => (hf r hr).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f' (Ioo (-δ) δ) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont' fun r hr => ?_
    rw [interior_Ioo] at hr
    rw [(hf' r hr).deriv]; exact hneg r hr
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  intro s hs hs0
  rcases lt_or_gt_of_ne hs0 with hlt | hgt
  · -- `s < 0`: `f' > 0` on `(s, 0)`, so `f` is strictly increasing on `[s, 0]`
    have hpos : ∀ r ∈ Ioo s 0, 0 < f' r := fun r hr => by
      have := hanti ⟨by linarith [hs.1, hr.1], by linarith [hr.2, hδ]⟩ h0mem hr.2
      rw [h0'] at this; exact this
    have hmono : StrictMonoOn f (Icc s 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont.mono fun r hr => ⟨by linarith [hs.1, hr.1], by linarith [hr.2, hδ]⟩) fun r hr => ?_
      rw [interior_Icc] at hr
      rw [(hf r ⟨by linarith [hs.1, hr.1], by linarith [hr.2, hδ]⟩).deriv]; exact hpos r hr
    have := hmono ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    rw [h0] at this; exact this
  · have hneg' : ∀ r ∈ Ioo 0 s, f' r < 0 := fun r hr => by
      have := hanti h0mem ⟨by linarith [hr.1, hδ], by linarith [hr.2, hs.2]⟩ hr.1
      rw [h0'] at this; exact this
    have hmono : StrictAntiOn f (Icc 0 s) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (hcont.mono fun r hr => ⟨by linarith [hr.1, hδ], by linarith [hr.2, hs.2]⟩) fun r hr => ?_
      rw [interior_Icc] at hr
      rw [(hf r ⟨by linarith [hr.1, hδ], by linarith [hr.2, hs.2]⟩).deriv]; exact hneg' r hr
    have := hmono ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt
    rw [h0] at this; exact this

end Lightlike.Penrose
