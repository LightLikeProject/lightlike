import Mathlib
import Lightlike.PL.Schoenflies.InsideSubset
import Lightlike.PL.JordanComponents

/-!
# The inside of a polygon lies in any sqBox that contains its carrier

Row G3-188 (PL5), ring cells.  For a closed square `sqBox c R = {z | |z₁ - c₁| ≤ R, |z₂ - c₂| ≤ R}` the complement is
connected and unbounded, so the inside of a polygon with carrier in the sqBox lies in the sqBox
(`inside_subset_sqBox`).  Used to see that a polygon of small diameter cannot enclose a large connected set.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- The closed square of half-side `R` about `c`. -/
def sqBox (c : ℝ × ℝ) (R : ℝ) : Set (ℝ × ℝ) := {z | |z.1 - c.1| ≤ R ∧ |z.2 - c.2| ≤ R}

lemma isPreconnected_compl_sqBox (c : ℝ × ℝ) (R : ℝ) : IsPreconnected (sqBox c R)ᶜ := by
  have h := (isPreconnected_outside R).image (fun z : ℝ × ℝ => z + c) (by fun_prop)
  convert h using 1
  ext z
  simp only [sqBox, mem_compl_iff, mem_setOf_eq, mem_image, squareOutside, mem_union, not_and_or, not_le]
  constructor
  · intro hz
    refine ⟨z - c, ?_, by simp⟩
    simp only [Prod.fst_sub, Prod.snd_sub, mem_setOf_eq]
    rcases hz with (h | h)
    · rw [lt_abs] at h
      rcases h with h | h
      · exact Or.inl (Or.inl (Or.inl (by linarith)))
      · exact Or.inl (Or.inr (by linarith))
    · rw [lt_abs] at h
      rcases h with h | h
      · exact Or.inl (Or.inl (Or.inr (by linarith)))
      · exact Or.inr (by linarith)
  · rintro ⟨x, hx, rfl⟩
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_right, mem_setOf_eq] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact Or.inl (lt_abs.2 (Or.inl h))
    · exact Or.inr (lt_abs.2 (Or.inl h))
    · exact Or.inl (lt_abs.2 (Or.inr (by linarith)))
    · exact Or.inr (lt_abs.2 (Or.inr (by linarith)))

lemma not_isBounded_compl_sqBox (c : ℝ × ℝ) (R : ℝ) : ¬ Bornology.IsBounded (sqBox c R)ᶜ := by
  intro hb
  have hb' : Bornology.IsBounded (sqBox c R) := by
    refine (Metric.isBounded_closedBall (x := c) (r := R)).subset ?_
    intro z hz
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
    exact hz
  have : Bornology.IsBounded (univ : Set (ℝ × ℝ)) := by
    have := hb.union hb'
    simpa using this
  exact NormedSpace.unbounded_univ ℝ (ℝ × ℝ) this

/-- **The inside of a polygon lies in any square that contains its carrier.** -/
theorem inside_subset_sqBox {n : ℕ} (p : Polygon n) {c : ℝ × ℝ} {R : ℝ} (hcar : p.carrier ⊆ sqBox c R) :
    p.inside ⊆ sqBox c R := fun z hz => mem_of_parity_eq_one p hcar (isPreconnected_compl_sqBox c R)
  (not_isBounded_compl_sqBox c R) hz.2

end Lightlike.PL.Schoenflies
