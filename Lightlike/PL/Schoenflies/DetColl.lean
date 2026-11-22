import Mathlib
import Lightlike.PL.Schoenflies.TriMap
import Lightlike.PL.PolygonTriangle

/-!
# Orientation determinant of a simple triangle

Piece 11 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  Three points with
vanishing orientation determinant `det3` are collinear; hence the vertices of a simple triangle
(which are affinely independent) have `det3 ≠ 0`, so the triangle map `triMap` is available.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- Vanishing orientation determinant implies collinearity. -/
lemma collinear_of_det3_eq_zero {a b c : ℝ × ℝ} (h : det3 a b c = 0) :
    Collinear ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  by_cases hab : b = a
  · subst hab
    have : ({b, b, c} : Set (ℝ × ℝ)) = {b, c} := by simp
    rw [this]; exact collinear_pair ℝ b c
  · have hw : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
      intro h0
      apply hab
      have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
      have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
      exact Prod.ext (by linarith) (by linarith)
    rw [collinear_iff_of_mem (p₀ := a) (by simp)]
    refine ⟨b - a, ?_⟩
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨((x.1 - a.1) * (b.1 - a.1) + (x.2 - a.2) * (b.2 - a.2)) /
        ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2), ?_⟩
      simp only [det3, cross, Prod.fst_sub, Prod.snd_sub] at h
      ext
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
        field_simp
        linear_combination (-(b.2 - a.2)) * h
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        field_simp
        linear_combination ((b.1 - a.1)) * h

/-- **The vertices of a simple triangle have nonzero orientation determinant.** -/
lemma det3_ne_zero_of_isSimple {p : Polygon 3} (hs : p.IsSimple) :
    det3 (p 0) (p 1) (p 2) ≠ 0 := by
  intro h
  have hind := Polygon.affineIndependent_of_isSimple hs
  have hp : p = ![p 0, p 1, p 2] := by
    funext i; fin_cases i <;> rfl
  rw [hp, affineIndependent_iff_not_collinear_set] at hind
  exact hind (collinear_of_det3_eq_zero h)

/-- Non-vacuity: the standard triangle has nonzero determinant, a collinear triple has zero. -/
example : det3 (0, 0) (1, 0) (0, 1) ≠ 0 ∧ det3 (0, 0) (1, 1) (2, 2) = 0 := by
  constructor <;> simp [det3, cross]

end Lightlike.PL.Schoenflies
