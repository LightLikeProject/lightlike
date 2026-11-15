import Mathlib
import Lightlike.Regge.CMS.PerTriangle

/-!
# The area of a triangle in the plane (RC6b)

The triangle with vertices `a, b, c : Fin 2 → ℝ` is the convex hull `tri a b c`. Its Lebesgue
measure is `|det2 (b - a) (c - a)| / 2`. The proof maps the standard simplex `simplex2` (measure
`1/2`, by integrating the slices) by an affine map.
-/

open MeasureTheory Set

namespace Lightlike.CMS

/-- The standard triangle `{x | 0 ≤ x₀, 0 ≤ x₁, x₀ + x₁ ≤ 1}`. -/
def simplex2 : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

theorem measurableSet_simplex2 : MeasurableSet simplex2 := by
  have : simplex2 = (fun x : Fin 2 → ℝ => x 0) ⁻¹' Ici 0 ∩ (fun x : Fin 2 → ℝ => x 1) ⁻¹' Ici 0 ∩
      {x | x 0 + x 1 ≤ 1} := by
    ext x; simp [simplex2, and_assoc]
  rw [this]
  refine ((measurableSet_Ici.preimage (measurable_pi_apply 0)).inter
    (measurableSet_Ici.preimage (measurable_pi_apply 1))).inter ?_
  exact measurableSet_le ((measurable_pi_apply 0).add (measurable_pi_apply 1)) measurable_const

theorem volume_simplex2 : volume simplex2 = ENNReal.ofReal (1 / 2) := by
  have hmp := MeasureTheory.volume_preserving_finTwoArrow ℝ
  set D : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} with hD
  have hpre : simplex2 = (MeasurableEquiv.finTwoArrow (α := ℝ)) ⁻¹' D := rfl
  have hDm : MeasurableSet D := by
    have : D = {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p | 0 ≤ p.2} ∩ {p | p.1 + p.2 ≤ 1} := by
      ext p; simp [hD, and_assoc]
    rw [this]
    exact ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const)
  rw [hpre, hmp.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply hDm]
  have hslice : ∀ x : ℝ, volume (Prod.mk x ⁻¹' D) =
      (Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have : Prod.mk x ⁻¹' D = Icc 0 (1 - x) := by
        ext y; simp only [hD, mem_preimage, mem_ofPred_eq, mem_Icc]; constructor
        · intro h; exact ⟨h.2.1, by linarith [h.2.2]⟩
        · intro h; exact ⟨hx.1, h.1, by linarith [h.2]⟩
      rw [this, Real.volume_Icc, indicator_of_mem hx]; simp
    · have : Prod.mk x ⁻¹' D = ∅ := by
        ext y
        simp only [hD, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro h
        exact hx ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      rw [this, indicator_of_notMem hx]; simp
  simp_rw [hslice]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    norm_num
  · exact (continuous_const.sub continuous_id).integrableOn_Icc
  · exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by simp [hx.2]

/-- The affine map sending the standard triangle to the triangle `a b c`. -/
def triMap (a b c : Fin 2 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ := a + (x 0) • (b - a) + (x 1) • (c - a)

/-- The triangle with vertices `a`, `b`, `c`. -/
def tri (a b c : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := triMap a b c '' simplex2

theorem triMap_eq (a b c : Fin 2 → ℝ) :
    triMap a b c = (fun y => a + y) ∘ Matrix.toLin' !![(b - a) 0, (c - a) 0; (b - a) 1, (c - a) 1] := by
  funext x
  ext i
  fin_cases i <;> simp [triMap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem volume_tri (a b c : Fin 2 → ℝ) :
    volume (tri a b c) = ENNReal.ofReal (|det2 (b - a) (c - a)| / 2) := by
  unfold tri
  rw [triMap_eq, Set.image_comp, Set.image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_fin_two_of, volume_simplex2,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [det2]
  rw [show (b - a) 0 * (c - a) 1 - (c - a) 0 * (b - a) 1 = (b - a) 0 * (c - a) 1 - (b - a) 1 * (c - a) 0 by ring]
  ring

theorem convex_simplex2 : Convex ℝ simplex2 := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · positivity
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hx2 hs, mul_le_mul_of_nonneg_left hy2 ht]

theorem convex_tri (a b c : Fin 2 → ℝ) : Convex ℝ (tri a b c) := by
  unfold tri
  rw [triMap_eq, Set.image_comp]
  exact (convex_simplex2.linear_image _).translate a

/-- The triangle is the convex hull of its vertices. -/
theorem tri_eq_convexHull (a b c : Fin 2 → ℝ) : tri a b c = convexHull ℝ {a, b, c} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, ⟨h0, h1, h2⟩, rfl⟩
    have := (convex_convexHull ℝ ({a, b, c} : Set (Fin 2 → ℝ))).sum_mem (t := Finset.univ)
      (w := ![1 - x 0 - x 1, x 0, x 1]) (z := ![a, b, c])
      (by intro i _; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (by intro i _; fin_cases i <;> simp <;> exact subset_convexHull ℝ _ (by simp))
    convert this using 1
    simp [Fin.sum_univ_three, triMap]
    ext i; simp; ring
  · apply convexHull_min _ (convex_tri a b c)
    intro p hp
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, ⟨le_refl _, le_refl _, by simp⟩, by simp [triMap]⟩
    · exact ⟨![1, 0], ⟨by simp, by simp, by simp⟩, by ext i; simp [triMap]⟩
    · exact ⟨![0, 1], ⟨by simp, by simp, by simp⟩, by ext i; simp [triMap]⟩

theorem measurableSet_tri (a b c : Fin 2 → ℝ) : MeasurableSet (tri a b c) := by
  rw [tri_eq_convexHull]
  exact ((Set.toFinite ({a, b, c} : Set (Fin 2 → ℝ))).isCompact_convexHull ℝ).isClosed.measurableSet

end Lightlike.CMS
