import Mathlib
import Lightlike.Regge.CMS.Final
import Lightlike.Regge.Geodesic.Tests

/-!
# Non-vacuity of the weighted deficit convergence (RC6b)

A flat chart with one vertex at the origin, whose star has the four neighbours `(±h, 0)`,
`(0, ±h)`, satisfies every hypothesis of `IsRiemMetric.cms_convergence` for each `h ∈ (0, 1]`:
`ρ = 1`, `θ = π/2`, `N = 4`, `M = 1`; the cell is the rectangle `[-h, h] × [-h/2, h/2]` of area
`2 h² = ½ ∑ⱼ det2`, which is its own boundary layer (the region is empty), of area `2 h² ≤ 2 h`.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- The four neighbours `(h, 0), (0, h), (-h, 0), (0, -h)`, cyclically. -/
def starW (h : ℝ) : ZMod 4 → Fin 2 → ℝ :=
  ![![h, 0], ![0, h], ![-h, 0], ![0, -h]]

theorem zmod4_cases (j : ZMod 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide

theorem starW_norm {h : ℝ} (hh : 0 ≤ h) (j : ZMod 4) : ‖starW h j‖ ≤ h := by
  rw [pi_norm_le_iff_of_nonneg hh]
  intro i
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp [starW, abs_of_nonneg hh, hh]

theorem starW_det2 (h : ℝ) (j : ZMod 4) : det2 (starW h j) (starW h (j + 1)) = h ^ 2 := by
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;> simp [det2, starW, e0, e1, e2, e3] <;> ring

theorem starW_angle (h : ℝ) (hh : 0 < h) (j : ZMod 4) :
    InnerProductGeometry.angle (toC (starW h j)) (toC (starW h (j + 1))) = π / 2 := by
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    simp [toC, starW, Complex.inner, e0, e1, e2, e3]

/-- The cell: the rectangle `[-h, h] × [-h/2, h/2]`. -/
def starCell (h : ℝ) : Set (Fin 2 → ℝ) := Icc ![-h, -h / 2] ![h, h / 2]

theorem starCell_volume {h : ℝ} (hh : 0 ≤ h) : volume.real (starCell h) = 2 * h ^ 2 := by
  unfold starCell
  rw [Measure.real, Real.volume_Icc_pi, ENNReal.toReal_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ENNReal.toReal_ofReal_eq_iff]
  rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

theorem starCell_subset {h : ℝ} (hh : 0 ≤ h) (h1 : h ≤ 1) : starCell h ⊆ Icc (-1 : Fin 2 → ℝ) 1 := by
  intro x hx
  simp only [starCell, mem_Icc, Pi.le_def] at hx ⊢
  obtain ⟨hl, hu⟩ := hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := hl i; fin_cases i <;> simp at this ⊢ <;> linarith
  · have := hu i; fin_cases i <;> simp at this ⊢ <;> linarith

theorem starCell_dist {h : ℝ} (hh : 0 ≤ h) {x : Fin 2 → ℝ} (hx : x ∈ starCell h) :
    dist x 0 ≤ h := by
  rw [dist_zero_right]
  simp only [starCell, mem_Icc, Pi.le_def] at hx
  rw [pi_norm_le_iff_of_nonneg hh]
  intro k
  rw [Real.norm_eq_abs, abs_le]
  obtain ⟨hl, hu⟩ := hx
  have := hl k; have := hu k
  constructor <;> fin_cases k <;> simp at * <;> linarith

/-- **Non-vacuity.** The single flat star satisfies every hypothesis of `cms_convergence`, so the
theorem applies to it: for the weight `f = 1`, the deficit is at most `C h`. -/
theorem single_star_bound :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → h ≤ 1 →
      |∑ _i ∈ (Finset.univ : Finset Unit), 1 * (2 * π - ∑ j : ZMod 4,
          triAngle (dist (shearBy (fun _ => 0)) univ 0 (0 + starW h j) ^ 2)
            (dist (shearBy (fun _ => 0)) univ 0 (0 + starW h (j + 1)) ^ 2)
            (dist (shearBy (fun _ => 0)) univ (0 + starW h j) (0 + starW h (j + 1)) ^ 2)) -
        ∫ x in (∅ : Set (Fin 2 → ℝ)), (fun _ => (1 : ℝ)) x *
          (scalarCurvature (shearBy (fun _ => 0)) x / 2 *
            √((shearBy (fun _ => 0) x).det))| ≤ C * h := by
  have hg : IsRiemMetric (shearBy (fun _ => 0)) univ :=
    isRiemMetric_shearBy contDiff_const
  obtain ⟨C, h₀, hh₀, hmain⟩ := hg.cms_convergence (K := Icc (-1 : Fin 2 → ℝ) 1) isCompact_Icc
    (subset_univ _) (ρ := 1) (N := 4) (M := 1) (b := 2) (by norm_num) one_pos
    (f := fun _ => 1) (Lf := 0)
    (LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp)
  refine ⟨C, h₀, hh₀, fun h hh hh0 hh1 => ?_⟩
  have hcell := starCell_subset hh.le hh1
  refine hmain Unit Finset.univ (fun _ => 4) (fun _ => 0) (fun _ => starW h) (fun _ => starCell h)
    ∅ (starCell h) h hh hh0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.card_univ, Fintype.card_unit, Nat.cast_one]; nlinarith
  · intro i _; simp [mem_Icc, Pi.le_def]
  · intro i _; simp
  · intro i _ j; exact starW_norm hh.le j
  · intro i _ j; rw [starW_det2]; simp
  · intro i _
    rw [Finset.sum_congr rfl fun j _ => starW_angle h hh j]
    simp; ring
  · intro i _; exact measurableSet_Icc
  · intro i _; exact hcell
  · intro i _ x hx; exact starCell_dist hh.le hx
  · intro i _
    rw [starCell_volume hh.le, Finset.sum_congr rfl fun j _ => starW_det2 h j]
    simp; ring
  · exact MeasurableSet.empty
  · exact empty_subset _
  · exact measurableSet_Icc
  · exact hcell
  · rw [starCell_volume hh.le]; nlinarith
  · exact Filter.Eventually.of_forall fun x => by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      by_cases hx : x ∈ starCell h <;> simp [hx]
  · exact Filter.Eventually.of_forall fun x hx => by
      simp only [Finset.univ_unique, Finset.sum_singleton, Set.indicator_empty]
      rw [Set.indicator_of_notMem hx]; simp

end Lightlike.CMS
