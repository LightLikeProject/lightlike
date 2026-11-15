import Mathlib
import Lightlike.Regge.CMS.Triangulation
import Lightlike.Regge.CMS.NonVacuity

/-!
# Non-vacuity of the triangulation-level convergence theorem (RC6b)

The four triangles `(0, wⱼ, wⱼ₊₁)` around the origin, with `w = starW h` (the neighbours
`(±h, 0)`, `(0, ±h)`), form a triangulation `starTri h` that satisfies every hypothesis of
`cms_convergence_triangulation` with the single vertex `V = {origin}`, for each `h ∈ (0, 1]`.
All four triangles have a corner outside `V`, so the region is empty and the bound is the
boundary-layer bound.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- Signs of the coordinates in the four quadrants. -/
def sgn0 : ZMod 4 → ℝ := ![1, -1, -1, 1]
/-- Signs of the second coordinate in the four quadrants. -/
def sgn1 : ZMod 4 → ℝ := ![1, 1, -1, -1]

/-- Vertex positions: the origin (`none`) and the four neighbours. -/
def starP (h : ℝ) : Option (ZMod 4) → Fin 2 → ℝ
  | none => 0
  | some j => starW h j

/-- Corners of the triangle `t`. -/
def starC (t : ZMod 4) : Fin 3 → Option (ZMod 4) := ![none, some t, some (t + 1)]

theorem cell_sign {h : ℝ} (hh : 0 ≤ h) (t : ZMod 4) {x : Fin 2 → ℝ}
    (hx : x ∈ cell (starP h) starC t) : 0 ≤ sgn0 t * x 0 ∧ 0 ≤ sgn1 t * x 1 := by
  obtain ⟨y, ⟨hy0, hy1, hy2⟩, rfl⟩ := hx
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases zmod4_cases t with rfl | rfl | rfl | rfl <;>
    simp [triMap, cell, starP, starC, starW, sgn0, sgn1, e0, e1, e2, e3] <;>
    constructor <;> nlinarith [mul_nonneg hh hy0, mul_nonneg hh hy1]

theorem star_disjoint {h : ℝ} (hh : 0 ≤ h) (t t' : ZMod 4) (hne : t ≠ t') :
    AEDisjoint volume (cell (starP h) starC t) (cell (starP h) starC t') := by
  have hsub : cell (starP h) starC t ∩ cell (starP h) starC t' ⊆
      {x | x 0 = 0} ∪ {x | x 1 = 0} := by
    rintro x ⟨hx, hx'⟩
    obtain ⟨a0, a1⟩ := cell_sign hh t hx
    obtain ⟨b0, b1⟩ := cell_sign hh t' hx'
    simp only [mem_union, mem_ofPred_eq]
    rcases zmod4_cases t with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases t' with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp [sgn0, sgn1] at a0 a1 b0 b1
       first | (left; linarith) | (right; linarith))
  have h0 : volume {x : Fin 2 → ℝ | x 0 = 0} = 0 := Measure.pi_hyperplane (fun _ => volume) 0 0
  have h1 : volume {x : Fin 2 → ℝ | x 1 = 0} = 0 := Measure.pi_hyperplane (fun _ => volume) 1 0
  exact measure_mono_null hsub (measure_union_null h0 h1)

theorem starC_inj (t : ZMod 4) : Function.Injective (starC t) := by
  revert t; decide

theorem cornersIn_star (t : ZMod 4) : cornersIn starC ({none} : Finset (Option (ZMod 4))) t = 1 := by
  revert t; decide

/-- **Non-vacuity.** The four-triangle star around the origin, for the flat metric. -/
theorem star_triangulation_bound :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → h ≤ 1 →
      |∑ v ∈ ({none} : Finset (Option (ZMod 4))), (fun _ : Fin 2 → ℝ => (1 : ℝ)) (starP h v) *
          (2 * π - ∑ j : ZMod 4, triAngle
            (dist (shearBy fun _ => (0 : ℝ)) univ (starP h v) (starP h (some j)) ^ 2)
            (dist (shearBy fun _ => (0 : ℝ)) univ (starP h v) (starP h (some (j + 1))) ^ 2)
            (dist (shearBy fun _ => (0 : ℝ)) univ (starP h (some j)) (starP h (some (j + 1))) ^ 2)) -
        ∫ x in ⋃ t ∈ Finset.univ.filter
            (fun t => cornersIn starC ({none} : Finset (Option (ZMod 4))) t = 3),
          cell (starP h) starC t,
          (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (scalarCurvature (shearBy fun _ => (0 : ℝ)) x / 2 *
            √((shearBy fun _ => (0 : ℝ)) x).det)| ≤ C * h := by
  have hg : IsRiemMetric (shearBy fun _ => (0 : ℝ)) univ := isRiemMetric_shearBy contDiff_const
  obtain ⟨C, h₀, hh₀, hmain⟩ := hg.cms_convergence_triangulation (K := Icc (-1 : Fin 2 → ℝ) 1)
    isCompact_Icc (subset_univ _) (ρ := 1) (N := 4) (M := 1) (m := 4) (by norm_num) one_pos
    (f := fun _ => 1) (Lf := 0) (LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp)
  refine ⟨C, h₀, hh₀, fun h hh hh0 hh1 => ?_⟩
  have hball : ∀ t, cell (starP h) starC t ⊆ Icc (-1 : Fin 2 → ℝ) 1 := by
    intro t
    refine (tri_subset_closedBall (q := 0) (h := h) ?_ ?_ ?_).trans ?_
    · simp [starP, starC, hh.le]
    · simp [starP, starC, dist_zero_right, starW_norm hh.le]
    · simp [starP, starC, dist_zero_right, starW_norm hh.le]
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hh.le] at hx
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> have := abs_le.1 ((Real.norm_eq_abs _).symm ▸ hx i) <;>
        simp <;> linarith [this.1, this.2]
  refine hmain (Option (ZMod 4)) (ZMod 4) {none} (fun _ => 4) (starP h) starC (fun _ j => some j)
    (fun _ t => t) h hh hh0 ?_ starC_inj (fun t t' hne => star_disjoint hh.le t t' hne) hball
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.card_singleton, Nat.cast_one]; nlinarith
  · intro t k
    simp only [starP, starC]
    fin_cases k <;> simp [dist_zero_right, starW_norm hh.le, hh.le]
  · intro v hv
    simp only [Finset.mem_singleton] at hv; subst hv
    exact ⟨fun a b hab => hab, fun t => ⟨fun _ => ⟨t, rfl⟩, fun _ => ⟨0, rfl⟩⟩⟩
  · intro v hv j; simp only [Finset.mem_singleton] at hv; subst hv; exact ⟨1, rfl⟩
  · intro v hv; simp only [Finset.mem_singleton] at hv; subst hv; simp [starP, mem_Icc]
  · intro v _; norm_num
  · intro v hv j; simp only [Finset.mem_singleton] at hv; subst hv; simp [starP, starW_norm hh.le]
  · intro v hv j; simp only [Finset.mem_singleton] at hv; subst hv; simp [starP, starW_det2]
  · intro v hv
    simp only [Finset.mem_singleton] at hv; subst hv
    simp only [starP, sub_zero]
    rw [Finset.sum_congr rfl fun j _ => starW_angle h hh j]; simp; ring
  · rw [show (Finset.univ.filter fun t => cornersIn starC ({none} : Finset (Option (ZMod 4))) t ≠ 3).card = 4 by
      simp only [cornersIn_star]; decide]
    push_cast; linarith

/-- **Trust check.** The triangle `(0,0), (2,0), (0,3)` has area `3`, and a formula without the
factor `1/2` (the parallelogram `|det2|`, here `6`) would give a different answer. -/
theorem volume_real_tri_example :
    volume.real (tri 0 ![2, 0] ![0, 3]) = 3 ∧ volume.real (tri 0 ![2, 0] ![0, 3]) ≠ 6 := by
  have : volume.real (tri 0 ![2, 0] ![0, 3]) = 3 := by
    rw [Measure.real, volume_tri, ENNReal.toReal_ofReal (by positivity)]
    simp [det2]
  exact ⟨this, by rw [this]; norm_num⟩

end Lightlike.CMS
