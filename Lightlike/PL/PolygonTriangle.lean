import Lightlike.PL.PolygonInside
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Simple triangles

A simple polygon with three vertices has affinely independent vertices: three collinear distinct
points have one between the other two, and that vertex then lies on two edges that meet only in
their shared endpoint. The vertices then form an affine basis of the plane, and in its barycentric
coordinates the carrier is the frontier, and the inside the interior, of the convex hull.

## Main results

* `Lightlike.PL.Polygon.affineIndependent_of_isSimple`
* `Lightlike.PL.Polygon.carrier_eq_frontier_hull`: the carrier is the frontier of the convex hull
* `Lightlike.PL.Polygon.inside_eq_interior_hull`: the inside is the interior of the convex hull
-/

open Set

namespace Lightlike.PL
namespace Polygon

/-- **The vertices of a simple triangle are affinely independent.** -/
theorem affineIndependent_of_isSimple {p : Polygon 3} (hs : p.IsSimple) :
    AffineIndependent ℝ p := by
  have e0 : finRotate 3 0 = 1 := rfl
  have e1 : finRotate 3 1 = 2 := rfl
  have e2 : finRotate 3 2 = 0 := rfl
  have hp : p = ![p 0, p 1, p 2] := by
    funext i; fin_cases i <;> rfl
  have c0 : p 0 ≠ p 1 := by simpa [e0] using hs.1 0
  have c1 : p 1 ≠ p 2 := by simpa [e1] using hs.1 1
  have c2 : p 2 ≠ p 0 := by simpa [e2] using hs.1 2
  have h01 := hs.2.2 0
  have h12 := hs.2.2 1
  have h20 := hs.2.2 2
  rw [e0] at h01
  rw [e1] at h12
  rw [e2] at h20
  have ed0 : p.edge 0 = segment ℝ (p 0) (p 1) := by simp [Polygon.edge, e0]
  have ed1 : p.edge 1 = segment ℝ (p 1) (p 2) := by simp [Polygon.edge, e1]
  have ed2 : p.edge 2 = segment ℝ (p 2) (p 0) := by simp [Polygon.edge, e2]
  rw [hp, affineIndependent_iff_not_collinear_set]
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · -- `p 1` lies between `p 0` and `p 2`: it is on edge 2 and is the start of edge 1
    have hm : p 1 ∈ p.edge 1 ∩ p.edge 2 :=
      ⟨ed1 ▸ left_mem_segment ℝ _ _, ed2 ▸ mem_segment_iff_wbtw.2 h.symm⟩
    rw [h12] at hm
    exact c1 hm
  · -- `p 2` lies between `p 1` and `p 0`: it is on edge 0 and is the end of edge 1
    have hm : p 2 ∈ p.edge 0 ∩ p.edge 1 :=
      ⟨ed0 ▸ mem_segment_iff_wbtw.2 h.symm, ed1 ▸ right_mem_segment ℝ _ _⟩
    rw [h01] at hm
    exact c1 hm.symm
  · -- `p 0` lies between `p 2` and `p 1`: it is on edge 1 and is the end of edge 2
    have hm : p 0 ∈ p.edge 1 ∩ p.edge 2 :=
      ⟨ed1 ▸ mem_segment_iff_wbtw.2 h.symm, ed2 ▸ right_mem_segment ℝ _ _⟩
    rw [h12] at hm
    exact c2 hm.symm

/-- **Trust check.** Three points on a line are not a simple triangle. -/
example : ¬ Polygon.IsSimple (n := 3) ![((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0)] := by
  intro hs
  have h := affineIndependent_of_isSimple hs
  rw [affineIndependent_iff_not_collinear_set] at h
  apply h
  rw [collinear_iff_of_mem (p₀ := ((0 : ℝ), (0 : ℝ))) (by simp)]
  refine ⟨(1, 0), ?_⟩
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨2, by simp⟩

/-- The affine basis given by the vertices of a simple triangle. -/
noncomputable def triBasis {p : Polygon 3} (hs : p.IsSimple) : AffineBasis (Fin 3) ℝ (ℝ × ℝ) :=
  ⟨p, affineIndependent_of_isSimple hs,
    (affineIndependent_of_isSimple hs).affineSpan_eq_top_iff_card_eq_finrank_add_one.2
      (by simp [Module.finrank_prod])⟩

/-- The basis vectors are the vertices. -/
lemma triBasis_apply {p : Polygon 3} (hs : p.IsSimple) (i : Fin 3) : triBasis hs i = p i := rfl

/-- The basis has the vertices as its range. -/
lemma range_triBasis {p : Polygon 3} (hs : p.IsSimple) : range (triBasis hs) = range p := rfl

/-- The convex hull of the vertices is where all barycentric coordinates are nonnegative. -/
lemma hull_eq {p : Polygon 3} (hs : p.IsSimple) :
    convexHull ℝ (range p) = {x | ∀ i, 0 ≤ (triBasis hs).coord i x} := by
  rw [← range_triBasis hs, (triBasis hs).convexHull_eq_nonneg_coord]

/-- The interior of the hull is where all barycentric coordinates are positive. -/
lemma interior_hull_eq {p : Polygon 3} (hs : p.IsSimple) :
    interior (convexHull ℝ (range p)) = {x | ∀ i, 0 < (triBasis hs).coord i x} := by
  rw [← range_triBasis hs]; exact (triBasis hs).interior_convexHull

/-- The frontier of the hull is where all coordinates are nonnegative and one vanishes. -/
lemma frontier_hull_eq {p : Polygon 3} (hs : p.IsSimple) :
    frontier (convexHull ℝ (range p)) =
      {x | (∀ i, 0 ≤ (triBasis hs).coord i x) ∧ ∃ i, (triBasis hs).coord i x = 0} := by
  have hk : IsCompact (convexHull ℝ (range p)) := (Set.finite_range p).isCompact_convexHull ℝ
  have hc : IsClosed (convexHull ℝ (range p)) := hk.isClosed
  rw [← closure_sdiff_interior, hc.closure_eq, interior_hull_eq hs, hull_eq hs]
  ext x
  simp only [mem_sdiff, mem_ofPred_eq, not_forall, not_lt]
  constructor
  · rintro ⟨h, i, hi⟩; exact ⟨h, i, le_antisymm hi (h i)⟩
  · rintro ⟨h, i, hi⟩; exact ⟨h, i, hi.le⟩

/-- Barycentric coordinates of a vertex. -/
lemma coord_vertex {p : Polygon 3} (hs : p.IsSimple) (i j : Fin 3) :
    (triBasis hs).coord i (p j) = if i = j then 1 else 0 :=
  (triBasis hs).coord_apply i j

/-- Each edge lies in the convex hull of the vertices. -/
lemma edge_subset_hull {p : Polygon 3} (i : Fin 3) : p.edge i ⊆ convexHull ℝ (range p) :=
  (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ⟨i, rfl⟩)
    (subset_convexHull ℝ _ ⟨_, rfl⟩)

/-- A coordinate that vanishes at both endpoints of an edge vanishes on it. -/
lemma coord_eq_zero_of_mem_edge {p : Polygon 3} (hs : p.IsSimple) (i k : Fin 3) (hk1 : k ≠ i)
    (hk2 : k ≠ finRotate 3 i) {x : ℝ × ℝ} (hx : x ∈ p.edge i) : (triBasis hs).coord k x = 0 := by
  have hcv : Convex ℝ {y : ℝ × ℝ | (triBasis hs).coord k y = 0} :=
    Convex.affine_preimage ((triBasis hs).coord k) (convex_singleton (0 : ℝ))
  refine (hcv.segment_subset ?_ ?_) hx
  · simp [coord_vertex, hk1]
  · show (triBasis hs).coord k (p (finRotate 3 i)) = 0
    rw [coord_vertex]
    exact ite_eq_right_iff.2 fun h => absurd h hk2

/-- The carrier of a simple triangle, in barycentric coordinates. -/
lemma carrier_eq_aux {p : Polygon 3} (hs : p.IsSimple) :
    p.carrier = {x | (∀ i, 0 ≤ (triBasis hs).coord i x) ∧ ∃ i, (triBasis hs).coord i x = 0} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    refine ⟨fun j => ?_, ?_⟩
    · have := edge_subset_hull i hi
      rw [hull_eq hs] at this
      exact this j
    · fin_cases i
      · exact ⟨2, coord_eq_zero_of_mem_edge hs 0 2 (by decide) (by decide) hi⟩
      · exact ⟨0, coord_eq_zero_of_mem_edge hs 1 0 (by decide) (by decide) hi⟩
      · exact ⟨1, coord_eq_zero_of_mem_edge hs 2 1 (by decide) (by decide) hi⟩
  · rintro ⟨h, k, hk⟩
    have hx := (triBasis hs).linear_combination_coord_eq_self x
    have h1 := (triBasis hs).sum_coord_apply_eq_one x
    rw [Fin.sum_univ_three] at hx h1
    simp only [triBasis_apply] at hx
    refine mem_iUnion.2 ?_
    fin_cases k
    · refine ⟨1, ?_⟩
      simp only [Fin.zero_eta] at hk
      rw [hk] at hx h1
      refine ⟨(triBasis hs).coord 1 x, (triBasis hs).coord 2 x, h 1, h 2, by linarith, ?_⟩
      simpa using hx
    · refine ⟨2, ?_⟩
      simp only [Fin.mk_one] at hk
      rw [hk] at hx h1
      refine ⟨(triBasis hs).coord 2 x, (triBasis hs).coord 0 x, h 2, h 0, by linarith, ?_⟩
      rw [add_comm]; simpa using hx
    · refine ⟨0, ?_⟩
      have hk' : (triBasis hs).coord 2 x = 0 := hk
      rw [hk'] at hx h1
      refine ⟨(triBasis hs).coord 0 x, (triBasis hs).coord 1 x, h 0, h 1, by linarith, ?_⟩
      simpa using hx

/-- **The carrier of a simple triangle is the frontier of its convex hull.** -/
theorem carrier_eq_frontier_hull {p : Polygon 3} (hs : p.IsSimple) :
    p.carrier = frontier (convexHull ℝ (range p)) := by
  rw [frontier_hull_eq hs]; exact carrier_eq_aux hs

/-- Every weight vector of sum one is the coordinate vector of a point. -/
lemma exists_point_coords {p : Polygon 3} (hs : p.IsSimple) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 1) : ∃ x : ℝ × ℝ, ∀ i, (triBasis hs).coord i x = w i :=
  ⟨Finset.univ.affineCombination ℝ (triBasis hs) w, fun i =>
    (triBasis hs).coord_apply_combination_of_mem (Finset.mem_univ i) hw⟩

/-- **The inside of a simple triangle is the interior of its convex hull.** The complement of the
hull is a union of three open half-planes that meet pairwise, hence preconnected and unbounded, and
the interior of the hull is convex; so `eq_inside_of_isBounded` applies. -/
theorem inside_eq_interior_hull {p : Polygon 3} (hs : p.IsSimple) :
    p.inside = interior (convexHull ℝ (range p)) := by
  set b := triBasis hs with hb
  let H : Fin 3 → Set (ℝ × ℝ) := fun i => {x | b.coord i x < 0}
  have hHc : ∀ i, Convex ℝ (H i) := fun i =>
    Convex.affine_preimage (b.coord i) (convex_Iio (0 : ℝ))
  have hHp : ∀ i, IsPreconnected (H i) := fun i => (hHc i).isPreconnected
  have hmeet : ∀ i j, i ≠ j → (H i ∩ H j).Nonempty := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ : ∃ k, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide
    obtain ⟨x, hx⟩ := exists_point_coords hs (fun l => if l = k then 3 else -1) (by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_three] <;> norm_num)
    refine ⟨x, ?_, ?_⟩
    · show b.coord i x < 0
      rw [hx]; simp [Ne.symm hki]
    · show b.coord j x < 0
      rw [hx]; simp [Ne.symm hkj]
  have hA : IsPreconnected (H 0 ∪ H 1 ∪ H 2) := by
    obtain ⟨y, hy0, hy1⟩ := hmeet 0 1 (by decide)
    obtain ⟨z, hz0, hz2⟩ := hmeet 0 2 (by decide)
    exact ((hHp 0).union y hy0 hy1 (hHp 1)).union z (Or.inl hz0) hz2 (hHp 2)
  have hI : IsPreconnected (interior (convexHull ℝ (range p))) :=
    (convex_convexHull ℝ _).interior.isPreconnected
  have hU : p.carrierᶜ = (H 0 ∪ H 1 ∪ H 2) ∪ interior (convexHull ℝ (range p)) := by
    rw [carrier_eq_aux hs, interior_hull_eq hs]
    ext x
    have e1 : ∀ P : Fin 3 → Prop, (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := fun P => by
      constructor
      · intro h; exact ⟨h 0, h 1, h 2⟩
      · rintro ⟨a, b, c⟩ i; fin_cases i <;> assumption
    have e2 : ∀ P : Fin 3 → Prop, (∃ i, P i) ↔ P 0 ∨ P 1 ∨ P 2 := fun P => by
      constructor
      · rintro ⟨i, h⟩; fin_cases i
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
    simp only [mem_compl_iff, mem_ofPred_eq, mem_union, H, e1, e2]
    generalize (triBasis hs).coord 0 x = a
    generalize (triBasis hs).coord 1 x = c1
    generalize (triBasis hs).coord 2 x = c2
    rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy c1 0 with hb | hb | hb <;>
      rcases lt_trichotomy c2 0 with hc | hc | hc <;>
      first
        | (simp [ha, hb, hc, not_le.2, not_lt.2, le_of_lt]; done)
        | (simp [ha, hb, hc, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, le_of_lt ha, le_of_lt hb, le_of_lt hc])
  have hAb : ¬ Bornology.IsBounded (H 0 ∪ H 1 ∪ H 2) := by
    intro hb'
    have hk : IsCompact (convexHull ℝ (range p)) := (Set.finite_range p).isCompact_convexHull ℝ
    have : Bornology.IsBounded (univ : Set (ℝ × ℝ)) := by
      refine (hb'.union hk.isBounded).subset ?_
      intro x _
      by_cases hx : x ∈ convexHull ℝ (range p)
      · exact Or.inr hx
      · left
        rw [hull_eq hs] at hx
        simp only [mem_ofPred_eq, not_forall, not_le] at hx
        obtain ⟨i, hi⟩ := hx
        fin_cases i
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr hi)
        · exact Or.inr hi
    exact NormedSpace.unbounded_univ ℝ (ℝ × ℝ) this
  exact eq_inside_of_isBounded hs hU hA hI hAb |>.symm

end Polygon
end Lightlike.PL
