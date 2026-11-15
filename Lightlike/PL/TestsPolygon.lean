import Lightlike.PL.PolygonJordan
import Lightlike.PL.PolygonTriangulation

/-!
# Checks of the polygonal Jordan theorem

* The triangle with vertices `(0,0)`, `(1,0)`, `(0,1)` is a simple polygon, so the theorem applies
  to it (non-vacuity of the hypothesis).
* A polygon with a repeated vertex is not simple (the edge is degenerate).
* The bow tie `(0,0)`, `(1,1)`, `(1,0)`, `(0,1)` is not simple: its edges `0` and `2` cross at
  `(1/2, 1/2)`. The theorem needs the hypothesis, since a figure eight has three complementary
  regions.
-/

open Set

namespace Lightlike.PL
namespace Polygon

/-- The triangle with vertices `(0,0)`, `(1,0)`, `(0,1)`. -/
def triangle : Polygon 3 := ![(0, 0), (1, 0), (0, 1)]

private lemma rot0 : finRotate 3 0 = 1 := by decide
private lemma rot1 : finRotate 3 1 = 2 := by decide
private lemma rot2 : finRotate 3 2 = 0 := by decide

private lemma meet0 {z : ℝ × ℝ} (h1 : z ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0))
    (h2 : z ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (0, 1)) : z = (1, 0) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h1
  obtain ⟨c, d, hc, hd, hcd, h⟩ := h2
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp at e1 e2 ⊢
  linarith

private lemma meet1 {z : ℝ × ℝ} (h1 : z ∈ segment ℝ ((1 : ℝ), (0 : ℝ)) (0, 1))
    (h2 : z ∈ segment ℝ ((0 : ℝ), (1 : ℝ)) (0, 0)) : z = (0, 1) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h1
  obtain ⟨c, d, hc, hd, hcd, h⟩ := h2
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp at e1 e2 ⊢
  constructor <;> linarith

private lemma meet2 {z : ℝ × ℝ} (h1 : z ∈ segment ℝ ((0 : ℝ), (1 : ℝ)) (0, 0))
    (h2 : z ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (1, 0)) : z = (0, 0) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := h1
  obtain ⟨c, d, hc, hd, hcd, h⟩ := h2
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp at e1 e2 ⊢
  linarith

/-- **Non-vacuity.** The triangle is a simple polygon. -/
theorem triangle_isSimple : triangle.IsSimple := by
  refine ⟨fun i => ?_, fun i j hij h1 h2 => ?_, fun i => ?_⟩
  · fin_cases i <;> simp [triangle, Prod.ext_iff]
  · exfalso
    revert i j
    decide
  · fin_cases i
    · have e : (triangle.edge 0 : Set (ℝ × ℝ)) = segment ℝ ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
        show segment ℝ (triangle 0) (triangle (finRotate 3 0)) = _
        rw [rot0]; rfl
      have e' : (triangle.edge (finRotate 3 0) : Set (ℝ × ℝ)) = segment ℝ ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
        show segment ℝ (triangle (finRotate 3 0)) (triangle (finRotate 3 (finRotate 3 0))) = _
        rw [rot0, rot1]; rfl
      show triangle.edge 0 ∩ triangle.edge (finRotate 3 0) = {triangle (finRotate 3 0)}
      rw [e, e', rot0]
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨?_, ?_⟩, fun z hz => meet0 hz.1 hz.2⟩
      · exact right_mem_segment _ _ _
      · exact left_mem_segment _ _ _
    · have e : (triangle.edge 1 : Set (ℝ × ℝ)) = segment ℝ ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
        show segment ℝ (triangle 1) (triangle (finRotate 3 1)) = _
        rw [rot1]; rfl
      have e' : (triangle.edge (finRotate 3 1) : Set (ℝ × ℝ)) = segment ℝ ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (0 : ℝ)) := by
        show segment ℝ (triangle (finRotate 3 1)) (triangle (finRotate 3 (finRotate 3 1))) = _
        rw [rot1, rot2]; rfl
      show triangle.edge 1 ∩ triangle.edge (finRotate 3 1) = {triangle (finRotate 3 1)}
      rw [e, e', rot1]
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨?_, ?_⟩, fun z hz => meet1 hz.1 hz.2⟩
      · exact right_mem_segment _ _ _
      · exact left_mem_segment _ _ _
    · have e : (triangle.edge 2 : Set (ℝ × ℝ)) = segment ℝ ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (0 : ℝ)) := by
        show segment ℝ (triangle 2) (triangle (finRotate 3 2)) = _
        rw [rot2]; rfl
      have e' : (triangle.edge (finRotate 3 2) : Set (ℝ × ℝ)) = segment ℝ ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
        show segment ℝ (triangle (finRotate 3 2)) (triangle (finRotate 3 (finRotate 3 2))) = _
        rw [rot2, rot0]; rfl
      show triangle.edge 2 ∩ triangle.edge (finRotate 3 2) = {triangle (finRotate 3 2)}
      rw [e, e', rot2]
      refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨?_, ?_⟩, fun z hz => meet2 hz.1 hz.2⟩
      · exact right_mem_segment _ _ _
      · exact left_mem_segment _ _ _

/-- **Wrong-model check.** A polygon whose first two vertices coincide is not simple. -/
theorem not_isSimple_degenerate : ¬ Polygon.IsSimple (![(0, 0), (0, 0), (1, 0)] : Polygon 3) := by
  intro h
  exact h.1 0 (by simp [show finRotate 3 0 = 1 from by decide])

/-- The bow tie `(0,0)`, `(1,1)`, `(1,0)`, `(0,1)`. -/
def bowtie : Polygon 4 := ![(0, 0), (1, 1), (1, 0), (0, 1)]

/-- **Wrong-model check.** The bow tie is not simple: its edges `0` and `2` meet at
`(1/2, 1/2)`. -/
theorem not_isSimple_bowtie : ¬ bowtie.IsSimple := by
  intro h
  have hd := h.2.1 0 2 (by decide) (by decide) (by decide)
  have h0 : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ bowtie.edge 0 :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      simp [bowtie, show finRotate 4 0 = 1 from by decide]⟩
  have h2 : ((1 / 2 : ℝ), (1 / 2 : ℝ)) ∈ bowtie.edge 2 :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      simp [bowtie, show finRotate 4 2 = 3 from by decide]⟩
  exact Set.disjoint_left.1 hd h0 h2

/-- **Non-vacuity of the triangulation theorem.** The theorem applies to the triangle
`(0,0)`, `(1,0)`, `(0,1)`. -/
theorem triangle_triangulation : ∃ T, IsTriangulation triangle T :=
  exists_triangulation 3 triangle le_rfl triangle_isSimple

end Polygon
end Lightlike.PL
