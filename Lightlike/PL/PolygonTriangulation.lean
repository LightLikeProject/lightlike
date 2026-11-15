import Lightlike.PL.PolygonSplit
import Lightlike.PL.PolygonTriangle
import Lightlike.PL.SubdivSphere

/-!
# Triangulating a simple polygon

A **triangulation** of a simple polygon `q` is a finite family `T` of triangles, each spanned by
three vertices of `q`, whose faces form a geometric complex with underlying set the closed region
bounded by `q` (the inside together with the carrier), and in which every edge of `q` is a face.

The proof is by induction on the number of vertices: a triangle is its own triangulation, and a
polygon with at least four vertices splits along an interior diagonal into two smaller polygons
whose triangulations fit together along the diagonal.

## Main definitions

* `Lightlike.PL.Polygon.IsTriangulation`
-/

open Set Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

lemma space_closure (T : Finset (Finset E)) :
    (SComplex.closure T).space = ⋃ t ∈ T, convexHull ℝ (t : Set E) := by
  ext x
  simp only [mem_space, SComplex.mem_closure, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, ⟨t, ht, hst⟩, hx⟩
    exact ⟨t, ht, convexHull_mono (Finset.coe_subset.2 hst) hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ⟨t, ht, subset_rfl⟩, hx⟩

end SComplex

namespace Polygon

variable {n : ℕ}

/-- `T` is a **triangulation** of the polygon `q`: its triangles have three vertices among those
of `q`, their faces form a geometric complex whose underlying set is the closed region bounded by
`q`, and every edge of `q` is a face. -/
def IsTriangulation (q : Polygon n) (T : Finset (Finset (ℝ × ℝ))) : Prop :=
  (∀ t ∈ T, t.card = 3 ∧ (t : Set (ℝ × ℝ)) ⊆ Set.range q) ∧
    SComplex.IsGeom (SComplex.closure T) ∧
    (SComplex.closure T).space = q.inside ∪ q.carrier ∧
    ∀ i, ({q i, q (finRotate n i)} : Finset (ℝ × ℝ)) ∈ SComplex.closure T

/-- **A triangle is its own triangulation.** -/
theorem isTriangulation_triangle {q : Polygon 3} (hs : q.IsSimple) :
    ∃ T, IsTriangulation q T := by
  classical
  have hind := affineIndependent_of_isSimple hs
  have hinj : Function.Injective q := hind.injective
  set S : Finset (ℝ × ℝ) := Finset.univ.image q with hS
  have hSset : (S : Set (ℝ × ℝ)) = Set.range q := by simp [hS]
  refine ⟨{S}, ⟨fun t ht => ?_, ?_, ?_, fun i => ?_⟩⟩
  · rw [Finset.mem_singleton] at ht
    subst ht
    refine ⟨?_, hSset.le⟩
    rw [hS, Finset.card_image_of_injective _ hinj]; simp
  · rw [SComplex.closure_singleton]
    refine SComplex.isGeom_simplex ?_
    have := hind.range
    rwa [← hSset] at this
  · rw [SComplex.space_closure]
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    rw [hSset, inside_eq_interior_hull hs, carrier_eq_frontier_hull hs,
      ← closure_eq_interior_union_frontier]
    exact ((Set.finite_range q).isClosed_convexHull (𝕜 := ℝ)).closure_eq.symm
  · rw [SComplex.mem_closure]
    refine ⟨S, Finset.mem_singleton_self _, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hS]

end Polygon

end Lightlike.PL
