import Lightlike.PL.VertexRelabel
import Lightlike.PL.TestsPachner

/-!
# Trust checks for relabellings

* The transport theorem relates complexes on different vertex types: the boundaries of the
  triangles on `{0, 1, 2}` and on `{5, 6, 7}` in `ℕ`, two relabellings of the boundary of the
  triangle on `Fin 4`, are bistellar equivalent (non-vacuity of
  `bistellarEquiv_iff_of_isRelabelling`).
* A relabelling of a closed combinatorial 1-manifold is one (`IsClosedCombManifold.image`).
* Wrong input: the map sending every vertex to `0` is not injective on the vertices, and the image of
  the boundary of the triangle under it is the single vertex `{0}`, which is not a closed
  combinatorial 1-manifold: injectivity on the vertices cannot be dropped.
-/

open Finset

namespace Lightlike.PL

open SComplex

/-- The boundary of the triangle on `Fin 4`. -/
abbrev triangle4 : SComplex (Fin 4) := boundary {0, 1, 2}

lemma isClosedCombManifold_triangle4 : IsClosedCombManifold 1 triangle4 :=
  isClosedCombManifold_boundary (by decide)

lemma injOn_val : Set.InjOn (fun i : Fin 4 => (i : ℕ)) triangle4.verts := fun _ _ _ _ h => Fin.ext h

lemma injOn_val5 : Set.InjOn (fun i : Fin 4 => (i : ℕ) + 5) triangle4.verts := fun _ _ _ _ h =>
  Fin.ext (by simpa using h)

/-- Non-vacuity: two triangles on disjoint vertex sets of `ℕ` are bistellar equivalent, by transport
from `Fin 4`. -/
example : BistellarEquiv (triangle4.image fun i => (i : ℕ)) (triangle4.image fun i => (i : ℕ) + 5) :=
  (bistellarEquiv_iff_of_isRelabelling ⟨_, injOn_val, rfl⟩ ⟨_, injOn_val5, rfl⟩
    isClosedCombManifold_triangle4).1 (BistellarEquivIn.refl _)

example : IsClosedCombManifold 1 (triangle4.image fun i => (i : ℕ) + 5) :=
  isClosedCombManifold_triangle4.image injOn_val5

/-- Wrong input: a map that is not injective on the vertices collapses the triangle to a point,
which is not a closed combinatorial 1-manifold. -/
example : ¬ IsClosedCombManifold 1 (triangle4.image fun _ => (0 : ℕ)) := by
  intro h
  rw [isClosedCombManifold_iff] at h
  have hv : (0 : ℕ) ∈ (triangle4.image fun _ => (0 : ℕ)).verts := by
    rw [verts_image]; exact Finset.mem_image.2 ⟨0, by rw [verts_boundary (by decide)]; decide, rfl⟩
  obtain ⟨A, hA, hLA⟩ := h 0 hv
  have hlk : (triangle4.image fun _ => (0 : ℕ)).link {0} = simplex ∅ := by
    refine ext_mem fun s => ?_
    rw [mem_link', mem_simplex, subset_empty]
    constructor
    · rintro ⟨hd, hs⟩
      obtain ⟨t, -, ht⟩ := SComplex.mem_image.1 hs
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have : x ∈ t.image fun _ => (0 : ℕ) := by rw [ht]; exact mem_union_right _ hx
      obtain ⟨-, -, rfl⟩ := Finset.mem_image.1 this
      exact disjoint_singleton_left.1 hd hx
    · rintro rfl
      refine ⟨disjoint_empty_right _, ?_⟩
      rw [union_empty]
      exact SComplex.mem_image.2 ⟨{0}, by rw [mem_boundary]; decide, by simp⟩
  rw [hlk, lift_simplex, map_empty] at hLA
  have := hLA.maxCard_eq
  rw [maxCard_simplex, maxCard_boundary (card_pos.1 (by omega))] at this
  simp at this
  omega

end Lightlike.PL
