module

public import Lightlike.PonzanoRegge.SphereInvariants

/-!
# Tests for the invariants of combinatorial 2-spheres

**Wrong inputs rejected by the Euler characteristic** (each has an even number of triangles, so
the parity test of `IsSphere2.even_card` alone would not reject it):

* `not_isSphere2_wedge`: two tetrahedron boundaries glued at a vertex (Euler characteristic `3`);
* `not_isSphere2_torus`: the 7-vertex triangulation of the torus (Euler characteristic `0`);
* `not_isCombManifold_pinched`: two boundaries of 4-simplices glued at a vertex. The link of that
  vertex is two disjoint 2-spheres (Euler characteristic `4`), so the complex is not a closed
  combinatorial 3-manifold.
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test.Sphere

set_option maxRecDepth 20000

/-- Two tetrahedron boundaries `0123` and `0456`, glued at the vertex `0`. -/
def wedge : Finset (Finset (Fin 7)) := bdry 0 1 2 3 ∪ bdry 0 4 5 6

theorem euler2_wedge : euler2 wedge = 3 := by decide

/-- **Wrong input:** two spheres glued at a vertex are not a combinatorial 2-sphere. -/
theorem not_isSphere2_wedge : ¬ IsSphere2 wedge := fun h => by
  have := h.euler
  rw [euler2_wedge] at this
  exact absurd this (by decide)

/-- The 7-vertex torus: triangles `{i, i+1, i+3}` and `{i, i+2, i+3}` modulo 7. -/
def torus : Finset (Finset (Fin 7)) :=
  (univ : Finset (Fin 7)).image (fun i => ({i, i + 1, i + 3} : Finset (Fin 7))) ∪
    (univ : Finset (Fin 7)).image (fun i => ({i, i + 2, i + 3} : Finset (Fin 7)))

theorem card_torus : #torus = 14 := by decide

theorem euler2_torus : euler2 torus = 0 := by decide

/-- **Wrong input:** the torus is not a combinatorial 2-sphere (it has 14 triangles, an even
number, so only the Euler characteristic rejects it). -/
theorem not_isSphere2_torus : ¬ IsSphere2 torus := fun h => by
  have := h.euler
  rw [euler2_torus] at this
  exact absurd this (by decide)

/-- Two boundaries of 4-simplices, `01234` and `05678`, glued at the vertex `0`. -/
def pinched : Complex3 (Fin 9) :=
  ⟨{{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4},
    {0, 5, 6, 7}, {0, 5, 6, 8}, {0, 5, 7, 8}, {0, 6, 7, 8}, {5, 6, 7, 8}}, by decide⟩

theorem euler2_link_pinched : euler2 (pinched.link 0) = 4 := by decide

/-- **Wrong input:** two 3-spheres glued at a vertex are not a closed combinatorial 3-manifold:
the link of the common vertex has Euler characteristic `4`. -/
theorem not_isCombManifold_pinched : ¬ IsCombManifold pinched := fun h => by
  have := (h 0 (by decide)).euler
  rw [euler2_link_pinched] at this
  exact absurd this (by decide)

end Lightlike.PR.Test.Sphere
