module

public import Lightlike.PonzanoRegge.Manifold
public import Lightlike.Tests.PonzanoRegge

/-!
# Tests for combinatorial 3-manifolds

* `isCombManifold_S3`: the boundary of the 4-simplex `01234` (the 3-sphere with five
  tetrahedra) is a closed combinatorial 3-manifold; every vertex link is computed (`link_S3_*`) and
  is the boundary of a tetrahedron.
* `isCombManifold_S3_14`, `isCombManifold_S3_14_23`: after a 1-4 move (new vertex `5`) and then a
  2-3 move (triangle `012`, new edge `45`) it still is one, by the preservation theorems; the
  moves' preconditions are checked by `decide`.
* `not_isCombManifold_K1`: **wrong input**, a single tetrahedron is not one: the link of a vertex
  is a single triangle, and a combinatorial 2-sphere has an even number of triangles.
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test.Manifold

set_option maxRecDepth 10000

/-- The boundary of the 4-simplex `01234`, inside `Fin 6` (vertex `5` is used by a 1-4 move). -/
def S3 : Complex3 (Fin 6) :=
  ⟨{{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}}, by decide⟩

theorem link_S3_0 : S3.link 0 = bdry 1 2 3 4 := by decide
theorem link_S3_1 : S3.link 1 = bdry 0 2 3 4 := by decide
theorem link_S3_2 : S3.link 2 = bdry 0 1 3 4 := by decide
theorem link_S3_3 : S3.link 3 = bdry 0 1 2 4 := by decide
theorem link_S3_4 : S3.link 4 = bdry 0 1 2 3 := by decide

/-- **The boundary of the 4-simplex is a closed combinatorial 3-manifold.** -/
theorem isCombManifold_S3 : IsCombManifold S3 := by
  intro v hv
  fin_cases v
  · show IsSphere2 (S3.link 0)
    rw [link_S3_0]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · show IsSphere2 (S3.link 1)
    rw [link_S3_1]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · show IsSphere2 (S3.link 2)
    rw [link_S3_2]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · show IsSphere2 (S3.link 3)
    rw [link_S3_3]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · show IsSphere2 (S3.link 4)
    rw [link_S3_4]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact absurd hv (by decide)

/-- The 1-4 move on `0123` with new vertex `5` applies to `S3`. -/
theorem hmove14_S3 : IsMove14 S3 0 1 2 3 5 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- After the 1-4 move, the complex is still a closed combinatorial 3-manifold. -/
theorem isCombManifold_S3_14 : IsCombManifold (move14 S3 hmove14_S3) :=
  (isCombManifold_move14_iff hmove14_S3).mpr isCombManifold_S3

/-- Then a 2-3 move applies: the triangle `012` lies in `0124` and `0125` only, and `45` is not
an edge. -/
theorem hmove23_S3_14 : IsMove23 (move14 S3 hmove14_S3) 0 1 2 4 5 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- After both moves, the complex is still a closed combinatorial 3-manifold. -/
theorem isCombManifold_S3_14_23 :
    IsCombManifold (move23 (move14 S3 hmove14_S3) hmove23_S3_14) :=
  (isCombManifold_move23_iff hmove23_S3_14).mpr isCombManifold_S3_14

/-- **Wrong input:** a single tetrahedron is not a closed combinatorial 3-manifold (it has a
boundary): the link of vertex `0` is the single triangle `123`. -/
theorem not_isCombManifold_K1 : ¬ IsCombManifold K1 := by
  intro h
  have hlink : K1.link 0 = {{1, 2, 3}} := by decide
  have := (h 0 (by decide)).even_card
  rw [hlink] at this
  exact absurd this (by decide)

end Lightlike.PR.Test.Manifold
