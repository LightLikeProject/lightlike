module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Isolated
public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeEdge
public import Lightlike.PonzanoRegge.Manifold
public import Lightlike.PonzanoRegge.Move14

/-!
# A combinatorial 3-sphere that is not tree-connected

Starting from the boundary of the 4-simplex (inside `Fin 7`), five Pachner moves
(1-4 on `0134`, 2-3 on `034|25`, 1-4 on `0124`, 2-3 on `012|36`, 2-3 on `013|56`) give a closed
combinatorial 3-manifold `Sph7` with seven vertices and fourteen tetrahedra, whose 1-skeleton is
the complete graph on `Fin 7`. The Hamiltonian path `2-1-0-3-4-6-5` is a maximal tree that
is isolated (no triangle of `Sph7` has two of its edges), so by `not_treeConnected_of_isolated`
the star at `0` is a maximal tree that cannot be reached by triangle exchanges:
**`Sph7` is a simply connected closed combinatorial 3-manifold that is not `TreeConnected`.**

Consequences recorded in the handoff note of the stream (not in the repository): tree-connectedness is not preserved by the 2-3 move, and
the criterion "`π₁` of the 2-skeleton trivial ⇒ `TreeConnected`" is false. The exchange argument
(`amplitudeGF_eqvGen_exchange`) therefore cannot prove tree independence for all closed
combinatorial 3-manifolds; whether the amplitude is tree independent on `Sph7` is not decided here.
-/

@[expose] public section

namespace Lightlike.PR.Test.Sph7

open Finset

set_option maxRecDepth 100000

/-- The boundary of the 4-simplex `01234`, inside `Fin 7`. -/
def S3 : Complex3 (Fin 7) :=
  ⟨{{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}}, by decide⟩

theorem h1 : IsMove14 S3 0 1 3 4 5 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- The 3-sphere after the first 1-4 move on `S3`. -/
def K1 : Complex3 (Fin 7) := move14 S3 h1

theorem h2 : IsMove23 K1 0 3 4 2 5 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- After the 2-3 move on `K1`. -/
def K2 : Complex3 (Fin 7) := move23 K1 h2

theorem h3 : IsMove14 K2 0 1 2 4 6 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- After the 1-4 move on `K2`. -/
def K3 : Complex3 (Fin 7) := move14 K2 h3

theorem h4 : IsMove23 K3 0 1 2 3 6 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- After the 2-3 move on `K3`. -/
def K4 : Complex3 (Fin 7) := move23 K3 h4

theorem h5 : IsMove23 K4 0 1 3 5 6 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The seven-vertex sphere. -/
def Sphere7 : Complex3 (Fin 7) := move23 K4 h5

theorem link_S3_0 : S3.link 0 = bdry 1 2 3 4 := by decide
theorem link_S3_1 : S3.link 1 = bdry 0 2 3 4 := by decide
theorem link_S3_2 : S3.link 2 = bdry 0 1 3 4 := by decide
theorem link_S3_3 : S3.link 3 = bdry 0 1 2 4 := by decide
theorem link_S3_4 : S3.link 4 = bdry 0 1 2 3 := by decide

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
  · exact absurd hv (by decide)

/-- **`Sphere7` is a closed combinatorial 3-manifold** (five Pachner moves from the boundary of the
4-simplex). -/
theorem isCombManifold_Sphere7 : IsCombManifold Sphere7 :=
  (isCombManifold_move23_iff h5).mpr <| (isCombManifold_move23_iff h4).mpr <|
    (isCombManifold_move14_iff h3).mpr <| (isCombManifold_move23_iff h2).mpr <|
      (isCombManifold_move14_iff h1).mpr isCombManifold_S3

/-- The Hamiltonian path `2-1-0-3-4-6-5`. -/
def Tpath : Finset (Finset (Fin 7)) := {{1, 2}, {3, 4}, {0, 1}, {0, 3}, {4, 6}, {5, 6}}

/-- The star at `0`. -/
def Tstar : Finset (Finset (Fin 7)) := {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}, {0, 6}}

theorem verts_Sphere7 : Sphere7.verts = univ := by decide +kernel

theorem isMaxTree_Tpath : IsMaxTree Sphere7 Tpath := by
  refine ⟨by decide +kernel, ?_⟩
  rw [verts_Sphere7]
  refine IsSpanningTree.of_parent (r := 0) (mem_univ _) ![0, 0, 1, 0, 3, 6, 4]
    ![0, 1, 2, 1, 2, 4, 3] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem isMaxTree_Tstar : IsMaxTree Sphere7 Tstar := by
  refine ⟨by decide +kernel, ?_⟩
  rw [verts_Sphere7]
  refine IsSpanningTree.of_parent (r := 0) (mem_univ _) (fun _ => 0)
    (fun w => if w = 0 then 0 else 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- No triangle of `Sphere7` has two edges of the Hamiltonian path. -/
theorem isolated_Tpath : ∀ u v w : Fin 7, ({u, v} : Finset (Fin 7)) ∈ Tpath →
    ({v, w} : Finset (Fin 7)) ∈ Tpath → u ≠ w → ({u, v, w} : Finset (Fin 7)) ∈ Sphere7.tris →
      False := by
  decide +kernel

/-- **A simply connected closed combinatorial 3-manifold that is not tree-connected**: two maximal
trees of `Sphere7` (the star and the Hamiltonian path) are not connected by triangle exchanges. -/
theorem not_treeConnected_Sphere7 : ¬ TreeConnected Sphere7 :=
  not_treeConnected_of_isolated isMaxTree_Tpath isMaxTree_Tstar (by decide +kernel) isolated_Tpath

end Lightlike.PR.Test.Sph7
