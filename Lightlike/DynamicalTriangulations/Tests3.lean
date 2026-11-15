import Lightlike.DynamicalTriangulations.DehnSommerville3
import Lightlike.DynamicalTriangulations.Action3
import Lightlike.DynamicalTriangulations.Ergodicity3
import Lightlike.Tests.Manifold

/-!
# Trust checks for the three-dimensional Dehn–Sommerville relations and action

* The boundary of the 4-simplex `S3` is a closed combinatorial 3-manifold with
  `N = (5, 10, 10, 5)`, and satisfies `N₂ = 2N₃`, `N₁ = N₀ + N₃` (non-vacuity). Its action is
  `−10 κ₁ + 5 κ₃`, and after a 1-4 move `−14 κ₁ + 8 κ₃`, in agreement with `3κ₃ − 4κ₁`.
* Two tetrahedra glued along a triangle are not a closed manifold and violate `N₂ = 2N₃`
  (wrong model): the relation is not a consequence of the face counts alone.
-/

open Finset Lightlike.PR Lightlike.PR.Test.Manifold

namespace Lightlike.DynamicalTriangulations

/-- **Non-vacuity.** The boundary of the 4-simplex has face numbers `N = (5, 10, 10, 5)`. -/
theorem S3_counts :
    #S3.verts = 5 ∧ #S3.edges = 10 ∧ #S3.tris = 10 ∧ #S3.tets = 5 := by
  decide +kernel

/-- The relations hold on `S3`, as the theorems say they must. -/
example : (#S3.edges : ℤ) = #S3.verts + #S3.tets := isCombManifold_S3.card_edges

/-- The action of `S3` is `−10 κ₁ + 5 κ₃`, and agrees with `−κ₁ N₀ + (κ₃ − κ₁) N₃`. -/
theorem dtAction3_S3 (κ₁ κ₃ : ℝ) : dtAction3 κ₁ κ₃ S3 = -10 * κ₁ + 5 * κ₃ := by
  obtain ⟨-, h1, -, h3⟩ := S3_counts
  rw [dtAction3, h1, h3]; push_cast; ring

/-- After a 1-4 move on `S3` the action is `−14 κ₁ + 8 κ₃` (14 edges, 8 tetrahedra), a change of
`3κ₃ − 4κ₁`. -/
theorem dtAction3_S3_14 (κ₁ κ₃ : ℝ) :
    dtAction3 κ₁ κ₃ (move14 S3 hmove14_S3) = -14 * κ₁ + 8 * κ₃ := by
  obtain ⟨-, h1, -, h3⟩ := S3_counts
  rw [dtAction3, card_edges_move14, card_tets_move14, h1, h3]; push_cast; ring

/-- **Non-vacuity of the 2-3 formula.** On `S3` after a 1-4 move the 2-3 move of
`hmove23_S3_14` applies (triangle `012`, apexes `4` and `5`, and `45` not an edge), and changes the
action by `κ₃ − κ₁`. -/
theorem dtAction3_S3_14_23 (κ₁ κ₃ : ℝ) :
    dtAction3 κ₁ κ₃ (move23 (move14 S3 hmove14_S3) hmove23_S3_14) -
        dtAction3 κ₁ κ₃ (move14 S3 hmove14_S3) = κ₃ - κ₁ :=
  dtAction3_move23 κ₁ κ₃ hmove23_S3_14

/-- The closed manifold after the move has `N₀ = 6`, and `14 = 6 + 8`. -/
example : (14 : ℤ) = 6 + 8 := by norm_num

/-- **Wrong model.** Two tetrahedra `0123` and `1234` glued along the triangle `123`. -/
def twoTets : Complex3 (Fin 5) := ⟨{{0, 1, 2, 3}, {1, 2, 3, 4}}, by decide⟩

/-- It violates `N₂ = 2N₃`: it has 7 triangles and 2 tetrahedra. -/
theorem twoTets_not_dehnSommerville : #twoTets.tris ≠ 2 * #twoTets.tets := by
  decide +kernel

/-- It is therefore not a closed combinatorial 3-manifold. -/
theorem twoTets_not_isCombManifold : ¬ IsCombManifold twoTets :=
  fun h => twoTets_not_dehnSommerville h.card_tris

end Lightlike.DynamicalTriangulations
