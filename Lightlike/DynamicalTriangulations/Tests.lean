import Lightlike.DynamicalTriangulations.DehnSommerville
import Lightlike.DynamicalTriangulations.Action
import Lightlike.DynamicalTriangulations.Causal
import Lightlike.DynamicalTriangulations.Ergodicity

/-!
# Trust checks for the Dehn–Sommerville relations

* The boundary of the 5-simplex is a closed combinatorial 4-manifold with face numbers
  `N = (6, 15, 20, 15, 6)`, and satisfies both relations (non-vacuity).
* Two 4-simplices glued along a tetrahedron are not a manifold, and violate `2N₃ = 5N₄` (wrong
  model): the relation is not a consequence of the face counts alone.
-/

open Finset Lightlike.PL SComplex

namespace Lightlike.DynamicalTriangulations

/-- **Non-vacuity.** The boundary of the 5-simplex is a closed combinatorial 4-manifold with face
counts `N = (6, 15, 20, 15, 6)`. -/
theorem boundary_fin6_dehnSommerville :
    IsClosedCombManifold 4 (boundary (univ : Finset (Fin 6))) ∧
      (List.range 5).map (fun k => #((boundary (univ : Finset (Fin 6))).faces.filter
        fun s => #s = k + 1)) = [6, 15, 20, 15, 6] := by
  refine ⟨isClosedCombManifold_boundary (by simp), ?_⟩
  decide +kernel

/-- The relations hold on the boundary of the 5-simplex: `2·15 = 5·6` and
`2·15 − 3·20 + 6·15 − 10·6 = 0`. -/
example : 2 * (15 : ℤ) - 3 * 20 + 6 * 15 - 10 * 6 = 0 ∧ 2 * 15 = 5 * 6 := by norm_num

/-- **Wrong model.** Two 4-simplices `01234` and `12345` glued along the 3-face `1234` violate the
relation `2N₃ = 5N₄` of closed combinatorial 4-manifolds. -/
theorem twoSimplices_not_dehnSommerville :
    2 * #((closure {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}} : SComplex (Fin 6)).faces.filter
        fun s => #s = 4) ≠
      5 * #((closure {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}} : SComplex (Fin 6)).faces.filter
        fun s => #s = 5) := by
  decide +kernel

/-- The same complex is not a closed combinatorial 4-manifold (contrapositive of
`IsClosedCombManifold.two_mul_card_eq`). -/
theorem twoSimplices_not_closedCombManifold :
    ¬ IsClosedCombManifold 4 (closure {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}} : SComplex (Fin 6)) :=
  fun h => twoSimplices_not_dehnSommerville (by simpa using h.two_mul_card_eq (n := 4) (by norm_num))

/-- **Non-vacuity of the action formula.** The boundary of the 5-simplex is a closed combinatorial
4-manifold with `N₂ = 20`, `N₄ = 6`, so `S = −20 κ₂ + 6 κ₄`, and the relation `N₂ = 2N₀ + 2N₄ − 2χ`
gives `20 = 12 + 12 − 4`. -/
theorem dtAction_sphere (κ₂ κ₄ : ℝ) :
    dtAction κ₂ κ₄ (FourD.Complex4.sphere (univ : Finset (Fin 6))) = -20 * κ₂ + 6 * κ₄ := by
  have h6 : #(univ : Finset (Fin 6)) = 6 := by simp
  rw [dtAction, FourD.Complex4.card_faces_sphere h6 (by norm_num),
    FourD.Complex4.card_faces_sphere h6 (by norm_num)]
  simp [Nat.choose]
  ring

/-- The relation `N₂ = 2N₀ + 2N₄ − 2χ` on the boundary of the 5-simplex. -/
example : (20 : ℤ) = 2 * 6 + 2 * 6 - 2 * 2 := by norm_num

/-- Time function on the boundary of the 5-simplex: vertices `0..3` at time `0`, `4, 5` at time `1`. -/
def tSplit (v : Fin 6) : ℕ := if v.val < 4 then 0 else 1

/-- **Non-vacuity of the layering.** A single 4-simplex with four vertices at time `0` and one at
time `1` is layered, and its tetrahedron `{0,1,2,3}` is spacelike. -/
theorem layered_single : IsLayered tSplit (⟨{{0, 1, 2, 3, 4}}, by decide⟩ : FourD.Complex4 (Fin 6)) := by
  intro s hs
  have : s = {0, 1, 2, 3, 4} := by simpa using hs
  subst this
  refine ⟨0, ?_, ⟨0, by decide, rfl⟩, ⟨4, by decide, rfl⟩⟩
  decide +kernel

/-- **Wrong model.** Times `0,0,0,1,2` span three levels, so the simplex is not layered. -/
theorem not_layered_single :
    ¬ IsLayered (fun v : Fin 5 => if v.val < 3 then 0 else v.val - 2)
      (⟨{{0, 1, 2, 3, 4}}, by decide⟩ : FourD.Complex4 (Fin 5)) := by
  intro h
  obtain ⟨τ, h1, -, -⟩ := h {0, 1, 2, 3, 4} (by simp)
  have a := h1 0 (by decide)
  have b := h1 4 (by decide)
  simp at a b
  omega

/-- The boundary of the 5-simplex on the vertices `0..5` inside `Fin 7`. -/
def sphere7 : FourD.Complex4 (Fin 7) := FourD.Complex4.sphere (univ.filter fun v => v.val < 6)

/-- **Non-vacuity of the move chain.** The 1-5 move subdividing the 4-simplex `{0,1,2,3,4}` with the
new vertex `6` is a 4D move on `sphere7`, so the result is connected to `sphere7`. -/
theorem sphere7_move : FourD.Complex4.IsMove sphere7 {0, 1, 2, 3, 4} {6} := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;> decide +kernel

theorem sphere7_moveEquiv : MoveEquiv sphere7 (sphere7.move sphere7_move) :=
  Relation.EqvGen.rel _ _ (.move sphere7_move)

/-- The sphere `sphere7` is a closed combinatorial 4-manifold and so is its move image. -/
theorem sphere7_isCombManifold4 : PL.IsCombManifold4 (sphere7.move sphere7_move) :=
  (PL.isCombManifold4_move_iff sphere7_move).2 (PL.isCombManifold4_sphere (by decide +kernel))

/-- **The statement for every vertex type applies:** the lifts of `sphere7` and of its 1-5
subdivision to `Fin 7 ⊕ ℕ` are connected by moves, obtained from the stellar equivalence of the
generated complexes rather than from the move itself. -/
theorem sphere7_lift_moveEquiv : MoveEquiv sphere7.lift (sphere7.move sphere7_move).lift :=
  (moveEquiv_lift_iff_stellarEquiv (PL.isCombManifold4_sphere (by decide +kernel))).2
    (by rw [PL.ofComplex4_move sphere7_move]; exact SComplex.StellarEquiv.bistellar _)

/-- **Wrong model.** A single 4-simplex (Euler characteristic 1) is not connected to the boundary of
the 5-simplex (Euler characteristic 2) by moves. -/
theorem simplex_not_moveEquiv_sphere :
    ¬ MoveEquiv (FourD.Complex4.simplex ({0, 1, 2, 3, 4} : Finset (Fin 6)) (by decide))
      (FourD.Complex4.sphere (univ : Finset (Fin 6))) := by
  intro h
  have := h.euler4_eq
  rw [FourD.Complex4.euler4_simplex, FourD.Complex4.euler4_sphere (by simp)] at this
  omega

/-- **Non-vacuity of the 1-5 formula.** The 1-5 move of `sphere7` changes the action by
`−2κ₂ + 4(κ₄ − 2κ₂)`. -/
theorem sphere7_dtAction_move (κ₂ κ₄ : ℝ) :
    dtAction κ₂ κ₄ (sphere7.move sphere7_move) - dtAction κ₂ κ₄ sphere7 =
      -2 * κ₂ + 4 * (κ₄ - 2 * κ₂) :=
  dtAction_move_one_five κ₂ κ₄ sphere7_move (PL.isCombManifold4_sphere (by decide +kernel))
    (by decide +kernel)

/-- On the 1-5 subdivision of `sphere7` the tetrahedron `{0,1,2,3}` lies in exactly the two
4-simplices `{0,1,2,3,5}` and `{0,1,2,3,6}`, and `{5,6}` is not an edge: a 2-4 move applies. -/
theorem sphere7_move24 :
    FourD.Complex4.IsMove (sphere7.move sphere7_move) {0, 1, 2, 3} {5, 6} := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Non-vacuity of the move formula for `2 ≤ #σ`, `2 ≤ #τ`.** The move of `sphere7_move24` has
`#σ = 4` and `#τ = 2`, so it changes the action by `2(κ₄ − 2κ₂)`. -/
theorem sphere7_dtAction_move24 (κ₂ κ₄ : ℝ) :
    dtAction κ₂ κ₄ ((sphere7.move sphere7_move).move sphere7_move24) -
        dtAction κ₂ κ₄ (sphere7.move sphere7_move) = 2 * (κ₄ - 2 * κ₂) := by
  have := dtAction_move κ₂ κ₄ sphere7_move24 sphere7_isCombManifold4 (by decide +kernel)
    (by decide +kernel)
  rw [this]
  have h4 : #({0, 1, 2, 3} : Finset (Fin 7)) = 4 := by decide
  have h2 : #({5, 6} : Finset (Fin 7)) = 2 := by decide
  rw [h4, h2]
  norm_num

/-- **Wrong model.** Dropping the Euler characteristic term from the Dehn–Sommerville substitution
gives `−24κ₂ + 6κ₄` on the boundary of the 5-simplex, which differs from the true action
`−20κ₂ + 6κ₄` unless `κ₂ = 0`. -/
theorem dtAction_sphere_ne_without_euler {κ₂ : ℝ} (κ₄ : ℝ) (hκ : κ₂ ≠ 0) :
    dtAction κ₂ κ₄ (FourD.Complex4.sphere (univ : Finset (Fin 6))) ≠
      -2 * κ₂ * 6 + (κ₄ - 2 * κ₂) * 6 := by
  rw [dtAction_sphere]
  intro h
  apply hκ
  linarith

end Lightlike.DynamicalTriangulations
