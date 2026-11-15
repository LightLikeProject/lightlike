import Lightlike.PL.PachnerMoves
import Lightlike.PonzanoRegge.Manifold

/-!
# Ergodicity of the 3D Pachner moves

The Monte Carlo of three-dimensional dynamical triangulations moves between triangulations with
the four Pachner moves 2-3, 3-2, 1-4 and 4-1; it can reach every triangulation of a manifold only
if these moves connect all of them (Ambjørn–Durhuus–Jónsson 1997). Pachner's theorem of the PL
layer (`Lightlike.PL.Complex3.pachner3`) says exactly this for the triangulations
`Lightlike.PR.Complex3` of `PonzanoRegge/`.

* `MoveEquiv3 K L`: `L` is obtained from `K` by a chain of 3D moves and inverse moves.
* `MoveEquiv3.isCombManifold_iff`: chains of moves keep closed combinatorial 3-manifolds.
* `moveEquiv3_lift_iff_stellarEquiv`: **ergodicity**: for a nonempty closed combinatorial
  3-manifold `K`, the lifts of `K` and `L` to `V ⊕ ℕ` are connected by 3D moves iff the generated
  complexes are stellar equivalent.
-/

open Finset Lightlike.PL Lightlike.PR

namespace Lightlike.DynamicalTriangulations

variable {V : Type*} [DecidableEq V]

/-- `K` and `L` are connected by a chain of 3D moves (2-3, 3-2, 1-4, 4-1) and inverse moves. -/
def MoveEquiv3 (K L : Complex3 V) : Prop := Relation.EqvGen Move3Step K L

/-- A chain of 3D moves is a bistellar equivalence of the generated complexes. -/
theorem MoveEquiv3.bistellarEquivIn {K L : Complex3 V} (h : MoveEquiv3 K L) :
    SComplex.BistellarEquivIn (ofComplex3 K) (ofComplex3 L) :=
  bistellarEquivIn_of_move3 h

/-- **Chains of 3D moves keep closed combinatorial 3-manifolds**, in both directions. -/
theorem MoveEquiv3.isCombManifold_iff {K L : Complex3 V} (h : MoveEquiv3 K L) :
    IsCombManifold K ↔ IsCombManifold L := by
  induction h with
  | rel _ _ h =>
    cases h with
    | move23 hm => exact (isCombManifold_move23_iff hm).symm
    | move32 hm => exact (isCombManifold_move32_iff hm).symm
    | move14 hm => exact (isCombManifold_move14_iff hm).symm
    | move41 hm => exact (isCombManifold_move41_iff hm).symm
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Ergodicity of the 3D Pachner moves from Pachner's theorem.** For a nonempty closed
combinatorial 3-manifold `K`, the lifts of `K` and `L` to the vertex type `V ⊕ ℕ`, which has an
unlimited supply of new vertices for the moves, are connected by a chain of 2-3, 3-2, 1-4 and 4-1
moves iff the generated complexes are stellar equivalent. -/
theorem moveEquiv3_lift_iff_stellarEquiv {K L : Complex3 V} (hK : IsCombManifold K)
    (hne : K.tets.Nonempty) :
    MoveEquiv3 (mapComplex3 K (Function.Embedding.inl : V ↪ V ⊕ ℕ))
        (mapComplex3 L (Function.Embedding.inl : V ↪ V ⊕ ℕ)) ↔
      SComplex.StellarEquiv (ofComplex3 K) (ofComplex3 L) :=
  (pachner3 hK hne).symm

end Lightlike.DynamicalTriangulations
