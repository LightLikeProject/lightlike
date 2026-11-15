import Lightlike.PL.Complex4
import Lightlike.PL.PachnerMain
import Lightlike.PL.PachnerMoves

/-!
# Ergodicity of the 4D Pachner moves

The Monte Carlo of four-dimensional dynamical triangulations moves between triangulations with the
five Pachner moves (1-5, 2-4, 3-3, 4-2, 5-1); it can reach every triangulation of a manifold only
if these moves connect all of them (Ambjørn–Durhuus–Jónsson 1997; Ambjørn–Jurkiewicz–Loll 2001).
This file derives that from Pachner's theorem for the generated simplicial complexes.

* `MoveEquiv K L`: `L` is obtained from `K` by a chain of 4D moves and inverse moves on
  4-simplices (`Lightlike/FourD/Pachner.lean`), each step being a `Move4Step`.
* `IsCombManifold4In K`: `K` is a closed combinatorial 4-manifold inside its vertex type `V`.
* `IsCombManifold4In.card_add_card`: in such a manifold a bistellar move `κ(A, B)` has
  `#A + #B = 6`, so it is one of the five 4D moves.
* `moveEquiv_iff_bistellarEquivIn`: `MoveEquiv K L` holds iff the generated complexes are
  bistellar equivalent.
* `moveEquiv_of_stellarEquivIn`: for an infinite vertex type, stellar equivalent closed
  combinatorial 4-manifolds are connected by 4D moves.
* `Complex4.lift`, `moveEquiv_iff_stellarEquiv`: for every vertex type, `K.lift` and `L.lift` on
  `V ⊕ ℕ` are connected by 4D moves iff the generated complexes are stellar equivalent.
-/

open Finset Lightlike.FourD Lightlike.PL Lightlike.PL.SComplex

namespace Lightlike.DynamicalTriangulations

variable {V : Type*} [DecidableEq V]

/-- `K` and `L` are connected by a chain of 4D moves and inverse moves. -/
def MoveEquiv (K L : Complex4 V) : Prop := Relation.EqvGen Move4Step K L

/-- A 4D complex is determined by the simplicial complex it generates. -/
lemma ofComplex4_injective {K L : Complex4 V} (h : ofComplex4 K = ofComplex4 L) : K = L := by
  apply Complex4.ext
  ext s
  constructor
  · intro hs
    have : s ∈ ofComplex4 L := h ▸ mem_closure.2 ⟨s, hs, subset_rfl⟩
    obtain ⟨t, ht, hst⟩ := mem_closure.1 this
    have : s = t := eq_of_subset_of_card_le hst (by rw [K.card_eq s hs, L.card_eq t ht])
    exact this ▸ ht
  · intro hs
    have : s ∈ ofComplex4 K := h ▸ mem_closure.2 ⟨s, hs, subset_rfl⟩
    obtain ⟨t, ht, hst⟩ := mem_closure.1 this
    have : s = t := eq_of_subset_of_card_le hst (by rw [L.card_eq s hs, K.card_eq t ht])
    exact this ▸ ht

/-- `K` is a **closed combinatorial 4-manifold inside `V`**: the vertex links of the generated
complex are stellar equivalent, inside `V`, to boundaries of 4-simplices. -/
def IsCombManifold4In (K : Complex4 V) : Prop := IsClosedCombManifoldIn 4 (ofComplex4 K)

/-- **Every bistellar move of a closed combinatorial 4-manifold is a 4D move**: `#A + #B = 6`,
because the link of `A` is a sphere of dimension `4 − #A` and equals `∂B`. -/
theorem IsCombManifold4In.card_add_card [Infinite V] {K : Complex4 V} (hK : IsCombManifold4In K)
    {A B : Finset V} (h : (ofComplex4 K).IsBistellar A B) : #A + #B = 6 := by
  obtain ⟨m, hm, hsph⟩ := (isMfdIn_main false 4).1 _ (isMfdIn_false_iff.2 hK) A h.mem
    h.nonempty_left
  obtain ⟨A', hA', hst⟩ | ⟨hb, -⟩ := hsph
  · have h1 := hst.maxCard_eq
    rw [h.link_eq, maxCard_boundary h.nonempty_right, maxCard_boundary
      (by rw [← card_pos]; omega)] at h1
    have := card_pos.2 h.nonempty_right
    omega
  · exact absurd hb (by decide)

/-- A chain of 4D moves is a bistellar equivalence of the generated complexes. -/
theorem MoveEquiv.bistellarEquivIn {K L : Complex4 V} (h : MoveEquiv K L) :
    BistellarEquivIn (ofComplex4 K) (ofComplex4 L) :=
  bistellarEquivIn_of_move4 h

/-- **A 4D move keeps closed combinatorial 4-manifolds inside an infinite vertex type.** -/
lemma isCombManifold4In_move_iff [Infinite V] {K : Complex4 V} {σ τ : Finset V}
    (h : K.IsMove σ τ) : IsCombManifold4In (K.move h) ↔ IsCombManifold4In K := by
  rw [IsCombManifold4In, IsCombManifold4In, ofComplex4_move, ← isMfdIn_false_iff,
    ← isMfdIn_false_iff]
  exact (isMfdIn_iff_of_stellarEquivIn (isMfdIn_main false 4).1
    (StellarEquivIn.bistellar' (isBistellar_move4 h))).symm

/-- Chains of moves keep closed combinatorial 4-manifolds. -/
lemma MoveEquiv.isCombManifold4In_iff [Infinite V] {K L : Complex4 V} (h : MoveEquiv K L) :
    IsCombManifold4In K ↔ IsCombManifold4In L := by
  induction h with
  | rel _ _ h => cases h with | move hm => exact (isCombManifold4In_move_iff hm).symm
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The Euler characteristic is invariant along a chain of moves**, so complexes with different
Euler characteristic are never connected: the moves are ergodic only within one `χ`. -/
theorem MoveEquiv.euler4_eq {K L : Complex4 V} (h : MoveEquiv K L) : K.euler4 = L.euler4 := by
  induction h with
  | rel _ _ h => cases h with | move hm => exact (Complex4.euler4_move hm).symm
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Bistellar equivalence of closed combinatorial 4-manifolds is a chain of 4D moves**, in both
directions, for every complex generated by 4-simplices. -/
theorem moveEquiv_of_bistellarEquivIn [Infinite V] {X Y : SComplex V} (h : BistellarEquivIn X Y) :
    (∀ K : Complex4 V, ofComplex4 K = X → IsCombManifold4In K →
        ∃ L : Complex4 V, ofComplex4 L = Y ∧ MoveEquiv K L) ∧
    (∀ L : Complex4 V, ofComplex4 L = Y → IsCombManifold4In L →
        ∃ K : Complex4 V, ofComplex4 K = X ∧ MoveEquiv L K) := by
  induction h with
  | rel X Y hXY =>
    cases hXY with
    | bistellar h =>
      rename_i A B
      refine ⟨fun K hK hm => ?_, fun L hL hm => ?_⟩
      · subst hK
        have hmv := isMove_of_isBistellar h (IsCombManifold4In.card_add_card hm h)
        exact ⟨K.move hmv, by rw [ofComplex4_move hmv],
          Relation.EqvGen.rel _ _ (.move hmv)⟩
      · have hb : (ofComplex4 L).IsBistellar _ _ := hL ▸ isBistellar_bistellar h
        have hmv := isMove_of_isBistellar hb (IsCombManifold4In.card_add_card hm hb)
        refine ⟨L.move hmv, ?_, Relation.EqvGen.rel _ _ (.move hmv)⟩
        have key : ∀ (Z : SComplex V) (hZ : Z = X.bistellar A B h) (hb : Z.IsBistellar B A),
            Z.bistellar B A hb = X := by
          rintro _ rfl hb; exact bistellar_bistellar h
        rw [ofComplex4_move hmv]
        exact key _ hL hb
  | refl X => exact ⟨fun K hK _ => ⟨K, hK, Relation.EqvGen.refl _⟩,
      fun L hL _ => ⟨L, hL, Relation.EqvGen.refl _⟩⟩
  | symm X Y _ ih => exact ⟨ih.2, ih.1⟩
  | trans X Y Z _ _ ih₁ ih₂ =>
    refine ⟨fun K hK hm => ?_, fun L hL hm => ?_⟩
    · obtain ⟨M, hM, hKM⟩ := ih₁.1 K hK hm
      obtain ⟨N, hN, hMN⟩ := ih₂.1 M hM (hKM.isCombManifold4In_iff.1 hm)
      exact ⟨N, hN, Relation.EqvGen.trans _ _ _ hKM hMN⟩
    · obtain ⟨M, hM, hLM⟩ := ih₂.2 L hL hm
      obtain ⟨N, hN, hMN⟩ := ih₁.2 M hM (hLM.isCombManifold4In_iff.1 hm)
      exact ⟨N, hN, Relation.EqvGen.trans _ _ _ hLM hMN⟩

/-- **Ergodicity of the 4D moves, in terms of bistellar equivalence.** -/
theorem moveEquiv_iff_bistellarEquivIn [Infinite V] {K L : Complex4 V} (hK : IsCombManifold4In K) :
    MoveEquiv K L ↔ BistellarEquivIn (ofComplex4 K) (ofComplex4 L) := by
  refine ⟨MoveEquiv.bistellarEquivIn, fun h => ?_⟩
  obtain ⟨M, hM, hKM⟩ := (moveEquiv_of_bistellarEquivIn h).1 K rfl hK
  rwa [ofComplex4_injective hM] at hKM

/-- **Ergodicity of the 4D Pachner moves from Pachner's theorem.** In an infinite vertex type, two
closed combinatorial 4-manifolds whose generated complexes are stellar equivalent are connected by
a chain of 4D moves and inverse moves. -/
theorem moveEquiv_of_stellarEquivIn [Infinite V] {K L : Complex4 V} (hK : IsCombManifold4In K)
    (h : StellarEquivIn (ofComplex4 K) (ofComplex4 L)) : MoveEquiv K L :=
  (moveEquiv_iff_bistellarEquivIn hK).2
    (StellarEquivIn.bistellarEquivIn h (isMfdIn_false_iff.2 hK))

/-! ## Every vertex type: lifting to `V ⊕ ℕ` -/

/-- The 4D complex `K` on the vertex type `V ⊕ ℕ`, which has an unlimited supply of new vertices
for the moves. -/
abbrev _root_.Lightlike.FourD.Complex4.lift (K : Complex4 V) : Complex4 (V ⊕ ℕ) :=
  mapComplex4 K Function.Embedding.inl

lemma ofComplex4_lift (K : Complex4 V) : ofComplex4 K.lift = (ofComplex4 K).lift :=
  ofComplex4_mapComplex4 K _

/-- A closed combinatorial 4-manifold on `V` is one inside `V ⊕ ℕ` after lifting. -/
lemma _root_.Lightlike.PL.IsCombManifold4.isCombManifold4In_lift {K : Complex4 V} (hK : IsCombManifold4 K) :
    IsCombManifold4In K.lift := by
  rw [IsCombManifold4In, ofComplex4_lift]
  exact hK

/-- **Ergodicity of the 4D Pachner moves for every vertex type.** For a closed combinatorial
4-manifold `K`, the lifts to `V ⊕ ℕ` of `K` and `L` are connected by a chain of 4D moves and inverse
moves iff the generated complexes are stellar equivalent. This is `pachner4` for the 4D moves,
proved here from the bistellar version so that it also covers the empty complex. -/
theorem moveEquiv_lift_iff_stellarEquiv {K L : Complex4 V} (hK : IsCombManifold4 K) :
    MoveEquiv K.lift L.lift ↔ SComplex.StellarEquiv (ofComplex4 K) (ofComplex4 L) := by
  rw [SComplex.StellarEquiv, ← ofComplex4_lift, ← ofComplex4_lift]
  refine ⟨fun h => BistellarEquivIn.stellarEquivIn h.bistellarEquivIn, fun h => ?_⟩
  exact moveEquiv_of_stellarEquivIn hK.isCombManifold4In_lift h

end Lightlike.DynamicalTriangulations
