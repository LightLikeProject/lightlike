module

public import Lightlike.PonzanoRegge.Manifold

/-!
# Move-connected triangulations

The relation "connected by the four Pachner moves" on complexes (`MoveConnected`), and what it
gives for the gauge-fixed Ponzano–Regge amplitude without Pachner's theorem.

* `PachnerStep K K'`: `K'` arises from `K` by one 2-3, 3-2, 1-4 or 4-1 move.
* `MoveConnected K K'`: the equivalence closure of `PachnerStep`.
* `MoveConnected.isCombManifold_iff`: move-connected complexes are closed combinatorial
  3-manifolds together or not at all.
* `reach_move23`, `reach_move14`: from every state `(K, T, cut)` with a maximal tree `T`, the
  2-3 and 1-4 moves can be followed by choosing the cutoffs of the new edges, keeping the cutoffs
  of the old edges, and the gauge-fixed amplitude does not change.

Pachner's theorem (any two triangulations of a closed PL manifold are `MoveConnected`) needs PL
topology that Mathlib lacks and is not proved here.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- **One Pachner move** between complexes: a 2-3, 3-2, 1-4 or 4-1 move. -/
inductive PachnerStep : Complex3 V → Complex3 V → Prop
  | m23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) : PachnerStep K (move23 K h)
  | m32 {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) : PachnerStep K (move32 K h)
  | m14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) : PachnerStep K (move14 K h)
  | m41 {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) : PachnerStep K (move41 K h)

/-- Two complexes are **move-connected** if a finite chain of Pachner moves (in either direction)
leads from one to the other. -/
def MoveConnected (K K' : Complex3 V) : Prop := Relation.EqvGen PachnerStep K K'

/-- A Pachner move preserves "closed combinatorial 3-manifold", in both directions. -/
theorem PachnerStep.isCombManifold_iff {K K' : Complex3 V} (h : PachnerStep K K') :
    IsCombManifold K ↔ IsCombManifold K' := by
  cases h with
  | m23 h => exact (isCombManifold_move23_iff h).symm
  | m32 h => exact (isCombManifold_move32_iff h).symm
  | m14 h => exact (isCombManifold_move14_iff h).symm
  | m41 h => exact (isCombManifold_move41_iff h).symm

/-- Move-connected complexes are closed combinatorial 3-manifolds together or not at all. -/
theorem MoveConnected.isCombManifold_iff {K K' : Complex3 V} (h : MoveConnected K K') :
    IsCombManifold K ↔ IsCombManifold K' := by
  induction h with
  | rel _ _ hs => exact hs.isCombManifold_iff
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `MoveConnected` is reflexive, symmetric and transitive: an equivalence relation. -/
theorem moveConnected_equivalence : Equivalence (MoveConnected (V := V)) :=
  Relation.EqvGen.is_equivalence _

/-! ## Following the forward moves with cutoffs -/

/-- **A 2-3 move can always be followed with the cutoffs of the old edges kept.** From a state with
a maximal tree `T`, choose the cutoff of the new edge `DE` as `cut AD + cut AE`; then the state
`(move23 K h, T, cut')` is reached by `GFTreeStep`s, so the gauge-fixed amplitude is the same. -/
theorem reach_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E)
    {T : Finset (Finset V)} (hT : IsMaxTree K T) (cut : Finset V → ℕ) :
    ∃ cut' : Finset V → ℕ, (∀ e ∈ K.edges, cut' e = cut e) ∧
      Relation.ReflTransGen GFTreeStep (K, T, cut) (move23 K h, T, cut') := by
  have hDEK : ({D, E} : Finset V) ∉ K.edges := fun hm => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp hm
    exact h.fresh t ht hst
  have hne : ∀ X : V, (X = A) → ({X, D} : Finset V) ≠ {D, E} := by
    rintro X rfl hX
    have : X ∈ ({D, E} : Finset V) := hX ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h.hAD h'
    · exact h.hAE h'
  have hne' : ({A, E} : Finset V) ≠ {D, E} := by
    intro hX
    have : A ∈ ({D, E} : Finset V) := hX ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h.hAD h'
    · exact h.hAE h'
  have hAD := hne A rfl
  refine ⟨Function.update cut {D, E} (cut {A, D} + cut {A, E}), ?_, ?_⟩
  · intro e he
    exact Function.update_of_ne (by rintro rfl; exact hDEK he) _ _
  · refine Relation.ReflTransGen.head (b := (K, T, Function.update cut {D, E}
        (cut {A, D} + cut {A, E}))) (GFTreeStep.recut hT (fun e he => ?_)) ?_
    · exact (Function.update_of_ne (by rintro rfl; exact hDEK (mem_sdiff.mp he).1) _ _).symm
    · refine Relation.ReflTransGen.single (GFTreeStep.move23 h hT ?_)
      rw [Function.update_of_ne hAD, Function.update_of_ne hne', Function.update_self]

/-- **A 1-4 move can always be followed with the cutoffs of the old edges kept.** The cutoff of
every edge through the new vertex `E` is `cut AD + cut BD + cut CD`; the gauge set grows by `DE`.
-/
theorem reach_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E)
    {T : Finset (Finset V)} (hT : IsMaxTree K T) (cut : Finset V → ℕ) :
    ∃ cut' : Finset V → ℕ, (∀ e ∈ K.edges, cut' e = cut e) ∧
      Relation.ReflTransGen GFTreeStep (K, T, cut) (move14 K h, insert {D, E} T, cut') := by
  classical
  have hE : ∀ e ∈ K.edges, E ∉ e := fun e he hEe => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
    exact h.fresh t ht (hst hEe)
  refine ⟨fun e => if E ∈ e then cut {A, D} + cut {B, D} + cut {C, D} else cut e, ?_, ?_⟩
  · intro e he
    simp only [hE e he, ite_false]
  · refine Relation.ReflTransGen.head (b := (K, T, fun e => if E ∈ e then
        cut {A, D} + cut {B, D} + cut {C, D} else cut e))
      (GFTreeStep.recut hT (fun e he => ?_)) ?_
    · simp only [hE e (mem_sdiff.mp he).1, ite_false]
    · refine Relation.ReflTransGen.single (GFTreeStep.move14 h hT ?_ ?_ ?_)
      · simp [h.hAE.symm, h.hDE.symm]
        omega
      · simp [h.hBE.symm, h.hDE.symm]
        omega
      · simp [h.hCE.symm, h.hDE.symm]

end Lightlike.PR
