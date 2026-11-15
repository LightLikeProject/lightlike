import Lightlike.PL.Join
import Lightlike.PL.Starring

/-!
# Tame stellar moves commute with joins

A chain of tame stellar moves relative to a protected complex `E` on `X` lifts to a chain relative
to `E * Z` on `X * Z`, as long as every vertex of `Z` is protected and `Z` shares no vertex with
`X`. Together with the gluing lemma for tame chains this lets a move made inside a link be
applied to the whole star of a simplex.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V] {E X Y Z : SComplex V} {S : Finset V}

/-- A face of `X` that lies in `E * Z`, with `X` and `Z` vertex-disjoint, lies in `E`. -/
lemma mem_of_mem_join_of_mem {B : Finset V} (hB : B ∈ X) (hXZ : Disjoint X.verts Z.verts)
    (h : B ∈ E.join Z) : B ∈ E := by
  obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 h
  have : u = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    exact disjoint_left.1 hXZ (mem_verts_of_mem hB (mem_union_right _ hx))
      (mem_verts_of_mem hu hx)
  subst this
  rwa [union_empty]

/-- An admissible subdivision of `X` is one of `X * Z`, relative to `E * Z`, when the vertices of
`Z` are protected and not in `X`. -/
lemma IsSub.join_right {B : Finset V} {b : V} (h : IsSub E S X B b) (hZ : ∅ ∈ Z)
    (hZS : Z.verts ⊆ S) (hXZ : Disjoint X.verts Z.verts) :
    IsSub (E.join Z) S (X.join Z) B b := by
  obtain ⟨hB, hne, hBE, hbX, hbS, hbE, hS⟩ := h
  refine ⟨mem_join.2 ⟨B, hB, ∅, hZ, union_empty _⟩, hne,
    fun h' => hBE (mem_of_mem_join_of_mem hB hXZ h'), fun h' => ?_, hbS, fun h' => ?_, hS⟩
  · exact (mem_union.1 (verts_join_subset _ _ h')).elim hbX fun h'' => hbS (hZS h'')
  · exact (mem_union.1 (verts_join_subset _ _ h')).elim hbE fun h'' => hbS (hZS h'')

/-- One tame move lifts to a tame move relative to `E * Z` after joining with `Z`. -/
lemma TStep.join_right (h : TStep E S X Y) (hZ : ∅ ∈ Z) (hZS : Z.verts ⊆ S)
    (hXZ : Disjoint X.verts Z.verts) : TStep (E.join Z) S (X.join Z) (Y.join Z) := by
  have hYZ : Disjoint Y.verts Z.verts := disjoint_right.2 fun x hx hY =>
    disjoint_left.1 hXZ ((h.mem_verts_iff (hZS hx)).2 hY) hx
  rcases h with ⟨B, b, hsub, rfl⟩ | ⟨B, b, hsub, hBE, rfl⟩
  · refine .inl ⟨B, b, hsub.join_right hZ hZS hXZ, ?_⟩
    exact join_starAt hXZ (disjoint_of_subset_left (subset_verts hsub.1) hXZ)
  · refine .inr ⟨B, b, hsub.join_right hZ hZS hYZ, fun hB => hBE fun x hx => ?_, ?_⟩
    · rcases mem_union.1 (verts_join_subset _ _ (hB hx)) with h' | h'
      · exact h'
      · exact absurd h' (disjoint_left.1 (disjoint_of_subset_left (subset_verts hsub.1) hYZ) hx)
    · exact join_starAt hYZ (disjoint_of_subset_left (subset_verts hsub.1) hYZ)

/-- **A chain of tame moves on `X` lifts to a chain on `X * Z`**, relative to `E * Z`, when every
vertex of `Z` is protected and `Z` shares no vertex with `X`. -/
theorem TChain.join_right (h : TChain E S X Y) (hZ : ∅ ∈ Z) (hZS : Z.verts ⊆ S)
    (hXZ : Disjoint X.verts Z.verts) : TChain (E.join Z) S (X.join Z) (Y.join Z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail Y W hch hst ih =>
    have hYZ : Disjoint Y.verts Z.verts := disjoint_right.2 fun x hx hY =>
      disjoint_left.1 hXZ ((TChain.mem_verts_iff hch (hZS hx)).2 hY) hx
    exact ih.tail (hst.join_right hZ hZS hYZ)

end SComplex
end Lightlike.PL
