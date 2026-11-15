import Lightlike.PL.Complex4
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Causal (layered) triangulations

A causal dynamical triangulation is a triangulation with a **time function** `t : V → ℕ` on the
vertices such that every 4-simplex spans exactly two consecutive times: its vertices have times `τ`
and `τ + 1`, both occurring (Ambjørn–Jurkiewicz–Loll 2001; Loll 2019). The 4-simplices are of type
`(4,1)`, `(3,2)`, `(2,3)` or `(1,4)` according to how many vertices lie at the earlier time. A
tetrahedron whose vertices all have the same time is **spacelike**; the others are timelike.

## Main results

* `IsLayered t K`: every 4-simplex of `K` spans exactly two consecutive times.
* `IsLayered.card_spatial_subset`: a 4-simplex contains at most one spacelike tetrahedron, and it
  does exactly when it is of type `(4,1)` or `(1,4)`.
* `two_mul_card_spatial_tets`: in a closed combinatorial 4-manifold with a layering, twice the
  number of spacelike tetrahedra is the number of 4-simplices of type `(4,1)` or `(1,4)`.
-/

open Finset Lightlike.FourD

namespace Lightlike.DynamicalTriangulations

variable {V : Type*} [DecidableEq V]

/-- A tetrahedron (or any vertex set) is **spacelike** for the time function `t` when all its
vertices have the same time. -/
def IsSpacelike (t : V → ℕ) (f : Finset V) : Prop := ∀ v ∈ f, ∀ w ∈ f, t v = t w

instance (t : V → ℕ) (f : Finset V) : Decidable (IsSpacelike t f) := by
  unfold IsSpacelike; infer_instance

/-- `t` **layers** `K`: every 4-simplex has vertices at exactly two consecutive times `τ` and
`τ + 1`. -/
def IsLayered (t : V → ℕ) (K : Complex4 V) : Prop :=
  ∀ s ∈ K.simps, ∃ τ, (∀ v ∈ s, t v = τ ∨ t v = τ + 1) ∧ (∃ v ∈ s, t v = τ) ∧
    ∃ v ∈ s, t v = τ + 1

/-- A 4-simplex of a layered complex is not spacelike: it has two vertices of different times. -/
lemma IsLayered.not_spacelike {t : V → ℕ} {K : Complex4 V} (h : IsLayered t K) {s : Finset V}
    (hs : s ∈ K.simps) : ¬ IsSpacelike t s := by
  obtain ⟨τ, -, ⟨v, hv, hvτ⟩, ⟨w, hw, hwτ⟩⟩ := h s hs
  intro hsp
  have := hsp v hv w hw
  omega

/-- A 4-simplex of a layered complex contains at most one spacelike tetrahedron. -/
lemma IsLayered.spatial_unique {t : V → ℕ} {K : Complex4 V} (h : IsLayered t K) {s f f' : Finset V}
    (hs : s ∈ K.simps) (hf : f ⊆ s) (hf' : f' ⊆ s) (hc : #f = 4) (hc' : #f' = 4)
    (hsp : IsSpacelike t f) (hsp' : IsSpacelike t f') : f = f' := by
  by_contra hne
  have h5 := K.card_eq s hs
  have hss : f ∪ f' ⊆ s := union_subset hf hf'
  have h3 : f ⊂ f ∪ f' := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨subset_union_left, fun heq => hne ?_⟩
    have : f' ⊆ f := heq ▸ subset_union_right
    exact (eq_of_subset_of_card_le this (by omega)).symm
  have h4 : 5 ≤ #(f ∪ f') := by have := card_lt_card h3; omega
  have hu : s ⊆ f ∪ f' := (eq_of_subset_of_card_le hss (by omega)).symm ▸ subset_rfl
  have hinter : (f ∩ f').Nonempty := by
    rw [← card_pos]
    have := card_union_add_card_inter f f'
    have := card_le_card hss
    omega
  obtain ⟨c, hc1⟩ := hinter
  have hcf := (mem_inter.1 hc1).1
  have hcf' := (mem_inter.1 hc1).2
  apply (h.not_spacelike hs ?_).elim
  intro v hv w hw
  have hv' := hu hv
  have hw' := hu hw
  have tv : t v = t c := by
    rcases mem_union.1 hv' with h | h
    · exact hsp v h c hcf
    · exact hsp' v h c hcf'
  have tw : t w = t c := by
    rcases mem_union.1 hw' with h | h
    · exact hsp w h c hcf
    · exact hsp' w h c hcf'
  rw [tv, tw]

/-- **Spacelike tetrahedra and the simplices of type `(4,1)` and `(1,4)`.** In a layered closed
combinatorial 4-manifold, every spacelike tetrahedron lies in exactly two 4-simplices, and a
4-simplex contains at most one spacelike tetrahedron, so twice the number of spacelike tetrahedra is
the number of 4-simplices that contain one: those of type `(4,1)` and `(1,4)`. -/
theorem two_mul_card_spatial_tets {t : V → ℕ} {K : Complex4 V} (hK : Lightlike.PL.IsCombManifold4 K)
    (hL : IsLayered t K) :
    2 * #(K.tets.filter (IsSpacelike t)) =
      #(K.simps.filter fun s => ∃ f ⊆ s, #f = 4 ∧ IsSpacelike t f) := by
  have hc := hK.isClosed4
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := K.tets.filter (IsSpacelike t))
    (t := K.simps.filter fun s => ∃ f ⊆ s, #f = 4 ∧ IsSpacelike t f) (fun f s => f ⊆ s)
  have hl : ∀ f ∈ K.tets.filter (IsSpacelike t),
      #((K.simps.filter fun s => ∃ f ⊆ s, #f = 4 ∧ IsSpacelike t f).bipartiteAbove
        (fun f s => f ⊆ s) f) = 2 := by
    intro f hf
    rw [mem_filter] at hf
    rw [← hc f hf.1, Complex4.star]
    congr 1
    ext s
    simp only [mem_bipartiteAbove, mem_filter]
    constructor
    · rintro ⟨⟨hs, -⟩, hfs⟩
      exact ⟨hs, hfs⟩
    · rintro ⟨hs, hfs⟩
      exact ⟨⟨hs, f, hfs, Complex4.card_of_mem_faces hf.1, hf.2⟩, hfs⟩
  have hr : ∀ s ∈ K.simps.filter (fun s => ∃ f ⊆ s, #f = 4 ∧ IsSpacelike t f),
      #((K.tets.filter (IsSpacelike t)).bipartiteBelow (fun f s => f ⊆ s) s) = 1 := by
    intro s hs
    rw [mem_filter] at hs
    obtain ⟨hs, f, hfs, hf4, hfsp⟩ := hs
    rw [card_eq_one]
    refine ⟨f, ?_⟩
    ext g
    simp only [mem_bipartiteBelow, mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨hg, hgsp⟩, hgs⟩
      exact hL.spatial_unique hs hgs hfs (Complex4.card_of_mem_faces hg) hf4 hgsp hfsp
    · rintro rfl
      refine ⟨⟨Complex4.mem_faces.2 ⟨s, hs, hfs, hf4⟩, hfsp⟩, hfs⟩
  rw [sum_congr rfl hl, sum_congr rfl hr] at h
  simpa [mul_comm] using h

end Lightlike.DynamicalTriangulations
