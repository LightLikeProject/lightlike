import Lightlike.PL.Schoenflies.LatticeGraph

/-!
# A boundary cycle through a given boundary edge

Row G3-188, milestone PL5 (third pass), item 5b, route A.  For a finite pinch-free set `S` of lattice
squares, every boundary edge lies on a cycle of the boundary graph (`exists_boundary_cycle`): a closed
sequence of `n ≥ 3` distinct lattice points, consecutive ones adjacent in `bdGraph S`, passing through the
given edge.  This is Mathlib's `SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`
applied to the (finite) subgraph induced on the vertices of positive degree.
-/

namespace Lightlike.PL.Schoenflies

open Set

variable {S : Set (ℤ × ℤ)}

/-- The lattice points incident to a boundary edge. -/
def bdVerts (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) := {v | ∃ w, (bdGraph S).Adj v w}

/-- For a finite set of squares the set of vertices of positive degree is finite: they are corners of
squares of `S`. -/
lemma bdVerts_finite (hS : S.Finite) : (bdVerts S).Finite := by
  have hsub : bdVerts S ⊆ S ∪ (fun s : ℤ × ℤ => (s.1 + 1, s.2)) '' S ∪
      (fun s : ℤ × ℤ => (s.1, s.2 + 1)) '' S ∪ (fun s : ℤ × ℤ => (s.1 + 1, s.2 + 1)) '' S := by
    rintro ⟨x, y⟩ ⟨⟨a, b⟩, h⟩
    have h' : BdAdj S (x, y) (a, b) := h
    rw [bdAdj_iff] at h'
    simp only [HB, VB] at h'
    have e1 : ((x - 1 + 1, y) : ℤ × ℤ) = (x, y) := by simp
    have e2 : ((x, y - 1 + 1) : ℤ × ℤ) = (x, y) := by simp
    have e3 : ((x - 1 + 1, y - 1 + 1) : ℤ × ℤ) = (x, y) := by simp
    have c1 : ((x - 1, y) ∈ S) → (x, y) ∈ (fun s : ℤ × ℤ => (s.1 + 1, s.2)) '' S :=
      fun hs => ⟨(x - 1, y), hs, e1⟩
    have c2 : ((x, y - 1) ∈ S) → (x, y) ∈ (fun s : ℤ × ℤ => (s.1, s.2 + 1)) '' S :=
      fun hs => ⟨(x, y - 1), hs, e2⟩
    have c3 : ((x - 1, y - 1) ∈ S) → (x, y) ∈ (fun s : ℤ × ℤ => (s.1 + 1, s.2 + 1)) '' S :=
      fun hs => ⟨(x - 1, y - 1), hs, e3⟩
    rcases h' with ⟨_, _, (⟨h1, _⟩ | ⟨h1, _⟩)⟩ | ⟨_, _, (⟨h1, _⟩ | ⟨h1, _⟩)⟩ |
      ⟨_, _, (⟨h1, _⟩ | ⟨h1, _⟩)⟩ | ⟨_, _, (⟨h1, _⟩ | ⟨h1, _⟩)⟩
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inr (c2 h1))
    · exact Or.inl (Or.inl (Or.inr (c1 h1)))
    · exact Or.inr (c3 h1)
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr (c1 h1)))
    · exact Or.inl (Or.inr (c2 h1))
    · exact Or.inr (c3 h1)
  exact ((((hS.union (hS.image _)).union (hS.image _)).union (hS.image _))).subset hsub

/-- The boundary graph restricted to the vertices of positive degree still consists of cycles. -/
lemma isCycles_induce (hS : NoPinch S) : ((bdGraph S).induce (bdVerts S)).IsCycles := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  have hnb : ((bdGraph S).induce (bdVerts S)).neighborSet v =
      Subtype.val ⁻¹' (bdGraph S).neighborSet v.val := by
    ext u
    exact Iff.rfl
  rw [hnb, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
  · exact bdGraph_isCycles S hS ⟨w.val, hw⟩
  · intro u hu
    exact ⟨⟨u, ⟨v.val, hu.symm⟩⟩, rfl⟩

/-- A function with `g n = g 0` composed with the rotation of `Fin n`. -/
lemma rotate_apply {α : Type*} (n : ℕ) (g : ℕ → α) (hg : g n = g 0) (i : Fin n) :
    g (finRotate n i).val = g (i.val + 1) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [coe_finRotate]
    split_ifs with h
    · have : i.val = m := by rw [h]; rfl
      rw [this]; exact hg.symm
    · rfl

/-- **Every boundary edge lies on a boundary cycle.** For a finite pinch-free set `S` of lattice squares
and a boundary edge `a b`, there are `n ≥ 3` distinct lattice points `v 0, …, v (n-1)`, consecutive ones
(cyclically) adjacent in the boundary graph, and one consecutive pair is `{a, b}`. -/
theorem exists_boundary_cycle (hS : NoPinch S) (hfin : S.Finite) {a b : ℤ × ℤ}
    (hab : (bdGraph S).Adj a b) :
    ∃ (n : ℕ) (v : Fin n → ℤ × ℤ), 3 ≤ n ∧ Function.Injective v ∧
      (∀ i, (bdGraph S).Adj (v i) (v (finRotate n i))) ∧
      ∃ i, (v i = a ∧ v (finRotate n i) = b) ∨ (v i = b ∧ v (finRotate n i) = a) := by
  classical
  have ha : a ∈ bdVerts S := ⟨b, hab⟩
  have hb : b ∈ bdVerts S := ⟨a, hab.symm⟩
  have : Finite (bdVerts S) := (bdVerts_finite hfin).to_subtype
  set G' := (bdGraph S).induce (bdVerts S) with hG'
  have : G'.LocallyFinite := fun v => Fintype.ofFinite _
  have hadj : G'.Adj ⟨a, ha⟩ ⟨b, hb⟩ := hab
  obtain ⟨c, hc, hcv⟩ := (isCycles_induce hS).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G'.connectedComponentMk ⟨a, ha⟩) (show (⟨a, ha⟩ : bdVerts S) ∈ (G'.connectedComponentMk ⟨a, ha⟩).supp from rfl)
    (⟨⟨b, hb⟩, hadj⟩ : (G'.neighborSet ⟨a, ha⟩).Nonempty)
  have hv0 : (⟨a, ha⟩ : bdVerts S) ∈ c.toSubgraph.verts := by
    rw [hcv]; rfl
  have hedge : s((⟨a, ha⟩ : bdVerts S), ⟨b, hb⟩) ∈ c.edges := by
    rw [← SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact (hc.adj_toSubgraph_iff_of_isCycles (isCycles_induce hS) hv0 _).2 hadj
  obtain ⟨i, hi, hie⟩ := (SimpleGraph.Walk.mk_mem_edges_iff_exists c).1 hedge
  have h3 := hc.three_le_length
  refine ⟨c.length, fun j => (c.getVert j.val).val, h3, ?_, ?_, ⟨⟨i, hi⟩, ?_⟩⟩
  · intro j k hjk
    have := hc.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) (Subtype.ext hjk)
    exact Fin.ext this
  · intro j
    have e := rotate_apply c.length c.getVert (by simp) j
    show (bdGraph S).Adj (c.getVert j.val).val (c.getVert (finRotate c.length j).val).val
    rw [e]
    exact c.adj_getVert_succ j.isLt
  · have e := rotate_apply c.length c.getVert (by simp) ⟨i, hi⟩
    simp only
    rw [e]
    rcases Sym2.eq_iff.1 hie with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩

end Lightlike.PL.Schoenflies
