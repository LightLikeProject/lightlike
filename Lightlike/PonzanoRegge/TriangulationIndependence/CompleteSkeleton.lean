module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeConnected

/-!
# Tree-connectedness on complexes with a complete 2-skeleton

Lemma L9 of the closed-manifold gauge-tree programme (Freidel–Louapre 2004, Section III), positive
side. If every three distinct vertices of `K` span a triangle of `K` (the 2-skeleton is complete),
then every maximal tree is exchange-connected to the star at any chosen vertex `r`
(`treeConnected_of_complete_triangles`). The proof is an induction on the number of tree edges that
miss `r`: a tree edge `zy` with `ry` in the tree and `rz` not in it is exchanged for `zr`, which adds
one edge at `r` (`TreeExchange` with `(u, v, w) = (z, y, r)`).

The boundary of the 4-simplex (a combinatorial 3-sphere) has this property, see `K5` and
`treeConnected_K5`, so the gauge-fixed amplitude of that sphere is independent of the tree.

This is consistent with the cohomological obstruction of `Cocycle.lean`: a complete 2-skeleton has
`H¹(·; ZMod 2) = 0`.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- A path from a vertex with property `N` to one without it has a step that leaves `N`. -/
lemma exists_crossing {R : V → V → Prop} {N : V → Prop} {a b : V}
    (h : Relation.ReflTransGen R a b) (ha : N a) (hb : ¬ N b) :
    ∃ y z, N y ∧ ¬ N z ∧ R y z := by
  induction h with
  | refl => exact absurd ha hb
  | @tail b' c _ hbc ih =>
    by_cases hb' : N b'
    · exact ⟨b', c, hb', hb, hbc⟩
    · exact ih hb'

/-- A maximal tree all of whose edges contain `r` is the star of `r` in the 1-skeleton. -/
lemma IsMaxTree.eq_star {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T) {r : V}
    (hr : r ∈ K.verts) (hall : ∀ e ∈ T, r ∈ e) :
    T = K.edges.filter (fun e => r ∈ e) := by
  ext e
  simp only [mem_filter]
  constructor
  · intro he
    exact ⟨hT.1 he, hall e he⟩
  · rintro ⟨he, hre⟩
    obtain ⟨t, ht, hst, hc⟩ := Complex3.mem_edges.mp he
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    have key : ∀ x, x ∈ K.verts → x ≠ r → ({r, x} : Finset V) ∈ T := by
      intro x hx hxr
      rcases (hT.2.conn r hr x hx).cases_tail with h | ⟨y, _, hyx⟩
      · exact absurd h hxr
      · have hmem := hall _ hyx
        simp only [mem_insert, mem_singleton] at hmem
        rcases hmem with h | h
        · rw [← h] at hyx
          exact hyx
        · exact absurd h (Ne.symm hxr)
    have ha : a ∈ K.verts := Complex3.mem_verts.mpr ⟨t, ht, hst (by simp)⟩
    have hb : b ∈ K.verts := Complex3.mem_verts.mpr ⟨t, ht, hst (by simp)⟩
    have hra : r = a ∨ r = b := by simpa using hre
    rcases hra with h | h
    · rw [← h]
      exact key b hb (fun hbr => hab (h.symm.trans hbr.symm))
    · rw [← h, pair_comm]
      exact key a ha (fun har => hab (har.trans h))

/-- **Tree-connectedness for a complete 2-skeleton**: if any three distinct vertices of `K` span a
triangle of `K`, then any two maximal trees are connected by triangle exchanges. -/
theorem treeConnected_of_complete_triangles (K : Complex3 V)
    (hK : ∀ ⦃x y z : V⦄, x ∈ K.verts → y ∈ K.verts → z ∈ K.verts → x ≠ y → y ≠ z → x ≠ z →
      ({x, y, z} : Finset V) ∈ K.tris) : TreeConnected K := by
  have main : ∀ r ∈ K.verts, ∀ n : ℕ, ∀ T : Finset (Finset V), IsMaxTree K T →
      #(T.filter (fun e => r ∉ e)) = n →
      Relation.EqvGen (TreeExchange K) T (K.edges.filter (fun e => r ∈ e)) := by
    intro r hr n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro T hT hn
    by_cases hall : ∀ e ∈ T, r ∈ e
    · rw [hT.eq_star hr hall]
      exact Relation.EqvGen.refl _
    · push Not at hall
      obtain ⟨e, heT, hre⟩ := hall
      have hz : ∃ z ∈ K.verts, z ≠ r ∧ ({r, z} : Finset V) ∉ T := by
        by_contra hcon
        push Not at hcon
        obtain ⟨A, hA⟩ : ∃ A : Finset (Finset V),
            A = (K.verts.erase r).image (fun x => ({r, x} : Finset V)) := ⟨_, rfl⟩
        have hAT : A ⊆ T := by
          intro f hf
          rw [hA] at hf
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hf
          exact hcon x (mem_of_mem_erase hx) (ne_of_mem_erase hx)
        have hAcard : #A = #(K.verts.erase r) := by
          rw [hA]
          apply card_image_of_injOn
          intro x _ y _ hxy
          have hxy' : ({r, x} : Finset V) = {r, y} := hxy
          rcases pair_eq_pair_iff'.mp hxy' with ⟨_, h⟩ | ⟨h1, h2⟩
          · exact h
          · exact h2.trans h1
        have hAT' : A = T := eq_of_subset_of_card_le hAT (by
          rw [hAcard, card_erase_of_mem hr]
          have := hT.2.card
          omega)
        rw [← hAT', hA] at heT
        obtain ⟨x, _, rfl⟩ := mem_image.mp heT
        exact hre (by simp)
      obtain ⟨z, hzv, hzr, hrzT⟩ := hz
      obtain ⟨y, z', hNy, hNz', hyz⟩ := exists_crossing
        (N := fun x => x = r ∨ ({r, x} : Finset V) ∈ T)
        (hT.2.conn r hr z hzv) (Or.inl rfl)
        (by
          rintro (h | h)
          · exact hzr h
          · exact hrzT h)
      have hyz : ({y, z'} : Finset V) ∈ T := hyz
      have hNz' : z' ≠ r ∧ ({r, z'} : Finset V) ∉ T := by
        simpa only [not_or] using hNz'
      have hyr : y ≠ r := by
        intro h
        rw [h] at hyz
        exact hNz'.2 hyz
      have hry : ({r, y} : Finset V) ∈ T := hNy.resolve_left hyr
      have hz'y : z' ≠ y := by
        intro h
        have := (hT.2.edge _ hyz).2
        rw [h] at this
        simp at this
      have hz'v : z' ∈ K.verts := Complex3.mem_verts.mpr (by
        obtain ⟨t, ht, hst, _⟩ := Complex3.mem_edges.mp (hT.1 hyz)
        exact ⟨t, ht, hst (by simp)⟩)
      have hyv : y ∈ K.verts := Complex3.mem_verts.mpr (by
        obtain ⟨t, ht, hst, _⟩ := Complex3.mem_edges.mp (hT.1 hyz)
        exact ⟨t, ht, hst (by simp)⟩)
      have htri := hK hz'v hyv hr hz'y hyr hNz'.1
      have hzy : ({z', y} : Finset V) ∈ T := by rwa [pair_comm]
      have hyr' : ({y, r} : Finset V) ∈ T := by rwa [pair_comm]
      have hf : ({z', r} : Finset V) ∉ T := fun h => hNz'.2 (by rwa [pair_comm] at h)
      have hex := TreeExchange.mk hT.1 hz'y hyr hNz'.1 htri hzy hyr' hf
      have hT' := hT.exchange hz'y hyr hNz'.1 htri hzy hyr' hf
      have hmem : ({z', y} : Finset V) ∈ T.filter (fun e => r ∉ e) := by
        refine mem_filter.mpr ⟨hzy, ?_⟩
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨hNz'.1.symm, hyr.symm⟩
      have hfil : (insert ({z', r} : Finset V) (T.erase {z', y})).filter (fun e => r ∉ e) =
          (T.filter (fun e => r ∉ e)).erase {z', y} := by
        have hc : ¬ (r ∉ ({z', r} : Finset V)) := by simp
        rw [filter_insert]
        simp only [hc, ↓reduceIte]
        rw [filter_erase]
      have hlt : #((insert ({z', r} : Finset V) (T.erase {z', y})).filter (fun e => r ∉ e)) < n := by
        rw [hfil]
        exact lt_of_lt_of_eq (card_erase_lt_of_mem hmem) hn
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hex) (ih _ hlt _ hT' rfl)
  intro T T' hT hT'
  have hne : K.verts.Nonempty := card_pos.mp (by have := hT.2.card; omega)
  obtain ⟨r, hr⟩ := hne
  exact Relation.EqvGen.trans _ _ _ (main r hr _ T hT rfl)
    (Relation.EqvGen.symm _ _ (main r hr _ T' hT' rfl))

/-- The boundary of the 4-simplex: the five tetrahedra on `Fin 5` (a combinatorial 3-sphere). -/
def K5 : Complex3 (Fin 5) :=
  ⟨(Finset.univ : Finset (Fin 5)).powersetCard 4, by simp [mem_powersetCard]⟩

/-- The boundary of the 4-simplex has a complete 2-skeleton. -/
theorem K5_complete : ∀ ⦃x y z : Fin 5⦄, x ∈ K5.verts → y ∈ K5.verts → z ∈ K5.verts →
    x ≠ y → y ≠ z → x ≠ z → ({x, y, z} : Finset (Fin 5)) ∈ K5.tris := by
  decide

/-- **On the boundary of the 4-simplex all maximal trees are exchange-connected**, so the
gauge-fixed amplitude does not depend on the tree. -/
theorem treeConnected_K5 : TreeConnected K5 :=
  treeConnected_of_complete_triangles K5 K5_complete

/-- The gauge-fixed amplitude of the boundary of the 4-simplex is independent of the maximal tree,
for every cut-off. -/
theorem amplitudeGF_K5_eq {T T' : Finset (Finset (Fin 5))} (hT : IsMaxTree K5 T)
    (hT' : IsMaxTree K5 T') (cut : Finset (Fin 5) → ℕ) :
    amplitudeGF K5 T cut = amplitudeGF K5 T' cut :=
  treeConnected_K5.amplitudeGF_eq hT hT' cut

end Lightlike.PR
