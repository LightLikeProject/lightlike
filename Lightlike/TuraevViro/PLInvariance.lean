import Lightlike.TuraevViro.LevelOne
import Lightlike.PL.PachnerMoves
import Lightlike.PL.Newman
import Lightlike.DynamicalTriangulations.Ergodicity3

/-!
# The Turaev–Viro state sum at `r = 3` up to PL homeomorphism

The `r = 3` Turaev–Viro state sum (`turaevViro (r := 3)`) is unchanged by all four 3D moves
(2-3 and 1-4 in `LevelOne.lean`, 3-2 and 4-1 here), by chains of them (`turaevViro3_moveEquiv3`),
and by an injective relabelling of the vertices (`turaevViro3_mapComplex3`; the colourings are
indexed by vertex sets, so the sum depends only on the combinatorics).

Combined with Newman's theorem (`SComplex.StellarEquiv.of_plHomeomorphic`) and the ergodicity of
the 3D moves on closed combinatorial 3-manifolds (`moveEquiv3_lift_iff_stellarEquiv`, from Pachner's
theorem), this gives **`turaevViro3_plHomeomorphic`**: PL homeomorphic closed combinatorial
3-manifolds have the same `r = 3` state sum.

## Main results

* `turaevViro3_move32`, `turaevViro3_move41`: the inverse moves.
* `Z_mapComplex3`, `turaevViro3_mapComplex3`: invariance under relabelling.
* `turaevViro3_moveEquiv3`: invariance along chains of 3D moves.
* `turaevViro3_plHomeomorphic`: invariance up to PL homeomorphism.

## What is not claimed

Only `r = 3`. For `r ≥ 4` the same argument needs q-Biedenharn–Elliott (`qBiedenharnElliott`,
open). Nothing here concerns the Ponzano–Regge amplitude: its regularised values are only
included in one another along forward moves (`TriangulationIndependence/`).

## References

* `turaev-1994`, Chapter VII (simplicial state sums on 3-manifolds); the comparison of the
  statement with the book is pending.
-/

open Finset Lightlike.PR Lightlike.PL
namespace Lightlike.TV
set_option linter.unusedSectionVars false
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- **The `r = 3` state sum is invariant under the 3-2 move**, the inverse of the 2-3 move. -/
theorem turaevViro3_move32 (K : Complex3 V) {A B C D E : V} (h : IsMove32 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move32 K h) = turaevViro (r := 3) (by norm_num) K := by
  have := turaevViro3_move23 (move32 K h) (isMove23_move32 h)
  rw [move23_move32 h] at this
  exact this.symm

/-- **The `r = 3` state sum is invariant under the 4-1 move**, the inverse of the 1-4 move. -/
theorem turaevViro3_move41 (K : Complex3 V) {A B C D E : V} (h : IsMove41 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move41 K h) = turaevViro (r := 3) (by norm_num) K := by
  have := turaevViro3_move14 (move41 K h) (isMove14_move41 h)
  rw [move14_move41 h] at this
  exact this.symm

/-- The edges of a relabelled complex are the relabelled edges. -/
lemma edges_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    (mapComplex3 K f).edges = K.edges.image (Finset.map f) := by
  ext s
  simp only [Complex3.mem_edges, mapComplex3, mem_image]
  constructor
  · rintro ⟨t', ⟨t, ht, rfl⟩, hs, h2⟩
    obtain ⟨u, hu, rfl⟩ := subset_map_iff.1 hs
    exact ⟨u, ⟨t, ht, hu, by simpa using h2⟩, rfl⟩
  · rintro ⟨u, ⟨t, ht, hu, h2⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, map_subset_map.2 hu, by simpa using h2⟩

/-- The triangles of a relabelled complex are the relabelled triangles. -/
lemma tris_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    (mapComplex3 K f).tris = K.tris.image (Finset.map f) := by
  ext s
  simp only [Complex3.mem_tris, mapComplex3, mem_image]
  constructor
  · rintro ⟨t', ⟨t, ht, rfl⟩, hs, h2⟩
    obtain ⟨u, hu, rfl⟩ := subset_map_iff.1 hs
    exact ⟨u, ⟨t, ht, hu, by simpa using h2⟩, rfl⟩
  · rintro ⟨u, ⟨t, ht, hu, h2⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, map_subset_map.2 hu, by simpa using h2⟩

/-- The vertices of a relabelled complex are the relabelled vertices. -/
lemma vertices_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    Model.vertices (mapComplex3 K f) = (Model.vertices K).map f := by
  ext w
  simp only [Model.vertices, mapComplex3, mem_biUnion, mem_image, mem_map, id]
  constructor
  · rintro ⟨t', ⟨t, ht, rfl⟩, hw⟩
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hw
    exact ⟨v, ⟨t, ht, hv⟩, rfl⟩
  · rintro ⟨v, ⟨t, ht, hv⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, mem_map_of_mem f hv⟩

/-- The sign of a triangle only depends on the colours of its edges. -/
lemma triW_map (f : V ↪ W) (col : Colouring V) (col' : Colouring W) (s : Finset V)
    (h : ∀ e ∈ s.powersetCard 2, col' (e.map f) = col e) :
    triW col' (s.map f) = triW col s := by
  unfold triW
  congr 2
  rw [powersetCard_map, sum_map]
  exact sum_congr rfl fun e he => by simpa using h e he

/-- The 6j weight of a tetrahedron only depends on the colours of its edges, not on the names of its vertices. -/
lemma tetW_map (M : Model) (f : V ↪ W) (col : Colouring V) (col' : Colouring W) (t : Finset V)
    (ht : #t = 4) (h : ∀ e ∈ t.powersetCard 2, col' (e.map f) = col e) :
    M.tetW col' (t.map f) = M.tetW col t := by
  set p : Fin 4 → V := fun i => ((t.equivFinOfCardEq ht).symm i : V) with hp
  have hpi : Function.Injective p := fun i j hij =>
    (t.equivFinOfCardEq ht).symm.injective (Subtype.ext hij)
  have hpt : ∀ i, p i ∈ t := fun i => coe_mem _
  have hcard : #(t.map f) = 4 := by rw [card_map, ht]
  rw [M.tetW_eq_tetAmp col ht hpi hpt,
    M.tetW_eq_tetAmp col' hcard (p := f ∘ p) (f.injective.comp hpi) (fun i => mem_map_of_mem f (hpt i))]
  rw [M.tetAmp_eq, M.tetAmp_eq]
  have key : ∀ i k, i ≠ k → col' {f (p i), f (p k)} = col {p i, p k} := by
    intro i k hik
    have hmem : ({p i, p k} : Finset V) ∈ t.powersetCard 2 := by
      rw [mem_powersetCard]
      refine ⟨?_, by rw [card_pair]; exact fun h => hik (hpi h)⟩
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact hpt _
    have := h _ hmem
    simpa [Finset.map_insert] using this
  simp only [Function.comp]
  rw [key 2 3 (by decide), key 1 3 (by decide), key 1 2 (by decide), key 0 1 (by decide),
    key 0 2 (by decide), key 0 3 (by decide)]

/-- The weight of a colouring is unchanged when the vertices are relabelled and the colouring is transported. -/
lemma weight_mapComplex3 (M : Model) (K : Complex3 V) (f : V ↪ W) (col : Colouring V)
    (col' : Colouring W) (h : ∀ e ∈ K.edges, col' (e.map f) = col e) :
    M.weight (mapComplex3 K f) col' = M.weight K col := by
  have hsub : ∀ s ∈ K.tris ∪ K.tets, ∀ e ∈ s.powersetCard 2, e ∈ K.edges := by
    intro s hs e he
    rw [mem_powersetCard] at he
    rw [Complex3.mem_edges]
    rcases mem_union.1 hs with hs | hs
    · obtain ⟨t, ht, hst, -⟩ := Complex3.mem_tris.1 hs
      exact ⟨t, ht, he.1.trans hst, he.2⟩
    · exact ⟨s, hs, he.1, he.2⟩
  unfold Model.weight
  rw [edges_mapComplex3, tris_mapComplex3]
  have hinj : Set.InjOn (Finset.map f) (K.edges : Set (Finset V)) := fun _ _ _ _ h => map_injective f h
  have hinj3 : Set.InjOn (Finset.map f) (K.tris : Set (Finset V)) := fun _ _ _ _ h => map_injective f h
  have hinj4 : Set.InjOn (Finset.map f) (K.tets : Set (Finset V)) := fun _ _ _ _ h => map_injective f h
  show (∏ e ∈ K.edges.image (Finset.map f), M.edgeW (col' e)) *
      (∏ g ∈ K.tris.image (Finset.map f), triW col' g) *
      ∏ t ∈ K.tets.image (Finset.map f), M.tetW col' t = _
  rw [prod_image hinj, prod_image hinj3, prod_image hinj4]
  have e1 : ∏ e ∈ K.edges, M.edgeW (col' (e.map f)) = ∏ e ∈ K.edges, M.edgeW (col e) :=
    prod_congr rfl fun e he => by rw [h e he]
  have e2 : ∏ s ∈ K.tris, triW col' (s.map f) = ∏ s ∈ K.tris, triW col s :=
    prod_congr rfl fun s hs => triW_map f col col' s
      (fun e he => h e (hsub s (mem_union_left _ hs) e he))
  have e3 : ∏ t ∈ K.tets, M.tetW col' (t.map f) = ∏ t ∈ K.tets, M.tetW col t :=
    prod_congr rfl fun t ht => tetW_map M f col col' t (K.card_eq t ht)
      (fun e he => h e (hsub t (mem_union_right _ ht) e he))
  rw [e1, e2, e3]

/-- Dependent functions on a finset agree at equal arguments. -/
lemma pi_dep_congr {E : Finset (Finset V)} (σ : ∀ e ∈ E, ℕ) {a b : Finset V} (h : a = b)
    (ha : a ∈ E) (hb : b ∈ E) : σ a ha = σ b hb := by subst h; rfl

/-- **The Turaev–Viro state sum does not depend on the names of the vertices**: it is the same for
the image of a complex under an injective relabelling. -/
theorem Z_mapComplex3 (M : Model) (K : Complex3 V) (f : V ↪ W) :
    M.Z (mapComplex3 K f) = M.Z K := by
  unfold Model.Z
  rw [vertices_mapComplex3, card_map, edges_mapComplex3]
  congr 1
  have hpre : ∀ e' ∈ K.edges.image (Finset.map f), e'.preimage f f.injective.injOn ∈ K.edges := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    simpa [preimage_map] using he
  refine sum_bij' (fun σ' _ => fun e he => σ' (e.map f) (mem_image_of_mem _ he))
    (fun σ _ => fun e' he' => σ (e'.preimage f f.injective.injOn) (hpre e' he')) ?_ ?_ ?_ ?_ ?_
  · intro σ' hσ'
    rw [mem_pi] at hσ' ⊢
    exact fun e he => hσ' _ _
  · intro σ hσ
    rw [mem_pi] at hσ ⊢
    exact fun e he => hσ _ _
  · intro σ' hσ'
    funext e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact pi_dep_congr σ' (by simp [preimage_map]) _ _
  · intro σ hσ
    funext e he
    exact pi_dep_congr σ (by simp [preimage_map]) _ _
  · intro σ' hσ'
    refine weight_mapComplex3 M K f _ _ fun e he => ?_
    simp [extS, he, mem_image_of_mem (Finset.map f) he]

open Lightlike.DynamicalTriangulations

/-- The `r = 3` state sum is the same along a single 3D move (2-3, 3-2, 1-4 or 4-1). -/
theorem turaevViro3_move3Step {K L : Complex3 V} (h : Move3Step K L) :
    turaevViro (r := 3) (by norm_num) K = turaevViro (r := 3) (by norm_num) L := by
  cases h with
  | move23 h => exact (turaevViro3_move23 _ h).symm
  | move32 h => exact (turaevViro3_move32 _ h).symm
  | move14 h => exact (turaevViro3_move14 _ h).symm
  | move41 h => exact (turaevViro3_move41 _ h).symm

/-- The `r = 3` state sum is the same along any chain of 3D moves. -/
theorem turaevViro3_moveEquiv3 {K L : Complex3 V} (h : MoveEquiv3 K L) :
    turaevViro (r := 3) (by norm_num) K = turaevViro (r := 3) (by norm_num) L := by
  induction h with
  | rel _ _ h => exact turaevViro3_move3Step h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The  state sum does not depend on the names of the vertices. -/
theorem turaevViro3_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    turaevViro (r := 3) (by norm_num) (mapComplex3 K f) = turaevViro (r := 3) (by norm_num) K :=
  Z_mapComplex3 _ K f

/-- **The `r = 3` Turaev–Viro state sum is an invariant of closed 3-manifolds up to PL
homeomorphism.** -/
theorem turaevViro3_plHomeomorphic {K L : Complex3 V} (hK : IsCombManifold K)
    (hKne : K.tets.Nonempty) (hLne : L.tets.Nonempty)
    (h : SComplex.PLHomeomorphic (ofComplex3 K) (ofComplex3 L)) :
    turaevViro (r := 3) (by norm_num) K = turaevViro (r := 3) (by norm_num) L := by
  have hmem : ∀ J : Complex3 V, J.tets.Nonempty → (∅ : Finset V) ∈ ofComplex3 J := by
    intro J ⟨t, ht⟩
    simp only [ofComplex3, SComplex.mem_closure]
    exact ⟨t, ht, empty_subset _⟩
  have h0 : ∅ ∈ ofComplex3 K ↔ ∅ ∈ ofComplex3 L :=
    ⟨fun _ => hmem L hLne, fun _ => hmem K hKne⟩
  have hs := SComplex.StellarEquiv.of_plHomeomorphic h0 h
  have hm := (moveEquiv3_lift_iff_stellarEquiv hK hKne).2 hs
  have := turaevViro3_moveEquiv3 hm
  rwa [turaevViro3_mapComplex3, turaevViro3_mapComplex3] at this
end Lightlike.TV
