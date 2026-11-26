import Lightlike.PonzanoRegge.TriangulationIndependence.Main
import Lightlike.TuraevViro.PLInvariance

/-!
# The regularised Ponzano–Regge values do not depend on the names of the vertices

Relabelling a complex by an injective map `f` of the vertices (`mapComplex3`) transports maximal
trees, cut-offs and colourings, and keeps every weight: so every regularised value of `K` is one of
`mapComplex3 K f` (`ampValues_subset_mapComplex3`), and the two sets are equal for a bijection
(`ampValues_mapComplex3_equiv`). The Turaev–Viro analogue is `Lightlike.TV.Z_mapComplex3`; the edge,
triangle and triangle-sign lemmas are reused from there.
-/

open Finset Lightlike.PL

namespace Lightlike.PR

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The 6j weight of a tetrahedron is unchanged by a relabelling that transports the colouring. -/
lemma tetW_map (f : V ↪ W) {col : Colouring V} {col' : Colouring W}
    (h : ∀ e : Finset V, col' (e.map f) = col e) {t : Finset V} (ht : #t = 4) :
    tetW col' (t.map f) = tetW col t := by
  set p : Fin 4 → V := fun i => ((t.equivFinOfCardEq ht).symm i : V) with hp
  have hpi : Function.Injective p := fun i j hij =>
    (t.equivFinOfCardEq ht).symm.injective (Subtype.ext hij)
  have hpt : ∀ i, p i ∈ t := fun i => coe_mem _
  have hcard : #(t.map f) = 4 := by rw [card_map, ht]
  rw [tetW_eq_tetAmp col ht hpi hpt,
    tetW_eq_tetAmp col' hcard (p := f ∘ p) (f.injective.comp hpi)
      (fun i => mem_map_of_mem f (hpt i))]
  unfold tetAmp
  congr 1
  ext z
  induction z using Sym2.ind with
  | _ i k =>
    simp only [dualCol, Sym2.lift_mk]
    rw [← h, map_eq_image, image_image]

/-- **The weight is unchanged by a relabelling that transports the colouring.** -/
lemma weight_mapComplex3 (K : Complex3 V) (f : V ↪ W) {col : Colouring V} {col' : Colouring W}
    (h : ∀ e : Finset V, col' (e.map f) = col e) :
    weight (mapComplex3 K f) col' = weight K col := by
  have hinj : ∀ S : Finset (Finset V), Set.InjOn (Finset.map f) (S : Set (Finset V)) :=
    fun _ _ _ _ _ he => map_injective f he
  unfold weight
  rw [TV.edges_mapComplex3, TV.tris_mapComplex3,
    show (mapComplex3 K f).tets = K.tets.image (Finset.map f) from rfl,
    prod_image (hinj _), prod_image (hinj _), prod_image (hinj _)]
  congr 1
  · congr 1
    · exact prod_congr rfl fun e _ => by rw [h]
    · exact prod_congr rfl fun s _ => TV.triW_map f col col' s fun e _ => h e
  · exact prod_congr rfl fun t ht => tetW_map f h (K.card_eq t ht)

lemma verts_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    (mapComplex3 K f).verts = K.verts.map f := by
  ext w
  simp only [Complex3.verts, mapComplex3, mem_biUnion, mem_image, mem_map, id]
  constructor
  · rintro ⟨t', ⟨t, ht, rfl⟩, hw⟩
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hw
    exact ⟨v, ⟨t, ht, hv⟩, rfl⟩
  · rintro ⟨v, ⟨t, ht, hv⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, mem_map_of_mem f hv⟩

/-- A maximal tree of `K` relabels to a maximal tree of `mapComplex3 K f`. -/
lemma IsMaxTree.map {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T) (f : V ↪ W) :
    IsMaxTree (mapComplex3 K f) (T.image (Finset.map f)) := by
  obtain ⟨hsub, hsp⟩ := hT
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · rw [TV.edges_mapComplex3]; exact image_subset_image hsub
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    obtain ⟨h1, h2⟩ := hsp.edge e he
    rw [verts_mapComplex3]
    exact ⟨map_subset_map.2 h1, by rw [card_map, h2]⟩
  · intro u' hu' v' hv'
    rw [verts_mapComplex3] at hu' hv'
    obtain ⟨u, hu, rfl⟩ := mem_map.1 hu'
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hv'
    refine Relation.ReflTransGen.lift f (fun a b hab => ?_) (hsp.conn u hu v hv)
    refine mem_image.2 ⟨{a, b}, hab, ?_⟩
    simp [Finset.map_insert]
  · rw [card_image_of_injOn (fun _ _ _ _ he => map_injective f he), verts_mapComplex3,
      card_map, hsp.card]

/-- `extS` commutes with relabelling. -/
lemma extS_map (f : V ↪ W) (S : Finset (Finset V)) (σ' : ∀ e ∈ S.image (Finset.map f), ℕ)
    (e : Finset V) :
    extS (S.image (Finset.map f)) σ' (e.map f) =
      extS S (fun e he => σ' (e.map f) (mem_image_of_mem _ he)) e := by
  unfold extS
  by_cases he : e ∈ S
  · rw [dif_pos (mem_image_of_mem _ he), dif_pos he]
  · have : e.map f ∉ S.image (Finset.map f) := fun h => by
      obtain ⟨e', he', hee⟩ := mem_image.1 h
      exact he (map_injective f hee ▸ he')
    rw [dif_neg this, dif_neg he]

/-- **Relabelling keeps the gauge-fixed amplitude**, with the relabelled tree and cut-off. -/
theorem amplitudeGF_mapComplex3 (K : Complex3 V) (f : V ↪ W) (T : Finset (Finset V))
    (cut : Finset V → ℕ) :
    amplitudeGF (mapComplex3 K f) (T.image (Finset.map f))
        (fun e' => cut (e'.preimage f f.injective.injOn)) = amplitudeGF K T cut := by
  have hinj : ∀ S : Finset (Finset V), Set.InjOn (Finset.map f) (S : Set (Finset V)) :=
    fun _ _ _ _ _ he => map_injective f he
  have hS : (mapComplex3 K f).edges \ T.image (Finset.map f) = (K.edges \ T).image (Finset.map f) := by
    rw [TV.edges_mapComplex3, image_sdiff_of_injOn (hinj _) (by simp)]
  unfold amplitudeGF
  rw [hS]
  have hpre : ∀ e' ∈ (K.edges \ T).image (Finset.map f),
      e'.preimage f f.injective.injOn ∈ K.edges \ T := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    simpa [preimage_map] using he
  refine sum_bij' (fun σ' _ => fun e he => σ' (e.map f) (mem_image_of_mem _ he))
    (fun σ _ => fun e' he' => σ (e'.preimage f f.injective.injOn) (hpre e' he')) ?_ ?_ ?_ ?_ ?_
  · intro σ' hσ'
    rw [mem_pi] at hσ' ⊢
    intro e he
    simpa [preimage_map] using hσ' _ (mem_image_of_mem _ he)
  · intro σ hσ
    rw [mem_pi] at hσ ⊢
    exact fun e' he' => hσ _ _
  · intro σ' hσ'
    funext e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact TV.pi_dep_congr σ' (by simp [preimage_map]) _ _
  · intro σ hσ
    funext e he
    exact TV.pi_dep_congr σ (by simp [preimage_map]) _ _
  · intro σ' _
    exact weight_mapComplex3 K f fun e => extS_map f _ σ' e

/-- **Every regularised value of `K` is a regularised value of a relabelling of `K`.** -/
theorem ampValues_subset_mapComplex3 (K : Complex3 V) (f : V ↪ W) :
    ampValues K ⊆ ampValues (mapComplex3 K f) := by
  rintro a ⟨T, cut, hT, rfl⟩
  exact ⟨T.image (Finset.map f), _, hT.map f, amplitudeGF_mapComplex3 K f T cut⟩


/-! ## Forward moves commute with relabelling -/

lemma complex3_ext {K L : Complex3 V} (h : K.tets = L.tets) : K = L := by
  cases K; cases L; cases h; rfl

lemma map_four (f : V ↪ W) (A B C D : V) :
    ({A, B, C, D} : Finset V).map f = {f A, f B, f C, f D} := by
  simp [Finset.map_insert]

lemma map_three (f : V ↪ W) (A B C : V) : ({A, B, C} : Finset V).map f = {f A, f B, f C} := by
  simp [Finset.map_insert]

lemma map_two (f : V ↪ W) (A B : V) : ({A, B} : Finset V).map f = {f A, f B} := by
  simp [Finset.map_insert]

/-- The conditions of a 2-3 move are kept by an injective relabelling. -/
lemma IsMove23.map {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) (f : V ↪ W) :
    IsMove23 (mapComplex3 K f) (f A) (f B) (f C) (f D) (f E) where
  hAB := f.injective.ne h.hAB
  hAC := f.injective.ne h.hAC
  hAD := f.injective.ne h.hAD
  hAE := f.injective.ne h.hAE
  hBC := f.injective.ne h.hBC
  hBD := f.injective.ne h.hBD
  hBE := f.injective.ne h.hBE
  hCD := f.injective.ne h.hCD
  hCE := f.injective.ne h.hCE
  hDE := f.injective.ne h.hDE
  mem₁ := mem_image.2 ⟨_, h.mem₁, map_four f _ _ _ _⟩
  mem₂ := mem_image.2 ⟨_, h.mem₂, map_four f _ _ _ _⟩
  face t' ht' hsub := by
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    rw [← map_three] at hsub
    rcases h.face t ht (map_subset_map.1 hsub) with rfl | rfl
    · exact .inl (map_four f _ _ _ _)
    · exact .inr (map_four f _ _ _ _)
  fresh t' ht' hsub := by
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    rw [← map_two] at hsub
    exact h.fresh t ht (map_subset_map.1 hsub)

/-- The conditions of a 1-4 move are kept by an injective relabelling. -/
lemma IsMove14.map {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) (f : V ↪ W) :
    IsMove14 (mapComplex3 K f) (f A) (f B) (f C) (f D) (f E) where
  hAB := f.injective.ne h.hAB
  hAC := f.injective.ne h.hAC
  hAD := f.injective.ne h.hAD
  hAE := f.injective.ne h.hAE
  hBC := f.injective.ne h.hBC
  hBD := f.injective.ne h.hBD
  hBE := f.injective.ne h.hBE
  hCD := f.injective.ne h.hCD
  hCE := f.injective.ne h.hCE
  hDE := f.injective.ne h.hDE
  mem := mem_image.2 ⟨_, h.mem, map_four f _ _ _ _⟩
  fresh t' ht' hE := by
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    obtain ⟨x, hx, hxE⟩ := mem_map.1 hE
    exact h.fresh t ht (f.injective hxE ▸ hx)

lemma mapComplex3_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) (f : V ↪ W) :
    mapComplex3 (move23 K h) f = move23 (mapComplex3 K f) (h.map f) := by
  have hinj : Function.Injective (Finset.map f : Finset V → Finset W) := map_injective f
  apply complex3_ext
  simp only [mapComplex3, move23, image_union, image_insert, image_singleton,
    image_erase hinj, map_four]

lemma mapComplex3_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) (f : V ↪ W) :
    mapComplex3 (move14 K h) f = move14 (mapComplex3 K f) (h.map f) := by
  have hinj : Function.Injective (Finset.map f : Finset V → Finset W) := map_injective f
  apply complex3_ext
  simp only [mapComplex3, move14, image_union, image_insert, image_singleton,
    image_erase hinj, map_four]

/-- A forward move relabels to a forward move. -/
theorem ForwardStep.map {K K' : Complex3 V} (h : ForwardStep K K') (f : V ↪ W) :
    ForwardStep (mapComplex3 K f) (mapComplex3 K' f) := by
  cases h with
  | m23 h => rw [mapComplex3_move23 h f]; exact .m23 (h.map f)
  | m14 h => rw [mapComplex3_move14 h f]; exact .m14 (h.map f)

/-- **Forward chains commute with an injective relabelling.** -/
theorem ForwardMoves.map {K K' : Complex3 V} (h : ForwardMoves K K') (f : V ↪ W) :
    ForwardMoves (mapComplex3 K f) (mapComplex3 K' f) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.map f)

end Lightlike.PR
