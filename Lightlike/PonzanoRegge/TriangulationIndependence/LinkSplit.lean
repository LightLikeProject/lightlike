import Lightlike.PonzanoRegge.TriangulationIndependence.Rename

/-!
# Preparing the link of a vertex for the rename: stacking many tetrahedra at once

The rename of a vertex `v` by forward moves (`commonForward_rename_of_split`) needs the link of `v`
to split into two tree-shellable disks. The reduction that makes the link of `v` such a link starts
by stacking every tetrahedron through `v` with its own fresh vertex.

* `stackAll K S g`: every tetrahedron `t ∈ S` of `K` replaced by the four cones from the fresh
  vertex `g t` on the faces of `t`; `forwardMoves_stackAll`: it is reached by 1-4 moves;
* `link_stackAll_star`: after stacking the star of `v`, the link of `v` is the stacked link;
* `flipAll K v g Ed opp`: then, for each original link edge `{x, y}` in `Ed` (with its two opposite link
  triangles `opp`), the 2-3 move on the two stacked tetrahedra `{v, x, y, a}`, `{v, x, y, b}` through it;
  `forwardStep_flip`: flipping one more edge is one 2-3 move (`FlipData` collects the conditions).

**Limits.** That the link of `v` after all flips is the link `L''` of the reduction, and the shellability of the
pieces, are the next steps (not here).
-/

open Finset Lightlike.PL

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A four-element set lists its elements. -/
lemma exists_four {t : Finset V} (ht : #t = 4) :
    ∃ A B C D : V, A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧ t = {A, B, C, D} := by
  obtain ⟨A, t', hA, rfl, ht'⟩ := card_eq_succ.1 ht
  obtain ⟨B, C, D, hBC, hBD, hCD, rfl⟩ := card_eq_three.1 ht'
  simp only [mem_insert, mem_singleton, not_or] at hA
  exact ⟨A, B, C, D, hA.1, hA.2.1, hA.2.2, hBC, hBD, hCD, rfl⟩

/-- The cones from `e` on the four faces of `t`. -/
def stackPieces (t : Finset V) (e : V) : Finset (Finset V) := t.image fun x => insert e (t.erase x)

/-- **All the tetrahedra of `S` stacked**: every `t ∈ S` replaced by the four cones from `g t` on
its faces. -/
def stackAll (K : Complex3 V) (S : Finset (Finset V)) (g : Finset V → V) : Complex3 V where
  tets := ((K.tets \ S) ∪ S.biUnion fun t => stackPieces t (g t)).filter (#· = 4)
  card_eq _ h := (mem_filter.1 h).2

/-- The conditions for stacking `S` with the labels `g`: `S` consists of tetrahedra of `K`, and the
labels are fresh and distinct. -/
structure StackData (K : Complex3 V) (S : Finset (Finset V)) (g : Finset V → V) : Prop where
  sub : S ⊆ K.tets
  fresh : ∀ t ∈ S, g t ∉ K.verts
  inj : ∀ s ∈ S, ∀ t ∈ S, g s = g t → s = t

/-- Stacking data restrict to a subset of the tetrahedra. -/
lemma StackData.mono {K : Complex3 V} {S S' : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) (hS : S' ⊆ S) : StackData K S' g :=
  ⟨hS.trans h.sub, fun t ht => h.fresh t (hS ht), fun s hs t ht => h.inj s (hS hs) t (hS ht)⟩

/-- The pieces of a stacked tetrahedron `t` with apex `e` are the faces of `t` joined to `e`. -/
lemma mem_stackPieces {t : Finset V} {e : V} {s : Finset V} :
    s ∈ stackPieces t e ↔ ∃ x ∈ t, insert e (t.erase x) = s := by
  simp [stackPieces]

/-- A piece of a stacked tetrahedron has four vertices. -/
lemma card_stackPiece {K : Complex3 V} {t : Finset V} (ht : t ∈ K.tets) {e : V}
    (he : e ∉ K.verts) {x : V} (hx : x ∈ t) : #(insert e (t.erase x)) = 4 := by
  have het : e ∉ t := fun h => he (mem_biUnion.2 ⟨t, ht, h⟩)
  rw [card_insert_of_notMem (fun h => het (mem_of_mem_erase h)), card_erase_of_mem hx,
    K.card_eq t ht]

/-- Membership in `stackAll`. -/
lemma StackData.mem_stackAll {K : Complex3 V} {S : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) {s : Finset V} :
    s ∈ (stackAll K S g).tets ↔ (s ∈ K.tets ∧ s ∉ S) ∨ ∃ t ∈ S, ∃ x ∈ t, insert (g t) (t.erase x) = s := by
  simp only [stackAll, mem_filter, mem_union, mem_sdiff, mem_biUnion, mem_stackPieces]
  constructor
  · rintro ⟨h1 | h1, -⟩
    · exact .inl h1
    · exact .inr h1
  · rintro (h1 | ⟨t, ht, x, hx, rfl⟩)
    · exact ⟨.inl h1, K.card_eq s h1.1⟩
    · exact ⟨.inr ⟨t, ht, x, hx, rfl⟩, card_stackPiece (h.sub ht) (h.fresh t ht) hx⟩

/-- Two complexes with the same tetrahedra are equal. -/
lemma complex3_eq' {K L : Complex3 V} (h : ∀ t, t ∈ K.tets ↔ t ∈ L.tets) : K = L := by
  cases K; cases L; congr; ext t; exact h t

/-- **Stacking a set of tetrahedra is a chain of 1-4 moves.** -/
theorem forwardMoves_stackAll {K : Complex3 V} {S : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) : ForwardMoves K (stackAll K S g) := by
  induction S using Finset.induction_on with
  | empty =>
    have : stackAll K ∅ g = K := complex3_eq' fun s => by
      rw [(h.mono (empty_subset _)).mem_stackAll]
      simp
    rw [this]
    exact .refl
  | @insert t S htS ih =>
    have hS := h.mono (subset_insert t S)
    have ht : t ∈ K.tets := h.sub (mem_insert_self t S)
    obtain ⟨A, B, C, D, hAB, hAC, hAD, hBC, hBD, hCD, rfl⟩ := exists_four (K.card_eq t ht)
    have hE := h.fresh _ (mem_insert_self _ S)
    set E := g {A, B, C, D} with hEdef
    have hEt : ∀ x ∈ ({A, B, C, D} : Finset V), E ≠ x := fun x hx e =>
      hE (e ▸ mem_biUnion.2 ⟨_, ht, hx⟩)
    have h14 : IsMove14 (stackAll K S g) A B C D E := by
      refine ⟨hAB, hAC, hAD, Ne.symm (hEt A (by simp)), hBC, hBD, Ne.symm (hEt B (by simp)), hCD,
        Ne.symm (hEt C (by simp)), Ne.symm (hEt D (by simp)), ?_, ?_⟩
      · rw [hS.mem_stackAll]; exact .inl ⟨ht, htS⟩
      · intro s hs hEs
        rw [hS.mem_stackAll] at hs
        rcases hs with ⟨hs, -⟩ | ⟨u, hu, x, hx, rfl⟩
        · exact hE (mem_biUnion.2 ⟨s, hs, hEs⟩)
        · rcases mem_insert.1 hEs with e | e
          · exact htS (h.inj _ (mem_insert_self _ S) u (mem_insert_of_mem hu) e ▸ hu)
          · exact hE (mem_biUnion.2 ⟨u, h.sub (mem_insert_of_mem hu), mem_of_mem_erase e⟩)
    suffices e : move14 (stackAll K S g) h14 = stackAll K (insert {A, B, C, D} S) g by
      rw [← e]; exact (ih hS).tail (.m14 h14)
    refine complex3_eq' fun s => ?_
    rw [h.mem_stackAll]
    simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase, hS.mem_stackAll]
    have eA : insert E (({A, B, C, D} : Finset V).erase A) = {B, C, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eB : insert E (({A, B, C, D} : Finset V).erase B) = {A, C, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eC : insert E (({A, B, C, D} : Finset V).erase C) = {A, B, D, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have eD : insert E (({A, B, C, D} : Finset V).erase D) = {A, B, C, E} := by
      ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind
    have hne : ∀ u ∈ S, ∀ x ∈ u, insert (g u) (u.erase x) ≠ {A, B, C, D} := fun u hu x hx e => by
      have : g u ∈ ({A, B, C, D} : Finset V) := e ▸ mem_insert_self _ _
      exact h.fresh u (mem_insert_of_mem hu) (mem_biUnion.2 ⟨_, ht, this⟩)
    constructor
    · rintro ((rfl | rfl | rfl | rfl) | ⟨hsT, ⟨hs, hsS⟩ | ⟨u, hu, x, hx, rfl⟩⟩)
      · exact .inr ⟨_, .inl rfl, D, by simp, eD⟩
      · exact .inr ⟨_, .inl rfl, C, by simp, eC⟩
      · exact .inr ⟨_, .inl rfl, B, by simp, eB⟩
      · exact .inr ⟨_, .inl rfl, A, by simp, eA⟩
      · exact .inl ⟨hs, not_or.2 ⟨hsT, hsS⟩⟩
      · exact .inr ⟨u, .inr hu, x, hx, rfl⟩
    · rintro (⟨hs, hsS⟩ | ⟨u, hu, x, hx, rfl⟩)
      · rw [not_or] at hsS
        exact .inr ⟨hsS.1, .inl ⟨hs, hsS.2⟩⟩
      · rcases hu with rfl | hu
        · simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact .inl (.inr (.inr (.inr eA)))
          · exact .inl (.inr (.inr (.inl eB)))
          · exact .inl (.inr (.inl eC))
          · exact .inl (.inl eD)
        · exact .inr ⟨hne u hu x hx, .inr ⟨u, hu, x, hx, rfl⟩⟩


/-- The tetrahedra through `v`. -/
def starTets (K : Complex3 V) (v : V) : Finset (Finset V) := K.tets.filter (v ∈ ·)

/-- **The link of `v` after stacking its star** is the link of `v` with every triangle `τ` stacked
by the fresh vertex `g (insert v τ)` (the Kleetope of the link). -/
theorem StackData.link_stackAll_star {K : Complex3 V} {v : V} {g : Finset V → V}
    (h : StackData K (starTets K v) g) (hv : v ∈ K.verts) :
    (stackAll K (starTets K v) g).link v =
      (K.link v).biUnion fun τ => stackPieces τ (g (insert v τ)) := by
  ext σ
  rw [Complex3.mem_link, h.mem_stackAll, mem_biUnion]
  simp only [starTets, mem_filter, mem_stackPieces]
  have hgv : ∀ t ∈ K.tets, v ∈ t → g t ≠ v := fun t ht hvt e =>
    h.fresh t (mem_filter.2 ⟨ht, hvt⟩) (e ▸ hv)
  constructor
  · rintro ⟨hvσ, ⟨hK, hn⟩ | ⟨t, ⟨ht, hvt⟩, x, hx, e⟩⟩
    · exact absurd ⟨hK, mem_insert_self v σ⟩ hn
    · have hvmem : v ∈ insert (g t) (t.erase x) := e ▸ mem_insert_self v σ
      rcases mem_insert.1 hvmem with e' | e'
      · exact absurd e'.symm (hgv t ht hvt)
      · have hxv : x ≠ v := fun hx' => (ne_of_mem_erase e') hx'.symm
        refine ⟨t.erase v, Complex3.mem_link.2 ⟨notMem_erase v t, by rwa [insert_erase hvt]⟩,
          x, mem_erase.2 ⟨hxv, hx⟩, ?_⟩
        rw [insert_erase hvt]
        have h1 : σ = (insert (g t) (t.erase x)).erase v := by rw [e, erase_insert hvσ]
        have hg := hgv t ht hvt
        rw [h1]
        ext y
        simp only [mem_insert, mem_erase]
        grind
  · rintro ⟨τ, hτ, x, hx, rfl⟩
    obtain ⟨hvτ, hτK⟩ := Complex3.mem_link.1 hτ
    have hgv' := hgv _ hτK (mem_insert_self v τ)
    refine ⟨fun hm => ?_, .inr ⟨insert v τ, ⟨hτK, mem_insert_self v τ⟩, x, mem_insert_of_mem hx, ?_⟩⟩
    · rcases mem_insert.1 hm with e | e
      · exact hgv' e.symm
      · exact hvτ (mem_of_mem_erase e)
    · have hxv : x ≠ v := fun e => hvτ (e ▸ hx)
      ext y
      simp only [mem_insert, mem_erase]
      grind


/-! ## Flipping the original link edges -/

section Flip

variable {K : Complex3 V} {v : V} {g : Finset V → V}

/-- The data of the flips: for each original link edge `e ∈ Ed`, its two link triangles
`opp e = (τ, τ')`, with fresh labels `a e = g (v ∪ τ)`, `b e = g (v ∪ τ')`. -/
structure FlipData (K : Complex3 V) (v : V) (g : Finset V → V) (Ed : Finset (Finset V))
    (opp : Finset V → Finset V × Finset V) : Prop where
  stack : StackData K (starTets K v) g
  hv : v ∈ K.verts
  closed : IsClosed2 (K.link v)
  edge : ∀ e ∈ Ed, e ∈ edges2 (K.link v)
  fst : ∀ e ∈ Ed, (opp e).1 ∈ K.link v ∧ e ⊆ (opp e).1
  snd : ∀ e ∈ Ed, (opp e).2 ∈ K.link v ∧ e ⊆ (opp e).2
  ne : ∀ e ∈ Ed, (opp e).1 ≠ (opp e).2

/-- The fresh label of the first link triangle at `e`. -/
def flipA (v : V) (g : Finset V → V) (opp : Finset V → Finset V × Finset V) (e : Finset V) : V :=
  g (insert v (opp e).1)

/-- The fresh label of the second link triangle at `e`. -/
def flipB (v : V) (g : Finset V → V) (opp : Finset V → Finset V × Finset V) (e : Finset V) : V :=
  g (insert v (opp e).2)

/-- The two stacked tetrahedra through `v ∪ e`, removed by the flip of `e`. -/
def flipRemoved (v : V) (g : Finset V → V) (opp : Finset V → Finset V × Finset V)
    (e : Finset V) : Finset (Finset V) :=
  {insert v (insert (flipA v g opp e) e), insert v (insert (flipB v g opp e) e)}

/-- The three tetrahedra created by the flip of `e`: `e ∪ {a, b}` and `{v, x, a, b}`, `x ∈ e`. -/
def flipAdded (v : V) (g : Finset V → V) (opp : Finset V → Finset V × Finset V)
    (e : Finset V) : Finset (Finset V) :=
  insert (insert (flipA v g opp e) (insert (flipB v g opp e) e))
    (e.image fun x => insert v (insert x {flipA v g opp e, flipB v g opp e}))

/-- **The star of `v` stacked and the edges `Ed` of its original link flipped.** -/
def flipAll (K : Complex3 V) (v : V) (g : Finset V → V) (Ed : Finset (Finset V))
    (opp : Finset V → Finset V × Finset V) : Complex3 V where
  tets := (((stackAll K (starTets K v) g).tets \ Ed.biUnion (flipRemoved v g opp)) ∪
    Ed.biUnion (flipAdded v g opp)).filter (#· = 4)
  card_eq _ h := (mem_filter.1 h).2



/-- Two distinct triangles share at most one edge. -/
lemma edge_eq_of_inter {τ τ' e e' : Finset V} (h3 : #τ = 3) (h3' : #τ' = 3) (hne : τ ≠ τ')
    (he : e ⊆ τ ∩ τ') (he' : e' ⊆ τ ∩ τ') (h2 : #e = 2) (h2' : #e' = 2) : e = e' := by
  have hle : #(τ ∩ τ') ≤ 2 := by
    by_contra hc
    have h3i : #(τ ∩ τ') = 3 := le_antisymm (h3 ▸ card_le_card inter_subset_left) (by omega)
    have e1 : τ ∩ τ' = τ := eq_of_subset_of_card_le inter_subset_left (by omega)
    have e2 : τ ∩ τ' = τ' := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)
  have x1 := eq_of_subset_of_card_le he (by omega)
  have x2 := eq_of_subset_of_card_le he' (by omega)
  rw [x1, x2]

/-- Flip data restrict to a subset of the edges. -/
lemma FlipData.mono {Ed Ed' : Finset (Finset V)} {opp : Finset V → Finset V × Finset V}
    (h : FlipData K v g Ed opp) (hE : Ed' ⊆ Ed) : FlipData K v g Ed' opp :=
  ⟨h.stack, h.hv, h.closed, fun e he => h.edge e (hE he), fun e he => h.fst e (hE he),
    fun e he => h.snd e (hE he), fun e he => h.ne e (hE he)⟩

namespace FlipData

variable {Ed : Finset (Finset V)} {opp : Finset V → Finset V × Finset V}
variable (h : FlipData K v g Ed opp)
include h

omit h in
/-- A triangle of the link of `v` joined to `v` is a tetrahedron of the star of `v`. -/
lemma mem_starTets_of_link {τ : Finset V} (hτ : τ ∈ K.link v) : insert v τ ∈ starTets K v :=
  mem_filter.2 ⟨(Complex3.mem_link.1 hτ).2, mem_insert_self v τ⟩

/-- The first label of a flipped edge is a fresh vertex. -/
lemma a_fresh {e : Finset V} (he : e ∈ Ed) : flipA v g opp e ∉ K.verts :=
  h.stack.fresh _ (mem_starTets_of_link (h.fst e he).1)

/-- The second label of a flipped edge is a fresh vertex. -/
lemma b_fresh {e : Finset V} (he : e ∈ Ed) : flipB v g opp e ∉ K.verts :=
  h.stack.fresh _ (mem_starTets_of_link (h.snd e he).1)

/-- The two labels of a flipped edge are different. -/
lemma a_ne_b {e : Finset V} (he : e ∈ Ed) : flipA v g opp e ≠ flipB v g opp e := fun hab => by
  have := h.stack.inj _ (mem_starTets_of_link (h.fst e he).1) _ (mem_starTets_of_link (h.snd e he).1) hab
  exact h.ne e he (insert_left_inj (Complex3.mem_link.1 (h.fst e he).1).1
    (Complex3.mem_link.1 (h.snd e he).1).1 this)

/-- A fresh vertex is not on a flipped edge. -/
lemma notMem_of_fresh {x : V} (hx : x ∉ K.verts) {e : Finset V} (he : e ∈ Ed) : x ∉ e := fun hxe =>
  hx (mem_biUnion.2 ⟨_, (Complex3.mem_link.1 (h.fst e he).1).2,
    mem_insert_of_mem ((h.fst e he).2 hxe)⟩)

/-- The vertex `v` is not on a flipped edge. -/
lemma v_notMem {e : Finset V} (he : e ∈ Ed) : v ∉ e := fun hve =>
  (Complex3.mem_link.1 (h.fst e he).1).1 ((h.fst e he).2 hve)

/-- A fresh vertex is not `v`. -/
lemma ne_v_of_fresh {x : V} (hx : x ∉ K.verts) : x ≠ v := fun e => hx (e ▸ h.hv)

/-- A flipped edge has two vertices. -/
lemma card_e {e : Finset V} (he : e ∈ Ed) : #e = 2 := (mem_edges2.1 (h.edge e he)).choose_spec.2.2


/-- The vertices of a flipped edge are vertices of the complex. -/
lemma x_verts {e : Finset V} (he : e ∈ Ed) {x : V} (hx : x ∈ e) : x ∈ K.verts :=
  mem_biUnion.2 ⟨_, (Complex3.mem_link.1 (h.fst e he).1).2,
    mem_insert_of_mem ((h.fst e he).2 hx)⟩

/-- Membership in `flipAll`. -/
lemma mem_flipAll {t : Finset V} :
    t ∈ (flipAll K v g Ed opp).tets ↔
      (t ∈ (stackAll K (starTets K v) g).tets ∧ ∀ e ∈ Ed, t ∉ flipRemoved v g opp e) ∨
        ∃ e ∈ Ed, t ∈ flipAdded v g opp e := by
  simp only [flipAll, mem_filter, mem_union, mem_sdiff, mem_biUnion, not_exists, not_and]
  constructor
  · rintro ⟨h1 | h1, -⟩
    · exact .inl h1
    · exact .inr h1
  · rintro (h1 | ⟨e, he, ht⟩)
    · exact ⟨.inl h1, (stackAll K (starTets K v) g).card_eq t h1.1⟩
    · refine ⟨.inr ⟨e, he, ht⟩, ?_⟩
      have ha := h.a_fresh he
      have hb := h.b_fresh he
      have hab := h.a_ne_b he
      simp only [flipAdded, mem_insert, mem_image] at ht
      rcases ht with rfl | ⟨x, hx, rfl⟩
      · rw [card_insert_of_notMem (by
          rw [mem_insert, not_or]; exact ⟨hab, h.notMem_of_fresh ha he⟩),
          card_insert_of_notMem (h.notMem_of_fresh hb he), h.card_e he]
      · have hxv := h.x_verts he hx
        apply card_four
        · exact fun e' => h.v_notMem he (e' ▸ hx)
        · exact (h.ne_v_of_fresh ha).symm
        · exact (h.ne_v_of_fresh hb).symm
        · exact fun e' => ha (e' ▸ hxv)
        · exact fun e' => hb (e' ▸ hxv)
        · exact hab

end FlipData


/-- The link triangles through an edge `e ∈ Ed` are its two triangles `opp e`. -/
lemma FlipData.two {Ed : Finset (Finset V)} {opp : Finset V → Finset V × Finset V}
    (h : FlipData K v g Ed opp) {e : Finset V} (he : e ∈ Ed) {σ : Finset V}
    (hσ : σ ∈ K.link v) (heσ : e ⊆ σ) : σ = (opp e).1 ∨ σ = (opp e).2 := by
  have h2 := h.closed e (h.edge e he)
  have hsub : ({(opp e).1, (opp e).2} : Finset (Finset V)) ⊆ (K.link v).filter (e ⊆ ·) := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_filter.2 (h.fst e he)
    · exact mem_filter.2 (h.snd e he)
  have heq := eq_of_subset_of_card_le hsub (by rw [h2, card_pair (h.ne e he)])
  have : σ ∈ ({(opp e).1, (opp e).2} : Finset (Finset V)) := heq ▸ mem_filter.2 ⟨hσ, heσ⟩
  simpa using this

/-- The pair of fresh labels of a flip determines its edge. -/
lemma FlipData.edge_of_labels {Ed : Finset (Finset V)} {opp : Finset V → Finset V × Finset V}
    (h : FlipData K v g Ed opp) {e e' : Finset V} (he : e ∈ Ed) (he' : e' ∈ Ed)
    (h1 : flipA v g opp e' = flipA v g opp e ∨ flipA v g opp e' = flipB v g opp e)
    (h2 : flipB v g opp e' = flipA v g opp e ∨ flipB v g opp e' = flipB v g opp e) : e' = e := by
  have inj : ∀ {σ σ' : Finset V}, σ ∈ K.link v → σ' ∈ K.link v → g (insert v σ) = g (insert v σ') →
      σ = σ' := fun hσ hσ' e => insert_left_inj (Complex3.mem_link.1 hσ).1
        (Complex3.mem_link.1 hσ').1 (h.stack.inj _ (mem_starTets_of_link hσ) _ (mem_starTets_of_link hσ') e)
  have c1 := card_of_mem_link (h.fst e he).1
  have c2 := card_of_mem_link (h.snd e he).1
  have k1 : (opp e').1 = (opp e).1 ∨ (opp e').1 = (opp e).2 := by
    rcases h1 with e1 | e1
    · exact .inl (inj (h.fst e' he').1 (h.fst e he).1 e1)
    · exact .inr (inj (h.fst e' he').1 (h.snd e he).1 e1)
  have k2 : (opp e').2 = (opp e).1 ∨ (opp e').2 = (opp e).2 := by
    rcases h2 with e2 | e2
    · exact .inl (inj (h.snd e' he').1 (h.fst e he).1 e2)
    · exact .inr (inj (h.snd e' he').1 (h.snd e he).1 e2)
  have hsub' : e' ⊆ (opp e).1 ∩ (opp e).2 := by
    have hne' := h.ne e' he'
    rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
    · exact absurd (k1.trans k2.symm) hne'
    · rw [← k1, ← k2]; exact subset_inter (h.fst e' he').2 (h.snd e' he').2
    · rw [← k1, ← k2, inter_comm]; exact subset_inter (h.fst e' he').2 (h.snd e' he').2
    · exact absurd (k1.trans k2.symm) hne'
  exact edge_eq_of_inter c1 c2 (h.ne e he) hsub' (subset_inter (h.fst e he).2 (h.snd e he).2)
    (h.card_e he') (h.card_e he)


/-- A link triangle through the edge `{x, y}` is `{x, y}` plus a third vertex. -/
lemma third_vertex {τ : Finset V} (hτ : τ ∈ K.link v) {e : Finset V} (he : e ⊆ τ) (h2 : #e = 2) :
    ∃ z ∈ τ, z ∉ e ∧ ∀ y, y ∈ τ ↔ y ∈ e ∨ y = z := by
  have : #(τ \ e) = 1 := by rw [card_sdiff_of_subset he, card_of_mem_link hτ, h2]
  obtain ⟨z, hz⟩ := card_eq_one.1 this
  have hzτ : z ∈ τ \ e := hz ▸ mem_singleton_self z
  refine ⟨z, (mem_sdiff.1 hzτ).1, (mem_sdiff.1 hzτ).2, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · by_cases hye : y ∈ e
    · exact .inl hye
    · exact .inr (mem_singleton.1 (hz ▸ mem_sdiff.2 ⟨hy, hye⟩))
  · rintro (hy | rfl)
    · exact he hy
    · exact (mem_sdiff.1 hzτ).1

/-- **One flip**: the 2-3 move on `{v, x, y}` with apexes the fresh labels of the two link
triangles at `{x, y}`. -/
theorem forwardStep_flip {Ed : Finset (Finset V)} {opp : Finset V → Finset V × Finset V} {x y : V}
    (h : FlipData K v g (insert {x, y} Ed) opp) (hn : ({x, y} : Finset V) ∉ Ed) (hxy : x ≠ y) :
    ForwardStep (flipAll K v g Ed opp) (flipAll K v g (insert {x, y} Ed) opp) := by
  set e : Finset V := {x, y} with he_def
  have he : e ∈ insert e Ed := mem_insert_self e Ed
  have h0 := h.mono (subset_insert e Ed)
  have ha := h.a_fresh he
  have hb := h.b_fresh he
  have hab := h.a_ne_b he
  obtain ⟨a, ha_def⟩ : ∃ a, flipA v g opp e = a := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b, flipB v g opp e = b := ⟨_, rfl⟩
  rw [ha_def] at ha hab
  rw [hb_def] at hb hab
  have hxe : x ∈ e := by rw [he_def]; exact mem_insert_self x {y}
  have hye : y ∈ e := by rw [he_def]; exact mem_insert_of_mem (mem_singleton_self y)
  have hxV := h.x_verts he hxe
  have hyV := h.x_verts he hye
  have hve := h.v_notMem he
  have hvx : v ≠ x := fun e' => hve (e' ▸ hxe)
  have hvy : v ≠ y := fun e' => hve (e' ▸ hye)
  have hva : v ≠ a := (h.ne_v_of_fresh ha).symm
  have hvb : v ≠ b := (h.ne_v_of_fresh hb).symm
  have hxa : x ≠ a := fun e' => ha (e' ▸ hxV)
  have hxb : x ≠ b := fun e' => hb (e' ▸ hxV)
  have hya : y ≠ a := fun e' => ha (e' ▸ hyV)
  have hyb : y ≠ b := fun e' => hb (e' ▸ hyV)
  -- the two stacked tetrahedra through `v ∪ e`
  have piece : ∀ (τ : Finset V), τ ∈ K.link v → e ⊆ τ → ∃ z ∈ τ, z ∉ e ∧ z ≠ v ∧
      insert (g (insert v τ)) ((insert v τ).erase z) = insert v (insert (g (insert v τ)) e) := by
    intro τ hτ heτ
    obtain ⟨z, hzτ, hze, hiff⟩ := third_vertex hτ heτ (h.card_e he)
    have hzv : z ≠ v := fun e' => (Complex3.mem_link.1 hτ).1 (e' ▸ hzτ)
    refine ⟨z, hzτ, hze, hzv, ?_⟩
    ext w
    simp only [mem_insert, mem_erase, hiff]
    constructor
    · rintro (h1 | ⟨h1, h2 | h2 | h2⟩)
      · exact .inr (.inl h1)
      · exact .inl h2
      · exact .inr (.inr h2)
      · exact absurd h2 h1
    · rintro (h1 | h1 | h1)
      · exact .inr ⟨fun e' => hzv (e' ▸ h1), .inl h1⟩
      · exact .inl h1
      · exact .inr ⟨fun e' => hze (e' ▸ h1), .inr (.inl h1)⟩
  obtain ⟨z1, hz1τ, hz1e, hz1v, hp1⟩ := piece _ (h.fst e he).1 (h.fst e he).2
  obtain ⟨z2, hz2τ, hz2e, hz2v, hp2⟩ := piece _ (h.snd e he).1 (h.snd e he).2
  have hp1' := hp1
  have hp2' := hp2
  rw [show g (insert v (opp e).1) = a from ha_def] at hp1'
  rw [show g (insert v (opp e).2) = b from hb_def] at hp2'
  have pa : ({v, x, y, a} : Finset V) = insert v (insert a e) := by
    rw [he_def, insert_comm a x, pair_comm a y]
  have pb : ({v, x, y, b} : Finset V) = insert v (insert b e) := by
    rw [he_def, insert_comm b x, pair_comm b y]
  have inS_a : insert v (insert a e) ∈ (stackAll K (starTets K v) g).tets := by
    rw [h.stack.mem_stackAll]
    exact .inr ⟨(insert v (opp e).1 : Finset V), FlipData.mem_starTets_of_link (h.fst e he).1, z1, mem_insert_of_mem hz1τ,
      hp1.trans (by rw [show g (insert v (opp e).1) = a from ha_def])⟩
  have inS_b : insert v (insert b e) ∈ (stackAll K (starTets K v) g).tets := by
    rw [h.stack.mem_stackAll]
    exact .inr ⟨(insert v (opp e).2 : Finset V), FlipData.mem_starTets_of_link (h.snd e he).1, z2, mem_insert_of_mem hz2τ,
      hp2.trans (by rw [show g (insert v (opp e).2) = b from hb_def])⟩
  -- a removed or added tetrahedron of another flip is not one of these
  have key : ∀ (c d : V) (e' : Finset V), c ∉ K.verts → d ∉ K.verts → e' ∈ insert e Ed →
      insert v (insert c e') = insert v (insert d e) → e' = e := by
    intro c d e' hc hd he' heq
    have hve' := h.v_notMem he'
    have h1 := insert_left_inj (by rw [mem_insert, not_or]; exact ⟨(h.ne_v_of_fresh hc).symm, hve'⟩)
      (by rw [mem_insert, not_or]; exact ⟨(h.ne_v_of_fresh hd).symm, hve⟩) heq
    have hcd : c = d := by
      have : c ∈ insert d e := h1 ▸ mem_insert_self c e'
      rcases mem_insert.1 this with h2 | h2
      · exact h2
      · exact absurd h2 (h.notMem_of_fresh hc he)
    subst hcd
    exact insert_left_inj (h.notMem_of_fresh hc he') (h.notMem_of_fresh hc he) h1
  have notRem : ∀ e' ∈ Ed, ∀ t ∈ flipRemoved v g opp e', t ≠ insert v (insert a e) ∧
      t ≠ insert v (insert b e) := by
    intro e' he' t ht
    have he'' : e' ∈ insert e Ed := mem_insert_of_mem he'
    simp only [flipRemoved, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨fun h1 => hn (key _ _ _ (h.a_fresh he'') ha he'' h1 ▸ he'),
        fun h1 => hn (key _ _ _ (h.a_fresh he'') hb he'' h1 ▸ he')⟩
    · exact ⟨fun h1 => hn (key _ _ _ (h.b_fresh he'') ha he'' h1 ▸ he'),
        fun h1 => hn (key _ _ _ (h.b_fresh he'') hb he'' h1 ▸ he')⟩
  -- an added tetrahedron never contains `v`, `x` and `y`
  have addNoVXY : ∀ e' ∈ insert e Ed, ∀ t ∈ flipAdded v g opp e', ¬ (v ∈ t ∧ x ∈ t ∧ y ∈ t) := by
    intro e' he' t ht ⟨hvt, hxt, hyt⟩
    have ha' := h.a_fresh he'
    have hb' := h.b_fresh he'
    simp only [flipAdded, mem_insert, mem_image] at ht
    rcases ht with rfl | ⟨x', hx', rfl⟩
    · simp only [mem_insert] at hvt
      rcases hvt with h1 | h1 | h1
      · exact h.ne_v_of_fresh ha' h1.symm
      · exact h.ne_v_of_fresh hb' h1.symm
      · exact h.v_notMem he' h1
    · simp only [mem_insert, mem_singleton] at hxt hyt
      have xx : x = x' := by
        rcases hxt with h1 | h1 | h1 | h1
        exacts [absurd h1 hvx.symm, h1, absurd (h1 ▸ hxV) ha', absurd (h1 ▸ hxV) hb']
      have yy : y = x' := by
        rcases hyt with h1 | h1 | h1 | h1
        exacts [absurd h1 hvy.symm, h1, absurd (h1 ▸ hyV) ha', absurd (h1 ▸ hyV) hb']
      exact hxy (xx.trans yy.symm)
  have hgfresh : ∀ s ∈ starTets K v, g s ∉ K.verts := fun s hs => h.stack.fresh s hs
  have hgA : g (insert v (opp e).1) = a := ha_def
  have hgB : g (insert v (opp e).2) = b := hb_def
  -- a stacked tetrahedron through `v`, `x`, `y` is one of the two
  have stackVXY : ∀ s ∈ starTets K v, ∀ z ∈ s, v ∈ insert (g s) (s.erase z) →
      x ∈ insert (g s) (s.erase z) → y ∈ insert (g s) (s.erase z) →
      insert (g s) (s.erase z) = {v, x, y, a} ∨ insert (g s) (s.erase z) = {v, x, y, b} := by
    intro s hs z hz hvt hxt hyt
    obtain ⟨hsK, hvs⟩ := mem_filter.1 hs
    have hgs := hgfresh s hs
    have hσ : s.erase v ∈ K.link v :=
      Complex3.mem_link.2 ⟨notMem_erase v s, by rwa [insert_erase hvs]⟩
    have mem_σ : ∀ w ∈ insert (g s) (s.erase z), w ∈ K.verts → w ≠ v → w ∈ s.erase v :=
      fun w hw hwV hwv => by
        rcases mem_insert.1 hw with e1 | e1
        · exact absurd (e1 ▸ hwV) hgs
        · exact mem_erase.2 ⟨hwv, mem_of_mem_erase e1⟩
    have heσ : e ⊆ s.erase v := by
      rw [he_def]
      exact insert_subset (mem_σ x hxt hxV hvx.symm)
        (singleton_subset_iff.2 (mem_σ y hyt hyV hvy.symm))
    have hcard := card_stackPiece hsK hgs hz
    have hs' : s = insert v (s.erase v) := (insert_erase hvs).symm
    rcases h.two he hσ heσ with h1 | h1
    · left
      have hga : g s = a := by rw [hs', h1, hgA]
      refine (eq_of_subset_of_card_le ?_ ?_).symm
      · rw [← hga]
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        exacts [hvt, hxt, hyt, mem_insert_self _ _]
      · rw [hcard, card_four hvx hvy hva hxy hxa hya]
    · right
      have hgb : g s = b := by rw [hs', h1, hgB]
      refine (eq_of_subset_of_card_le ?_ ?_).symm
      · rw [← hgb]
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        exacts [hvt, hxt, hyt, mem_insert_self _ _]
      · rw [hcard, card_four hvx hvy hvb hxy hxb hyb]
  have h23 : IsMove23 (flipAll K v g Ed opp) v x y a b := by
    refine ⟨hvx, hvy, hva, hvb, hxy, hxa, hxb, hya, hyb, hab, ?_, ?_, ?_, ?_⟩
    · rw [h0.mem_flipAll, pa]
      exact .inl ⟨inS_a, fun e' he' hr => (notRem e' he' _ hr).1 rfl⟩
    · rw [h0.mem_flipAll, pb]
      exact .inl ⟨inS_b, fun e' he' hr => (notRem e' he' _ hr).2 rfl⟩
    · intro t ht hsub
      have hvt : v ∈ t := hsub (by simp)
      have hxt : x ∈ t := hsub (by simp)
      have hyt : y ∈ t := hsub (by simp)
      rw [h0.mem_flipAll] at ht
      rcases ht with ⟨hS, -⟩ | ⟨e', he', hadd⟩
      · rw [h.stack.mem_stackAll] at hS
        rcases hS with ⟨hK, hns⟩ | ⟨s, hs, z, hz, rfl⟩
        · exact absurd (mem_filter.2 ⟨hK, hvt⟩) hns
        · exact stackVXY s hs z hz hvt hxt hyt
      · exact absurd ⟨hvt, hxt, hyt⟩ (addNoVXY e' (mem_insert_of_mem he') t hadd)
    · intro t ht hsub
      have hat : a ∈ t := hsub (by simp)
      have hbt : b ∈ t := hsub (by simp)
      rw [h0.mem_flipAll] at ht
      rcases ht with ⟨hS, -⟩ | ⟨e', he', hadd⟩
      · rw [h.stack.mem_stackAll] at hS
        rcases hS with ⟨hK, -⟩ | ⟨s, hs, z, hz, rfl⟩
        · exact ha (mem_biUnion.2 ⟨t, hK, hat⟩)
        · have hsK := (mem_filter.1 hs).1
          have fa : a = g s := by
            rcases mem_insert.1 hat with e1 | e1
            · exact e1
            · exact absurd (mem_biUnion.2 ⟨s, hsK, mem_of_mem_erase e1⟩) ha
          have fb : b = g s := by
            rcases mem_insert.1 hbt with e1 | e1
            · exact e1
            · exact absurd (mem_biUnion.2 ⟨s, hsK, mem_of_mem_erase e1⟩) hb
          exact hab (fa.trans fb.symm)
      · have he'' : e' ∈ insert e Ed := mem_insert_of_mem he'
        have ha' := h.a_fresh he''
        have hb' := h.b_fresh he''
        have inPair : ∀ c, c ∉ K.verts → c ∈ t → c = flipA v g opp e' ∨ c = flipB v g opp e' := by
          intro c hc hct
          simp only [flipAdded, mem_insert, mem_image] at hadd
          rcases hadd with rfl | ⟨x', hx', rfl⟩
          · simp only [mem_insert] at hct
            rcases hct with h1 | h1 | h1
            · exact .inl h1
            · exact .inr h1
            · exact absurd h1 (h.notMem_of_fresh hc he'')
          · simp only [mem_insert, mem_singleton] at hct
            rcases hct with h1 | h1 | h1 | h1
            · exact absurd h1 (h.ne_v_of_fresh hc)
            · exact absurd (h1 ▸ h.x_verts he'' hx') hc
            · exact .inl h1
            · exact .inr h1
        have k1 := inPair a ha hat
        have k2 := inPair b hb hbt
        have : e' = e := by
          apply h.edge_of_labels he he''
          · rw [ha_def, hb_def]
            rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
            · exact absurd (k1.trans k2.symm) hab
            · exact .inl k1.symm
            · exact .inr k2.symm
            · exact absurd (k1.trans k2.symm) hab
          · rw [ha_def, hb_def]
            rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
            · exact absurd (k1.trans k2.symm) hab
            · exact .inr k2.symm
            · exact .inl k1.symm
            · exact absurd (k1.trans k2.symm) hab
        exact hn (this ▸ he')
  suffices eq : move23 (flipAll K v g Ed opp) h23 = flipAll K v g (insert e Ed) opp by
    rw [← eq]; exact .m23 h23
  have q1 : insert a (insert b e) = ({x, y, a, b} : Finset V) := by
    rw [he_def]; ext w; simp only [mem_insert, mem_singleton]
    constructor <;> intro hw <;> rcases hw with hw | hw | hw | hw <;> simp [hw]
  have q3 : insert v (insert y ({a, b} : Finset V)) = ({y, v, a, b} : Finset V) := insert_comm v y _
  refine complex3_eq' fun t => ?_
  rw [h.mem_flipAll]
  simp only [move23, mem_union, mem_insert, mem_singleton, mem_erase, h0.mem_flipAll,
    flipRemoved, flipAdded, mem_image, he_def]
  simp only [forall_eq_or_imp, exists_eq_or_imp]
  rw [show flipA v g opp {x, y} = a from ha_def, show flipB v g opp {x, y} = b from hb_def]
  have ea : insert v (insert a ({x, y} : Finset V)) = {v, x, y, a} := by rw [insert_comm a x, pair_comm a y]
  have eb : insert v (insert b ({x, y} : Finset V)) = {v, x, y, b} := by rw [insert_comm b x, pair_comm b y]
  have eab : insert a (insert b ({x, y} : Finset V)) = {x, y, a, b} := by rw [he_def] at q1; exact q1
  have eyv : ({v, y, a, b} : Finset V) = {y, v, a, b} := insert_comm v y _
  constructor
  · rintro ((h1 | h1 | h1) | ⟨hb', ha', (⟨hS, hall⟩ | hadd)⟩)
    · exact .inr (.inl (.inr ⟨x, by simp, h1.symm⟩))
    · exact .inr (.inl (.inl (by rw [eab]; exact h1)))
    · exact .inr (.inl (.inr ⟨y, by simp, by rw [h1]; exact eyv⟩))
    · refine .inl ⟨hS, ?_, hall⟩
      rintro (h2 | h2)
      · exact ha' (h2.trans ea)
      · exact hb' (h2.trans eb)
    · exact .inr (.inr hadd)
  · rintro (⟨hS, hn', hall⟩ | (h1 | ⟨w, hw, h1⟩) | ⟨e', he', hadd'⟩)
    · exact .inr ⟨fun h2 => hn' (.inr (h2.trans eb.symm)), fun h2 => hn' (.inl (h2.trans ea.symm)),
        .inl ⟨hS, hall⟩⟩
    · exact .inl (.inr (.inl (by rw [h1, eab])))
    · simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw <;> subst hw
      · exact .inl (.inl h1.symm)
      · exact .inl (.inr (.inr (by rw [← h1]; exact eyv)))
    · have hnot := addNoVXY e' (mem_insert_of_mem he') t (by
        simp only [flipAdded, mem_insert, mem_image]; exact hadd')
      exact .inr ⟨fun h2 => hnot (by rw [h2]; simp), fun h2 => hnot (by rw [h2]; simp),
        .inr ⟨e', he', hadd'⟩⟩

end Flip

end Lightlike.PR
