import Lightlike.PonzanoRegge.TriangulationIndependence.Rename

/-!
# Preparing the link of a vertex for the rename: stacking many tetrahedra at once

The rename of a vertex `v` by forward moves (`commonForward_rename_of_split`) needs the link of `v`
to split into two tree-shellable disks. The reduction that makes the link of `v` such a link starts
by stacking every tetrahedron through `v` with its own fresh vertex.

* `stackAll K S g`: every tetrahedron `t ∈ S` of `K` replaced by the four cones from the fresh
  vertex `g t` on the faces of `t`; `forwardMoves_stackAll`: it is reached by 1-4 moves.
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

lemma StackData.mono {K : Complex3 V} {S S' : Finset (Finset V)} {g : Finset V → V}
    (h : StackData K S g) (hS : S' ⊆ S) : StackData K S' g :=
  ⟨hS.trans h.sub, fun t ht => h.fresh t (hS ht), fun s hs t ht => h.inj s (hS hs) t (hS ht)⟩

lemma mem_stackPieces {t : Finset V} {e : V} {s : Finset V} :
    s ∈ stackPieces t e ↔ ∃ x ∈ t, insert e (t.erase x) = s := by
  simp [stackPieces]

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


namespace FlipData

variable {Ed : Finset (Finset V)} {opp : Finset V → Finset V × Finset V}
variable (h : FlipData K v g Ed opp)
include h

omit h in
lemma star_mem {τ : Finset V} (hτ : τ ∈ K.link v) : insert v τ ∈ starTets K v :=
  mem_filter.2 ⟨(Complex3.mem_link.1 hτ).2, mem_insert_self v τ⟩

lemma a_fresh {e : Finset V} (he : e ∈ Ed) : flipA v g opp e ∉ K.verts :=
  h.stack.fresh _ (star_mem (h.fst e he).1)

lemma b_fresh {e : Finset V} (he : e ∈ Ed) : flipB v g opp e ∉ K.verts :=
  h.stack.fresh _ (star_mem (h.snd e he).1)

lemma a_ne_b {e : Finset V} (he : e ∈ Ed) : flipA v g opp e ≠ flipB v g opp e := fun hab => by
  have := h.stack.inj _ (star_mem (h.fst e he).1) _ (star_mem (h.snd e he).1) hab
  exact h.ne e he (insert_left_inj (Complex3.mem_link.1 (h.fst e he).1).1
    (Complex3.mem_link.1 (h.snd e he).1).1 this)

lemma notMem_of_fresh {x : V} (hx : x ∉ K.verts) {e : Finset V} (he : e ∈ Ed) : x ∉ e := fun hxe =>
  hx (mem_biUnion.2 ⟨_, (Complex3.mem_link.1 (h.fst e he).1).2,
    mem_insert_of_mem ((h.fst e he).2 hxe)⟩)

lemma v_notMem {e : Finset V} (he : e ∈ Ed) : v ∉ e := fun hve =>
  (Complex3.mem_link.1 (h.fst e he).1).1 ((h.fst e he).2 hve)

lemma ne_v_of_fresh {x : V} (hx : x ∉ K.verts) : x ≠ v := fun e => hx (e ▸ h.hv)

lemma card_e {e : Finset V} (he : e ∈ Ed) : #e = 2 := (mem_edges2.1 (h.edge e he)).choose_spec.2.2

end FlipData

end Flip

end Lightlike.PR
