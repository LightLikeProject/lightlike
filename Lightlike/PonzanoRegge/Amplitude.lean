module

public import Lightlike.PonzanoRegge.Local

/-!
# The Ponzano–Regge amplitude of a triangulation, and its invariance under the 2-3 move

## Definitions

* `Complex3 V`: a finite pure 3-dimensional simplicial complex on vertices `V`, given by its
  tetrahedra (4-element vertex sets). Edges and triangles are all 2- and 3-element faces.
  No manifold condition is imposed. The 2-3 theorem below holds for every such complex, so in
  particular for triangulated 3-manifolds.
* `weight K col`: the Ponzano–Regge weight of the complex `K` coloured by `col`, namely
  `∏_edges (2j+1)(-1)^{2j} · ∏_triangles (-1)^{j_a+j_b+j_c} · ∏_tetrahedra {6j}`.
* `amplitude K L`: the state sum over all colourings with spins `≤ L/2`. A cutoff is needed: for
  a closed manifold the unregularised Ponzano–Regge sum diverges.
* `move23 K A B C D E h`: the 2-3 Pachner move. Two tetrahedra `ABCD`, `ABCE` sharing the triangle
  `ABC` are replaced by the three tetrahedra `ABDE`, `BCDE`, `CADE` around the new edge `DE`.
  Preconditions (`IsMove23`): the five vertices are distinct, `ABC` lies in no other tetrahedron,
  and `DE` is not already an edge.

## Main results

* `weight_move23`: for every colouring, `weight K col = Σ_x weight K' col[DE ↦ x]`, with `x`
  running over all spins of the new edge. The range `x ≤ j_AD + j_AE` is complete, since larger
  `x` give `0` (`weight_move23_eq_zero`), which yields the `tsum` form `weight_move23_tsum`.
* `amplitude_move23`: the cut-off amplitude of `K` equals that of `K'` with the new edge summed
  over all its spins.

**Hypothesis:** both results take `BiedenharnElliott` as an argument. It is proven for all spins
(`Lightlike.Pentagon.biedenharnElliott`); `Unconditional.lean` gives the hypothesis-free versions. In
`amplitude_move23` only the edges of `K` are cut off: the new edge `DE` is summed over all its
spins (`tsum`), so this is not "cut-off amplitude of `K'` = cut-off amplitude of `K`".
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A finite pure 3-dimensional simplicial complex, given by its tetrahedra. -/
structure Complex3 (V : Type*) [DecidableEq V] where
  /-- The tetrahedra, as 4-element vertex sets. -/
  tets : Finset (Finset V)
  card_eq : ∀ t ∈ tets, #t = 4

namespace Complex3

/-- The edges: all 2-element faces of tetrahedra. -/
def edges (K : Complex3 V) : Finset (Finset V) := K.tets.biUnion (powersetCard 2)

/-- The triangles: all 3-element faces of tetrahedra. -/
def tris (K : Complex3 V) : Finset (Finset V) := K.tets.biUnion (powersetCard 3)

lemma mem_edges {K : Complex3 V} {s : Finset V} :
    s ∈ K.edges ↔ ∃ t ∈ K.tets, s ⊆ t ∧ #s = 2 := by
  simp [edges, mem_powersetCard]

lemma mem_tris {K : Complex3 V} {s : Finset V} :
    s ∈ K.tris ↔ ∃ t ∈ K.tets, s ⊆ t ∧ #s = 3 := by
  simp [tris, mem_powersetCard]

end Complex3

/-- Triangle weight `(-1)^{j_a+j_b+j_c}` of a 3-element vertex set (doubled units). -/
def triW (col : Colouring V) (f : Finset V) : ℝ := (-1) ^ ((∑ e ∈ f.powersetCard 2, col e) / 2)

/-- Tetrahedron weight: the 6j symbol, for any enumeration of the four vertices
(`tetW_eq_tetAmp`). -/
noncomputable def tetW (col : Colouring V) (t : Finset V) : ℝ :=
  if h : #t = 4 then tetAmp col (fun i => ((t.equivFinOfCardEq h).symm i : V)) else 0

/-- **The Ponzano–Regge weight** of a coloured complex. -/
noncomputable def weight (K : Complex3 V) (col : Colouring V) : ℝ :=
  (∏ e ∈ K.edges, edgeW (col e)) * (∏ f ∈ K.tris, triW col f) * ∏ t ∈ K.tets, tetW col t

/-- **The Ponzano–Regge amplitude** with cutoff: the sum of `weight` over all colourings of the
edges by doubled spins `≤ L`. -/
noncomputable def amplitude (K : Complex3 V) (L : ℕ) : ℝ :=
  ∑ c ∈ K.edges.pi (fun _ => range (L + 1)),
    weight K (fun e => if h : e ∈ K.edges then c e h else 0)

/-! ## The weights of explicit simplices -/

/-- The tetrahedron weight equals the 6j amplitude `tetAmp` for any enumeration of its four
vertices. -/
lemma tetW_eq_tetAmp (col : Colouring V) {t : Finset V} (ht : #t = 4) {p : Fin 4 → V}
    (hp : Function.Injective p) (hpt : ∀ i, p i ∈ t) : tetW col t = tetAmp col p := by
  rw [tetW, dite_eq_left_of_eq_true (eq_true ht)]
  exact (tetAmp_reindex col hp fun i =>
    ⟨t.equivFinOfCardEq ht ⟨p i, hpt i⟩, by simp⟩).symm

/-- `tetW` only depends on the colouring of the edges of the tetrahedron. -/
lemma tetW_congr {col col' : Colouring V} {t : Finset V}
    (h : ∀ e ⊆ t, #e = 2 → col e = col' e) : tetW col t = tetW col' t := by
  unfold tetW
  split_ifs with ht
  · refine tetAmp_congr fun i k hik => h _ ?_ ?_
    · intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl <;> exact coe_mem _
    · rw [card_pair]
      intro heq
      exact hik ((t.equivFinOfCardEq ht).symm.injective (Subtype.ext heq))
  · rfl

omit [DecidableEq V] in
lemma triW_congr {col col' : Colouring V} {f : Finset V}
    (h : ∀ e ⊆ f, #e = 2 → col e = col' e) : triW col f = triW col' f := by
  unfold triW
  congr 2
  exact sum_congr rfl fun e he => h e (mem_powersetCard.mp he).1 (mem_powersetCard.mp he).2

/-- The triangle weight of `{u, v, w}` is `triSign`. -/
lemma triW_three (col : Colouring V) {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    triW col {u, v, w} = triSign col u v w := by
  have hu : u ∉ ({v, w} : Finset V) := by simp [huv, huw]
  have hP : ({u, v, w} : Finset V).powersetCard 2 = {{v, w}, {u, v}, {u, w}} := by
    have hself : ({v, w} : Finset V).powersetCard 2 = {{v, w}} := by
      rw [← card_pair hvw, powersetCard_self]
    rw [show (2 : ℕ) = 1 + 1 from rfl, powersetCard_succ_insert hu, powersetCard_one]
    rw [show Nat.succ 1 = 2 from rfl, hself]
    ext s; simp only [mem_union, mem_image, mem_map, mem_insert, mem_singleton]; aesop
  have h1 : ({v, w} : Finset V) ∉ ({{u, v}, {u, w}} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hu (h ▸ mem_insert_self u {v}), fun h => hu (h ▸ mem_insert_self u {w})⟩
  have h2 : ({u, v} : Finset V) ≠ {u, w} := by
    intro h
    have : v ∈ ({u, w} : Finset V) := h ▸ mem_insert_of_mem (mem_singleton_self v)
    simp only [mem_insert, mem_singleton] at this
    tauto
  rw [triW, triSign, hP, sum_insert h1, sum_pair h2, pair_comm w u]
  congr 2
  ring

/-! ## The 2-3 Pachner move -/

/-- Preconditions of a 2-3 move on `K`: two tetrahedra `ABCD`, `ABCE` share the triangle `ABC`,
which lies in no other tetrahedron, and `DE` is not yet an edge. -/
structure IsMove23 (K : Complex3 V) (A B C D E : V) : Prop where
  hAB : A ≠ B
  hAC : A ≠ C
  hAD : A ≠ D
  hAE : A ≠ E
  hBC : B ≠ C
  hBD : B ≠ D
  hBE : B ≠ E
  hCD : C ≠ D
  hCE : C ≠ E
  hDE : D ≠ E
  mem₁ : {A, B, C, D} ∈ K.tets
  mem₂ : {A, B, C, E} ∈ K.tets
  face : ∀ t ∈ K.tets, {A, B, C} ⊆ t → t = {A, B, C, D} ∨ t = {A, B, C, E}
  fresh : ∀ t ∈ K.tets, ¬ {D, E} ⊆ t

omit [DecidableEq V] in
lemma card_four {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) [DecidableEq V] : #({a, b, c, d} : Finset V) = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_insert_of_notMem (by simp [hbc, hbd]),
    card_pair hcd]

omit [DecidableEq V] in
lemma card_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) [DecidableEq V] :
    #({a, b, c} : Finset V) = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

/-- **The 2-3 Pachner move**: replace `ABCD`, `ABCE` by `ABDE`, `BCDE`, `CADE`. -/
def move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) : Complex3 V where
  tets := {{A, B, D, E}, {B, C, D, E}, {C, A, D, E}} ∪ ((K.tets.erase {A, B, C, D}).erase {A, B, C, E})
  card_eq t ht := by
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact card_four h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE
      · exact card_four h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE
      · exact card_four h.hAC.symm h.hCD h.hCE h.hAD h.hAE h.hDE
    · exact K.card_eq t (mem_of_mem_erase (mem_of_mem_erase ht))

/-- If `s ⊆ T` misses `x` and `T` without `x` lies in `T'`, then `s ⊆ T'`. -/
lemma subset_of_not_mem {s T T' : Finset V} {x : V} (h : s ⊆ T) (hx : x ∉ s)
    (hT : T.erase x ⊆ T') : s ⊆ T' :=
  fun _ hy => hT (mem_erase.mpr ⟨fun h' => hx (h' ▸ hy), h hy⟩)

/-- An explicit inclusion between small vertex sets (closed by `simp` + `tauto`). -/
macro "small_subset" : tactic =>
  `(tactic| (intro _y hy; simp only [mem_erase, mem_insert, mem_singleton, ne_eq] at hy ⊢; tauto))

/-- If `D, E ∈ s` and `#s = 2` then `s = {D, E}`. -/
lemma eq_pair_of_mem {s : Finset V} {D E : V} (hDE : D ≠ E) (hD : D ∈ s) (hE : E ∈ s)
    (hs : #s = 2) : s = {D, E} := by
  have hsub : ({D, E} : Finset V) ⊆ s := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  exact (eq_of_subset_of_card_le hsub (by rw [hs, card_pair hDE])).symm

/-- A set of at most three elements other than `{a, b, c}` misses one of `a, b, c`. -/
lemma not_mem_of_card_le {s : Finset V} {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : #s ≤ 3) (hne : s ≠ {a, b, c}) : a ∉ s ∨ b ∉ s ∨ c ∉ s := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  have hsub : ({a, b, c} : Finset V) ⊆ s := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  exact hne (eq_of_subset_of_card_le hsub (by rw [card_three hab hac hbc]; exact hs)).symm

/-- Edges of the moved complex: the old ones plus `DE`. -/
theorem edges_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    (move23 K h).edges = insert {D, E} K.edges := by
  ext s
  simp only [Complex3.mem_edges, mem_insert, move23, mem_union, mem_erase]
  constructor
  · rintro ⟨t, ht, hst, hs⟩
    by_cases hD : D ∈ s
    · by_cases hE : E ∈ s
      · exact Or.inl (eq_pair_of_mem h.hDE hD hE hs)
      right
      simp only [mem_singleton] at ht
      rcases ht with (rfl | rfl | rfl) | ⟨-, -, ht⟩
      · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
      · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
      · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
      · exact ⟨t, ht, hst, hs⟩
    · right
      simp only [mem_singleton] at ht
      rcases ht with (rfl | rfl | rfl) | ⟨-, -, ht⟩
      · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
      · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
      · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
      · exact ⟨t, ht, hst, hs⟩
  · rintro (rfl | ⟨t, ht, hst, hs⟩)
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_pair h.hDE⟩
    have hne : s ≠ {A, B, C} := fun h' => by
      rw [h', card_three h.hAB h.hAC h.hBC] at hs; omega
    by_cases h1 : t = {A, B, C, D}
    · subst h1
      rcases not_mem_of_card_le h.hAB h.hAC h.hBC (by omega) hne with hA | hB | hC
      · exact ⟨{B, C, D, E}, by simp, subset_of_not_mem hst hA (by small_subset), hs⟩
      · exact ⟨{C, A, D, E}, by simp, subset_of_not_mem hst hB (by small_subset), hs⟩
      · exact ⟨{A, B, D, E}, by simp, subset_of_not_mem hst hC (by small_subset), hs⟩
    by_cases h2 : t = {A, B, C, E}
    · subst h2
      rcases not_mem_of_card_le h.hAB h.hAC h.hBC (by omega) hne with hA | hB | hC
      · exact ⟨{B, C, D, E}, by simp, subset_of_not_mem hst hA (by small_subset), hs⟩
      · exact ⟨{C, A, D, E}, by simp, subset_of_not_mem hst hB (by small_subset), hs⟩
      · exact ⟨{A, B, D, E}, by simp, subset_of_not_mem hst hC (by small_subset), hs⟩
    exact ⟨t, Or.inr ⟨h2, h1, ht⟩, hst, hs⟩

/-- `{u, D, E}` is not a face of `K` when `DE` is not an edge. -/
lemma not_mem_tris_of_fresh (K : Complex3 V) {D E : V} (hfresh : ∀ t ∈ K.tets, ¬ {D, E} ⊆ t)
    (u : V) : ({u, D, E} : Finset V) ∉ K.tris := by
  rw [Complex3.mem_tris]
  rintro ⟨t, ht, hst, -⟩
  exact hfresh t ht ((by small_subset : ({D, E} : Finset V) ⊆ {u, D, E}).trans hst)

/-- Triangles of the moved complex: the old ones without `ABC`, plus `ADE`, `BDE`, `CDE`. -/
theorem tris_move23 (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    (move23 K h).tris =
      insert {A, D, E} (insert {B, D, E} (insert {C, D, E} (K.tris.erase {A, B, C}))) := by
  ext s
  simp only [Complex3.mem_tris, mem_insert, move23, mem_union, mem_erase, mem_singleton]
  constructor
  · rintro ⟨t, ht, hst, hs⟩
    -- triangles of the three new tetrahedra
    have new : ∀ {X Y : V}, X ≠ Y → X ≠ D → X ≠ E → Y ≠ D → Y ≠ E → s ⊆ {X, Y, D, E} →
        D ∈ s → E ∈ s → s = {X, D, E} ∨ s = {Y, D, E} := by
      intro X Y hXY hXD hXE hYD hYE hsub hD hE
      by_cases hX : X ∈ s
      · by_cases hY : Y ∈ s
        · exfalso
          have := card_le_card (show ({X, Y, D, E} : Finset V) ⊆ s by
            intro z hz; simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption)
          rw [card_four hXY hXD hXE hYD hYE h.hDE, hs] at this; omega
        · left
          exact eq_of_subset_of_card_le (subset_of_not_mem hsub hY (by small_subset))
            (by rw [hs, card_three hXD hXE h.hDE])
      · right
        exact eq_of_subset_of_card_le (subset_of_not_mem hsub hX (by small_subset))
          (by rw [hs, card_three hYD hYE h.hDE])
    rcases ht with (rfl | rfl | rfl) | ⟨h2, h1, ht⟩
    · by_cases hDE : D ∈ s ∧ E ∈ s
      · rcases new h.hAB h.hAD h.hAE h.hBD h.hBE hst hDE.1 hDE.2 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · refine Or.inr (Or.inr (Or.inr ⟨fun h' => ?_, ?_⟩))
        · have : C ∈ ({A, B, D, E} : Finset V) := hst (h' ▸ by simp)
          simp only [mem_insert, mem_singleton] at this
          rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAC h''.symm;
            exact h.hBC h''.symm; exact h.hCD h''; exact h.hCE h'']
        · rcases not_and_or.mp hDE with hD | hE
          · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
          · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
    · by_cases hDE : D ∈ s ∧ E ∈ s
      · rcases new h.hBC h.hBD h.hBE h.hCD h.hCE hst hDE.1 hDE.2 with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inl h'))
      · refine Or.inr (Or.inr (Or.inr ⟨fun h' => ?_, ?_⟩))
        · have : A ∈ ({B, C, D, E} : Finset V) := hst (h' ▸ by simp)
          simp only [mem_insert, mem_singleton] at this
          rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAB h'';
            exact h.hAC h''; exact h.hAD h''; exact h.hAE h'']
        · rcases not_and_or.mp hDE with hD | hE
          · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
          · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
    · by_cases hDE : D ∈ s ∧ E ∈ s
      · rcases new h.hAC.symm h.hCD h.hCE h.hAD h.hAE hst hDE.1 hDE.2 with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inl h'
      · refine Or.inr (Or.inr (Or.inr ⟨fun h' => ?_, ?_⟩))
        · have : B ∈ ({C, A, D, E} : Finset V) := hst (h' ▸ by simp)
          simp only [mem_insert, mem_singleton] at this
          rcases this with h'' | h'' | h'' | h'' <;> [exact h.hBC h'';
            exact h.hAB h''.symm; exact h.hBD h''; exact h.hBE h'']
        · rcases not_and_or.mp hDE with hD | hE
          · exact ⟨_, h.mem₂, subset_of_not_mem hst hD (by small_subset), hs⟩
          · exact ⟨_, h.mem₁, subset_of_not_mem hst hE (by small_subset), hs⟩
    · refine Or.inr (Or.inr (Or.inr ⟨fun h' => ?_, t, ht, hst, hs⟩))
      rcases h.face t ht (h' ▸ hst) with h'' | h'' <;> [exact h1 h''; exact h2 h'']
  · rintro (rfl | rfl | rfl | ⟨hne, t, ht, hst, hs⟩)
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_three h.hAD h.hAE h.hDE⟩
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_three h.hBD h.hBE h.hDE⟩
    · exact ⟨{B, C, D, E}, by simp, by small_subset, card_three h.hCD h.hCE h.hDE⟩
    by_cases h1 : t = {A, B, C, D}
    · subst h1
      rcases not_mem_of_card_le h.hAB h.hAC h.hBC hs.le hne with hA | hB | hC
      · exact ⟨{B, C, D, E}, by simp, subset_of_not_mem hst hA (by small_subset), hs⟩
      · exact ⟨{C, A, D, E}, by simp, subset_of_not_mem hst hB (by small_subset), hs⟩
      · exact ⟨{A, B, D, E}, by simp, subset_of_not_mem hst hC (by small_subset), hs⟩
    by_cases h2 : t = {A, B, C, E}
    · subst h2
      rcases not_mem_of_card_le h.hAB h.hAC h.hBC hs.le hne with hA | hB | hC
      · exact ⟨{B, C, D, E}, by simp, subset_of_not_mem hst hA (by small_subset), hs⟩
      · exact ⟨{C, A, D, E}, by simp, subset_of_not_mem hst hB (by small_subset), hs⟩
      · exact ⟨{A, B, D, E}, by simp, subset_of_not_mem hst hC (by small_subset), hs⟩
    exact ⟨t, Or.inr ⟨h2, h1, ht⟩, hst, hs⟩

/-! ## Invariance of the weight and of the amplitude -/

/-- **Ponzano–Regge is invariant under the 2-3 move** (assuming the instance `BEAt` of
Biedenharn–Elliott that this colouring needs; `BiedenharnElliott` gives all of them): for every
colouring of `K`, the weight of `K` equals the weight of the moved complex summed over all spins
`x ≤ j_AD + j_AE` of the new edge `DE` (all other edges keep their spins). -/
theorem weight_move23 (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (col : Colouring V) (hBE : BEAt col A B C D E) :
    weight K col = ∑ x ∈ range (col {A, D} + col {A, E} + 1),
      weight (move23 K h) (Function.update col {D, E} x) := by
  set rest := (K.tets.erase {A, B, C, D}).erase {A, B, C, E} with hrest
  have hT12 : ({A, B, C, D} : Finset V) ≠ {A, B, C, E} := fun h' => by
    have : D ∈ ({A, B, C, E} : Finset V) := h' ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAD h''.symm; exact h.hBD h''.symm;
      exact h.hCD h''.symm; exact h.hDE h'']
  -- every simplex of `K` avoids the new edge, so `col` and `col[DE ↦ x]` agree on it
  have hagree : ∀ x, ∀ t ∈ K.tets, ∀ e ⊆ t, #e = 2 →
      col e = Function.update col {D, E} x e := by
    intro x t ht e het he
    rw [Function.update_of_ne]
    rintro rfl
    exact h.fresh t ht het
  have hDE_notin : ({D, E} : Finset V) ∉ K.edges := by
    rw [Complex3.mem_edges]; rintro ⟨t, ht, hst, -⟩; exact h.fresh t ht hst
  have hABC : ({A, B, C} : Finset V) ∈ K.tris :=
    Complex3.mem_tris.mpr ⟨_, h.mem₁, by small_subset, card_three h.hAB h.hAC h.hBC⟩
  have hnew : ∀ u, ({u, D, E} : Finset V) ∉ K.tris.erase {A, B, C} :=
    fun u hu => not_mem_tris_of_fresh K h.fresh u (mem_of_mem_erase hu)
  have hne3 : ∀ {u v : V}, u ≠ v → u ≠ D → u ≠ E → ({u, D, E} : Finset V) ≠ {v, D, E} := by
    intro u v huv huD huE h'
    have : u ∈ ({v, D, E} : Finset V) := h' ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    tauto
  have hfreshT : ∀ {u v : V}, ({u, v, D, E} : Finset V) ∉ rest := fun hmem =>
    h.fresh _ (mem_of_mem_erase (mem_of_mem_erase hmem)) (by small_subset)
  -- weight of `K`
  have hK : weight K col = (∏ e ∈ K.edges, edgeW (col e)) *
      (triW col {A, B, C} * ∏ f ∈ K.tris.erase {A, B, C}, triW col f) *
      (tetW col {A, B, C, D} * (tetW col {A, B, C, E} * ∏ t ∈ rest, tetW col t)) := by
    rw [hrest, weight, mul_prod_erase _ _ hABC,
      mul_prod_erase _ _ (mem_erase.mpr ⟨hT12.symm, h.mem₂⟩), mul_prod_erase _ _ h.mem₁]
  -- weight of the moved complex, term by term
  have hK' : ∀ x, weight (move23 K h) (Function.update col {D, E} x) =
      (edgeW x * (triW (Function.update col {D, E} x) {A, D, E} *
        triW (Function.update col {D, E} x) {B, D, E} *
        triW (Function.update col {D, E} x) {C, D, E}) *
      (tetW (Function.update col {D, E} x) {A, B, D, E} *
        tetW (Function.update col {D, E} x) {B, C, D, E} *
        tetW (Function.update col {D, E} x) {C, A, D, E})) *
      ((∏ e ∈ K.edges, edgeW (col e)) * (∏ f ∈ K.tris.erase {A, B, C}, triW col f) *
        ∏ t ∈ rest, tetW col t) := by
    intro x
    have he : ∏ e ∈ K.edges, edgeW (Function.update col {D, E} x e) =
        ∏ e ∈ K.edges, edgeW (col e) := by
      refine prod_congr rfl fun e he => ?_
      obtain ⟨t, ht, het, hc⟩ := Complex3.mem_edges.mp he
      rw [hagree x t ht e het hc]
    have hf : ∏ f ∈ K.tris.erase {A, B, C}, triW (Function.update col {D, E} x) f =
        ∏ f ∈ K.tris.erase {A, B, C}, triW col f := by
      refine prod_congr rfl fun f hf => ?_
      obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp (mem_of_mem_erase hf)
      exact (triW_congr fun e hef hc => hagree x t ht e (hef.trans hft) hc).symm
    have ht : ∏ t ∈ rest, tetW (Function.update col {D, E} x) t = ∏ t ∈ rest, tetW col t := by
      refine prod_congr rfl fun t ht => ?_
      exact (tetW_congr fun e het hc =>
        hagree x t (mem_of_mem_erase (mem_of_mem_erase ht)) e het hc).symm
    have hdisj : Disjoint ({{A, B, D, E}, {B, C, D, E}, {C, A, D, E}} : Finset (Finset V)) rest := by
      rw [disjoint_left]
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> exact hfreshT
    have h34 : ({A, B, D, E} : Finset V) ∉ ({{B, C, D, E}, {C, A, D, E}} : Finset (Finset V)) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h' => ?_, fun h' => ?_⟩
      · have : A ∈ ({B, C, D, E} : Finset V) := h' ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h'' | h'' <;> [exact h.hAB h''; exact h.hAC h'';
          exact h.hAD h''; exact h.hAE h'']
      · have : B ∈ ({C, A, D, E} : Finset V) := h' ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h'' | h'' <;> [exact h.hBC h''; exact h.hAB h''.symm;
          exact h.hBD h''; exact h.hBE h'']
    have h45 : ({B, C, D, E} : Finset V) ≠ {C, A, D, E} := fun h' => by
      have : B ∈ ({C, A, D, E} : Finset V) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h'' | h'' | h'' | h'' <;> [exact h.hBC h''; exact h.hAB h''.symm;
        exact h.hBD h''; exact h.hBE h'']
    rw [weight, edges_move23, tris_move23, prod_insert hDE_notin, he,
      prod_insert (by
        simp only [mem_insert, not_or]
        exact ⟨hne3 h.hAB h.hAD h.hAE, hne3 h.hAC h.hAD h.hAE, hnew A⟩),
      prod_insert (by
        simp only [mem_insert, not_or]
        exact ⟨hne3 h.hBC h.hBD h.hBE, hnew B⟩),
      prod_insert (hnew C), hf]
    simp only [move23]
    rw [prod_union hdisj, prod_insert h34, prod_pair h45, ht, Function.update_self]
    ring
  -- the local identity
  have hloc := pachner23_local col hBE h.hAB h.hAC h.hAD h.hAE h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE
  rw [← triW_three col h.hAB h.hAC h.hBC,
    ← tetW_eq_tetAmp col (card_four h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD)
      (injective_vec4 h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD) (by intro i; fin_cases i <;> simp),
    ← tetW_eq_tetAmp col (card_four h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE)
      (injective_vec4 h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE) (by intro i; fin_cases i <;> simp)]
    at hloc
  have hterm : ∀ x, edgeW x * (triSign (Function.update col {D, E} x) A D E *
        triSign (Function.update col {D, E} x) B D E *
        triSign (Function.update col {D, E} x) C D E) *
      (tetAmp (Function.update col {D, E} x) ![A, B, D, E] *
        tetAmp (Function.update col {D, E} x) ![B, C, D, E] *
        tetAmp (Function.update col {D, E} x) ![C, A, D, E]) =
      edgeW x * (triW (Function.update col {D, E} x) {A, D, E} *
        triW (Function.update col {D, E} x) {B, D, E} *
        triW (Function.update col {D, E} x) {C, D, E}) *
      (tetW (Function.update col {D, E} x) {A, B, D, E} *
        tetW (Function.update col {D, E} x) {B, C, D, E} *
        tetW (Function.update col {D, E} x) {C, A, D, E}) := by
    intro x
    rw [triW_three _ h.hAD h.hAE h.hDE, triW_three _ h.hBD h.hBE h.hDE,
      triW_three _ h.hCD h.hCE h.hDE,
      tetW_eq_tetAmp _ (card_four h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE)
        (injective_vec4 h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE) (by intro i; fin_cases i <;> simp),
      tetW_eq_tetAmp _ (card_four h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE)
        (injective_vec4 h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE) (by intro i; fin_cases i <;> simp),
      tetW_eq_tetAmp _ (card_four h.hAC.symm h.hCD h.hCE h.hAD h.hAE h.hDE)
        (injective_vec4 h.hAC.symm h.hCD h.hCE h.hAD h.hAE h.hDE)
        (by intro i; fin_cases i <;> simp)]
  simp only [hterm] at hloc
  simp only [hK']
  rw [← sum_mul, ← hloc, hK]
  ring

/-- Spins of the new edge beyond `j_AD + j_AE` contribute nothing (triangle inequality in `ADE`),
so the finite sum in `weight_move23` is the sum over *all* spins of the new edge. -/
theorem weight_move23_eq_zero (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    (col : Colouring V) {x : ℕ} (hx : col {A, D} + col {A, E} < x) :
    weight (move23 K h) (Function.update col {D, E} x) = 0 := by
  have hmem : ({A, B, D, E} : Finset V) ∈ (move23 K h).tets := by simp [move23]
  rw [weight, prod_eq_zero hmem, mul_zero]
  rw [tetW_eq_tetAmp _ (card_four h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE)
    (p := ![B, E, D, A]) (injective_vec4 h.hBE h.hBD h.hAB.symm h.hDE.symm h.hAE.symm h.hAD.symm)
    (by intro i; fin_cases i <;> simp), tetAmp_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [pair_comm D A, pair_comm E A, pair_comm E D, Function.update_self,
    Function.update_of_ne (pair_ne_of_not_mem h.hAD h.hAE),
    Function.update_of_ne (pair_ne_of_not_mem h.hAD h.hAE)]
  exact sixJSym_vanishes_beyond_range hx

/-- `weight_move23` with the new edge summed over **all** spins (`tsum`). -/
theorem weight_move23_tsum (hBE : BiedenharnElliott) (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (col : Colouring V) :
    ∑' x, weight (move23 K h) (Function.update col {D, E} x) = weight K col := by
  rw [weight_move23 K h col (beAt_of_biedenharnElliott hBE col A B C D E), tsum_eq_sum]
  intro x hx
  exact weight_move23_eq_zero K h col (by simpa using hx)

/-- **The cut-off amplitude is invariant under the 2-3 move**, the new edge being summed over all
its spins: `amplitude K L = Σ_{colourings of K with spins ≤ L} Σ_x weight K' (…)`. -/
theorem amplitude_move23 (hBE : BiedenharnElliott) (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (L : ℕ) :
    amplitude K L = ∑ c ∈ K.edges.pi (fun _ => range (L + 1)),
      ∑' x, weight (move23 K h)
        (Function.update (fun e => if he : e ∈ K.edges then c e he else 0) {D, E} x) := by
  refine sum_congr rfl fun c _ => ?_
  rw [weight_move23_tsum hBE K h]

end Lightlike.PR
