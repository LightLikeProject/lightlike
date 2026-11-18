import Lightlike.GFT.DualVertexSets
import Lightlike.GFT.DualEuler
import Lightlike.Surfaces.Homology

/-!
# The dual of a colored graph in dimension 2 is a closed surface

The barycentric subdivision of the dual `Δ_G` of a colored graph `G` of dimension `2` (Gurau 2010, Section 5)
is a closed combinatorial surface (`Lightlike.Surfaces.IsSurface`): its vertices are the simplices of `Δ_G`, its
triangles are the flags `ρ₁ < ρ₂ < ρ₃` of simplices of ranks `1, 2, 3`. A flag is the data of a vertex `v` of `G`
(its top simplex `ρ₃`) and an order `(π 0, π 1, π 2)` of the three colors: `ρ₁` has the color `π 0`, `ρ₂` the
colors `π 0, π 1`, and both have the bubble containing `v`. The subdivision is a genuine set of vertex sets,
even where `Δ_G` itself has repeated simplices.
-/

open Finset Equiv Lightlike.PR
open scoped Classical

namespace Lightlike.GFT

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

variable (G : ColoredGraph 2 V)

/-- The simplices of the dual form a finite type. -/
noncomputable instance instFintypeDualSimplex : Fintype (DualSimplex G) :=
  inferInstanceAs (Fintype {p : Finset (Fin 3) × Finset V // ∃ v, p.2 = G.bubble (univ \ p.1) v})

/-- **The face of the top simplex `v` with the colors `S`**: the simplex with the colors `S` whose bubble
(of the other colors) contains `v`. -/
def face (S : Finset (Fin 3)) (v : V) : DualSimplex G :=
  ⟨(S, G.bubble (univ \ S) v), ⟨v, rfl⟩⟩

@[simp] lemma colors_face (S : Finset (Fin 3)) (v : V) : (face G S v).colors = S := rfl
@[simp] lemma bub_face (S : Finset (Fin 3)) (v : V) : (face G S v).bub = G.bubble (univ \ S) v := rfl

/-- Two faces are equal when they have the same colors and the vertices lie in one bubble. -/
lemma face_eq_face_iff {S T : Finset (Fin 3)} {v w : V} :
    face G S v = face G T w ↔ S = T ∧ w ∈ G.bubble (univ \ S) v := by
  constructor
  · intro h
    have h1 : S = T := congrArg DualSimplex.colors h
    have h2 : G.bubble (univ \ S) v = G.bubble (univ \ T) w := congrArg DualSimplex.bub h
    subst h1
    exact ⟨rfl, by rw [h2]; exact mem_bubble_self G _ w⟩
  · rintro ⟨rfl, h⟩
    exact DualSimplex.ext' rfl (bubble_eq_of_mem G _ h).symm

/-- The top simplex of `v` is the face with all colors. -/
lemma top_eq_face (v : V) : DualSimplex.top G v = face G univ v :=
  DualSimplex.ext' rfl (by simp [bubble_empty])

/-- The faces with the same colors at vertices of one bubble are equal. -/
lemma face_eq_of_mem {S : Finset (Fin 3)} {v w : V} (h : w ∈ G.bubble (univ \ S) v) :
    face G S v = face G S w := (face_eq_face_iff G).2 ⟨rfl, h⟩

/-- **The flag of a vertex `v` and an order `π` of the colors**: the faces of ranks `1, 2, 3`. -/
noncomputable def flag (v : V) (π : Perm (Fin 3)) : Finset (DualSimplex G) :=
  {face G {π 0} v, face G {π 0, π 1} v, face G univ v}

lemma mem_flag {v : V} {π : Perm (Fin 3)} {ρ : DualSimplex G} :
    ρ ∈ flag G v π ↔ ρ = face G {π 0} v ∨ ρ = face G {π 0, π 1} v ∨ ρ = face G univ v := by
  simp [flag]

lemma face_card_eq {S T : Finset (Fin 3)} {v w : V} (h : face G S v = face G T w) :
    S.card = T.card := by
  have := congrArg DualSimplex.colors h
  exact congrArg Finset.card this

lemma card_pair_colors (π : Perm (Fin 3)) : ({π 0, π 1} : Finset (Fin 3)).card = 2 := by
  rw [card_pair]
  exact fun h => absurd (π.injective h) (by decide)

/-- A flag has three elements. -/
lemma card_flag (v : V) (π : Perm (Fin 3)) : (flag G v π).card = 3 := by
  have c2 := card_pair_colors π
  have d1 : face G {π 0} v ≠ face G {π 0, π 1} v := fun h => by
    have := face_card_eq G h; simp at this
  have d2 : face G {π 0} v ≠ face G univ v := fun h => by
    have := face_card_eq G h; simp at this
  have d3 : face G {π 0, π 1} v ≠ face G univ v := fun h => by
    have := face_card_eq G h; simp at this
  unfold flag
  rw [card_insert_of_notMem (by simp [d1, d2]), card_insert_of_notMem (by simp [d3]), card_singleton]

lemma perm_ext_of_two (π σ : Perm (Fin 3)) (h0 : π 0 = σ 0) (h1 : π 1 = σ 1) : π = σ := by
  revert π σ; decide

/-- **A flag determines its vertex and its order of colors.** -/
lemma flag_injective : Function.Injective (fun p : V × Perm (Fin 3) => flag G p.1 p.2) := by
  rintro ⟨v, π⟩ ⟨w, σ⟩ h
  simp only at h
  have hm : ∀ ρ, ρ ∈ flag G v π → ρ ∈ flag G w σ := fun ρ hρ => h ▸ hρ
  have c2 := card_pair_colors π
  have c2' := card_pair_colors σ
  have ht : face G univ v = face G univ w := by
    rcases (mem_flag G).1 (hm _ ((mem_flag G).2 (Or.inr (Or.inr rfl)))) with h' | h' | h'
    · have := face_card_eq G h'; simp at this
    · have := face_card_eq G h'; simp at this
    · exact h'
  have hvw : v = w := by
    have := ((face_eq_face_iff G).1 ht).2
    rw [sdiff_self, Finset.bot_eq_empty, bubble_empty, mem_singleton] at this
    exact this.symm
  subst hvw
  have h0 : π 0 = σ 0 := by
    rcases (mem_flag G).1 (hm _ ((mem_flag G).2 (Or.inl rfl))) with h' | h' | h'
    · have := ((face_eq_face_iff G).1 h').1
      simpa using this
    · have := face_card_eq G h'; simp at this
    · have := face_card_eq G h'; simp at this
  have h1 : π 1 = σ 1 := by
    rcases (mem_flag G).1 (hm _ ((mem_flag G).2 (Or.inr (Or.inl rfl)))) with h' | h' | h'
    · have := face_card_eq G h'; simp at this
    · have := ((face_eq_face_iff G).1 h').1
      have hmem : π 1 ∈ ({σ 0, σ 1} : Finset (Fin 3)) := by rw [← this]; simp
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with e | e
      · exact absurd (by rw [← h0] at e; exact π.injective e) (by decide)
      · exact e
    · have := face_card_eq G h'; simp at this
  exact Prod.ext rfl (perm_ext_of_two π σ h0 h1)

/-- **The triangles of the subdivision of `Δ_G`**: the flags. -/
noncomputable def surf : Finset (Finset (DualSimplex G)) := univ.image fun p : V × Perm (Fin 3) => flag G p.1 p.2

lemma mem_surf {τ : Finset (DualSimplex G)} : τ ∈ surf G ↔ ∃ v π, flag G v π = τ := by
  simp [surf]

/-! ### The edges of the subdivision -/

omit [Fintype V] [DecidableEq V] in
lemma inv_ne_self (c : Fin 3) (v : V) : G.inv c v ≠ v := fun h => by
  have := G.sign_inv c v
  rw [h] at this
  exact this rfl

lemma perm_pair_swap01 : ∀ π σ : Perm (Fin 3),
    ({π 0, π 1} : Finset (Fin 3)) = {σ 0, σ 1} → σ = π ∨ σ = π * swap 0 1 := by decide

lemma perm_single_swap12 : ∀ π σ : Perm (Fin 3), π 0 = σ 0 → σ = π ∨ σ = π * swap 1 2 := by decide

lemma compl_pair (π : Perm (Fin 3)) : (univ \ {π 0, π 1} : Finset (Fin 3)) = {π 2} := by
  revert π; decide

/-- **An edge lies in exactly two flags**, given the two flags, the first one containing it, the second one
containing it too, and no other. -/
lemma card_filter_two {f : Finset (DualSimplex G)} {p q : V × Perm (Fin 3)}
    (hp : f ⊆ flag G p.1 p.2) (hq : f ⊆ flag G q.1 q.2) (hne : p ≠ q)
    (hall : ∀ u σ, f ⊆ flag G u σ → (u, σ) = p ∨ (u, σ) = q) :
    ((surf G).filter (f ⊆ ·)).card = 2 := by
  rw [card_eq_two]
  refine ⟨flag G p.1 p.2, flag G q.1 q.2, fun h => hne (flag_injective G h), ?_⟩
  ext τ
  simp only [mem_filter, mem_surf, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨u, σ, rfl⟩, hf⟩
    rcases hall u σ hf with h | h
    · left; rw [← h]
    · right; rw [← h]
  · rintro (rfl | rfl)
    · exact ⟨⟨p.1, p.2, rfl⟩, hp⟩
    · exact ⟨⟨q.1, q.2, rfl⟩, hq⟩

/-- Membership of a face of rank `3` in a flag. -/
lemma mem_flag_rank3 {v u : V} {σ : Perm (Fin 3)} (h : face G univ v ∈ flag G u σ) : v = u := by
  have c2 := card_pair_colors σ
  rcases (mem_flag G).1 h with h' | h' | h'
  · have := face_card_eq G h'; simp at this
  · have := face_card_eq G h'; simp at this
  · have := ((face_eq_face_iff G).1 h').2
    rw [sdiff_self, Finset.bot_eq_empty, bubble_empty, mem_singleton] at this
    exact this.symm

/-- Membership of a face of rank `2` in a flag. -/
lemma mem_flag_rank2 {S : Finset (Fin 3)} {v u : V} {σ : Perm (Fin 3)} (hS : S.card = 2)
    (h : face G S v ∈ flag G u σ) : S = {σ 0, σ 1} ∧ u ∈ G.bubble (univ \ S) v := by
  have c2 := card_pair_colors σ
  rcases (mem_flag G).1 h with h' | h' | h'
  · have := face_card_eq G h'; simp at this; omega
  · exact (face_eq_face_iff G).1 h'
  · have := face_card_eq G h'; simp at this; omega

/-- Membership of a face of rank `1` in a flag. -/
lemma mem_flag_rank1 {S : Finset (Fin 3)} {v u : V} {σ : Perm (Fin 3)} (hS : S.card = 1)
    (h : face G S v ∈ flag G u σ) : S = {σ 0} ∧ u ∈ G.bubble (univ \ S) v := by
  have c2 := card_pair_colors σ
  rcases (mem_flag G).1 h with h' | h' | h'
  · exact (face_eq_face_iff G).1 h'
  · have := face_card_eq G h'; simp at this; omega
  · have := face_card_eq G h'; simp at this; omega

/-- The faces of a flag with other vertices in the same bubbles. -/
lemma flag_swap01 (v : V) (π : Perm (Fin 3)) :
    face G {π 0, π 1} v ∈ flag G v (π * swap 0 1) ∧ face G univ v ∈ flag G v (π * swap 0 1) := by
  refine ⟨?_, by simp [flag]⟩
  simp [flag, Finset.pair_comm]

lemma flag_swap12 (v : V) (π : Perm (Fin 3)) :
    face G {π 0} v ∈ flag G v (π * swap 1 2) ∧ face G univ v ∈ flag G v (π * swap 1 2) := by
  have h0 : (swap (1 : Fin 3) 2) 0 = 0 := by decide
  refine ⟨?_, by simp [flag]⟩
  simp [flag, h0]

/-! ### Every edge lies in exactly two triangles -/

/-- The edge `{ρ₂, ρ₃}` of a flag lies in the two flags `π` and `π ∘ (0 1)`. -/
lemma closed_23 (v : V) (π : Perm (Fin 3)) :
    ((surf G).filter ({face G {π 0, π 1} v, face G univ v} ⊆ ·)).card = 2 := by
  refine card_filter_two G (p := (v, π)) (q := (v, π * swap 0 1)) ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [flag]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (flag_swap01 G v π).1
    · exact (flag_swap01 G v π).2
  · intro h
    have := (Prod.ext_iff.1 h).2
    have h2 := congrArg (fun σ : Perm (Fin 3) => σ 0) this
    simp at h2
  · intro u σ hf
    have h3 := hf (by simp : face G univ v ∈ _)
    have h2 := hf (by simp : face G {π 0, π 1} v ∈ _)
    have hu := mem_flag_rank3 G h3
    subst hu
    have := (mem_flag_rank2 G (card_pair_colors π) h2).1
    rcases perm_pair_swap01 π σ this with rfl | rfl
    · left; rfl
    · right; rfl

/-- The edge `{ρ₁, ρ₃}` of a flag lies in the two flags `π` and `π ∘ (1 2)`. -/
lemma closed_13 (v : V) (π : Perm (Fin 3)) :
    ((surf G).filter ({face G {π 0} v, face G univ v} ⊆ ·)).card = 2 := by
  refine card_filter_two G (p := (v, π)) (q := (v, π * swap 1 2)) ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [flag]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (flag_swap12 G v π).1
    · exact (flag_swap12 G v π).2
  · intro h
    have := (Prod.ext_iff.1 h).2
    have h2 := congrArg (fun σ : Perm (Fin 3) => σ 1) this
    simp at h2
  · intro u σ hf
    have h3 := hf (by simp : face G univ v ∈ _)
    have h1 := hf (by simp : face G {π 0} v ∈ _)
    have hu := mem_flag_rank3 G h3
    subst hu
    have := (mem_flag_rank1 G (by simp) h1).1
    have h0 : π 0 = σ 0 := by simpa using this
    rcases perm_single_swap12 π σ h0 with rfl | rfl
    · left; rfl
    · right; rfl

lemma perm_pair_first : ∀ π σ : Perm (Fin 3),
    ({π 0, π 1} : Finset (Fin 3)) = {σ 0, σ 1} → π 0 = σ 0 → π 1 = σ 1 := by decide

/-- The edge `{ρ₁, ρ₂}` of a flag lies in the flag and in the flag of the other end of the line of the
third color. -/
lemma closed_12 (v : V) (π : Perm (Fin 3)) :
    ((surf G).filter ({face G {π 0} v, face G {π 0, π 1} v} ⊆ ·)).card = 2 := by
  have hc2 : G.inv (π 2) v ∈ G.bubble (univ \ {π 0, π 1}) v := by
    rw [compl_pair, bubble_singleton]; simp
  have hc1 : G.inv (π 2) v ∈ G.bubble (univ \ {π 0}) v := by
    refine bubble_mono G ?_ v hc2
    intro x hx
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton] at hx ⊢
    exact fun h => hx (Or.inl h)
  refine card_filter_two G (p := (v, π)) (q := (G.inv (π 2) v, π)) ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> simp [flag]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_flag G).2 (Or.inl ((face_eq_face_iff G).2 ⟨rfl, hc1⟩))
    · exact (mem_flag G).2 (Or.inr (Or.inl ((face_eq_face_iff G).2 ⟨rfl, hc2⟩)))
  · intro h
    exact inv_ne_self G (π 2) v (congrArg Prod.fst h).symm
  · intro u σ hf
    have h1 := hf (by simp : face G {π 0} v ∈ _)
    have h2 := hf (by simp : face G {π 0, π 1} v ∈ _)
    obtain ⟨e1, -⟩ := mem_flag_rank1 G (by simp) h1
    obtain ⟨e2, hu⟩ := mem_flag_rank2 G (card_pair_colors π) h2
    have h0 : π 0 = σ 0 := by simpa using e1
    have h1' : π 1 = σ 1 := perm_pair_first π σ e2 h0
    have hσ : σ = π := (perm_ext_of_two π σ h0 h1').symm
    subst hσ
    rw [compl_pair, bubble_singleton] at hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · left; rfl
    · right; rfl

/-- Every triangle of the subdivision has three vertices. -/
lemma isTri2_surf : IsTri2 (surf G) := by
  intro τ hτ
  obtain ⟨v, π, rfl⟩ := (mem_surf G).1 hτ
  exact card_flag G v π

/-- **Every edge of the subdivision lies in exactly two triangles.** -/
lemma isClosed2_surf : IsClosed2 (surf G) := by
  intro f hf
  obtain ⟨τ, hτ, hfτ, hc⟩ := mem_edges2.1 hf
  obtain ⟨v, π, rfl⟩ := (mem_surf G).1 hτ
  rcases pair_of_sub3 (p := face G {π 0} v) (q := face G {π 0, π 1} v) (r := face G univ v) hfτ hc with
    rfl | rfl | rfl
  · exact closed_12 G v π
  · exact closed_13 G v π
  · exact closed_23 G v π

/-! ### The 1-skeleton is connected -/

lemma mem_verts2_surf {x : DualSimplex G} : x ∈ verts2 (surf G) ↔ ∃ v π, x ∈ flag G v π := by
  rw [mem_verts2]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨v, π, rfl⟩ := (mem_surf G).1 hτ
    exact ⟨v, π, hx⟩
  · rintro ⟨v, π, hx⟩
    exact ⟨flag G v π, (mem_surf G).2 ⟨v, π, rfl⟩, hx⟩

/-- Two distinct vertices of a flag are joined by an edge. -/
lemma edge_of_flag {x y : DualSimplex G} {v : V} {π : Perm (Fin 3)} (hx : x ∈ flag G v π)
    (hy : y ∈ flag G v π) (hxy : x ≠ y) : ({x, y} : Finset (DualSimplex G)) ∈ edges2 (surf G) :=
  pair_mem_edges2 ((mem_surf G).2 ⟨v, π, rfl⟩) hx hy hxy

lemma edge_symm {x y : DualSimplex G} :
    ({x, y} : Finset (DualSimplex G)) ∈ edges2 (surf G) ↔ ({y, x} : Finset (DualSimplex G)) ∈ edges2 (surf G) := by
  rw [Finset.pair_comm]

/-- Every vertex of a flag is joined to the top simplex of the flag. -/
lemma conn_top {x : DualSimplex G} {v : V} {π : Perm (Fin 3)} (hx : x ∈ flag G v π) :
    Relation.ReflTransGen (fun a b => ({a, b} : Finset (DualSimplex G)) ∈ edges2 (surf G)) x
      (face G univ v) := by
  by_cases h : x = face G univ v
  · rw [h]
  · exact Relation.ReflTransGen.single
      (edge_of_flag G hx ((mem_flag G).2 (Or.inr (Or.inr rfl))) h)

lemma exists_perm_two (c : Fin 3) : ∃ π : Perm (Fin 3), π 2 = c := ⟨swap 2 c, by simp⟩

/-- The tops of the two ends of a line are joined. -/
lemma conn_line (v : V) (c : Fin 3) :
    Relation.ReflTransGen (fun a b => ({a, b} : Finset (DualSimplex G)) ∈ edges2 (surf G))
      (face G univ v) (face G univ (G.inv c v)) := by
  obtain ⟨π, hπ⟩ := exists_perm_two c
  have hb : G.inv c v ∈ G.bubble (univ \ {π 0, π 1}) v := by
    rw [compl_pair, bubble_singleton, hπ]; simp
  have e1 : face G {π 0, π 1} v = face G {π 0, π 1} (G.inv c v) := (face_eq_face_iff G).2 ⟨rfl, hb⟩
  have hv : face G {π 0, π 1} v ∈ flag G v π := (mem_flag G).2 (Or.inr (Or.inl rfl))
  have hw : face G {π 0, π 1} (G.inv c v) ∈ flag G (G.inv c v) π :=
    (mem_flag G).2 (Or.inr (Or.inl rfl))
  have hne1 : face G univ v ≠ face G {π 0, π 1} v := fun h => by
    have := face_card_eq G h; simp at this
  have hne2 : face G {π 0, π 1} (G.inv c v) ≠ face G univ (G.inv c v) := fun h => by
    have := face_card_eq G h; simp at this
  have a1 : ({face G univ v, face G {π 0, π 1} v} : Finset (DualSimplex G)) ∈ edges2 (surf G) :=
    edge_of_flag G ((mem_flag G).2 (Or.inr (Or.inr rfl))) hv hne1
  have a2 : ({face G {π 0, π 1} (G.inv c v), face G univ (G.inv c v)} : Finset (DualSimplex G)) ∈
      edges2 (surf G) :=
    edge_of_flag G hw ((mem_flag G).2 (Or.inr (Or.inr rfl))) hne2
  exact Relation.ReflTransGen.head a1 (Relation.ReflTransGen.single (by rw [e1]; exact a2))

/-- **The 1-skeleton of the subdivision of the dual of a connected colored graph is connected.** -/
lemma isConnected2_surf (h : G.IsConnected) : IsConnected2 (surf G) := by
  have hsymm : Std.Symm (fun a b : DualSimplex G => ({a, b} : Finset (DualSimplex G)) ∈ edges2 (surf G)) :=
    ⟨fun a b hab => (edge_symm G).1 hab⟩
  have htops : ∀ v w : V, Relation.ReflTransGen
      (fun a b => ({a, b} : Finset (DualSimplex G)) ∈ edges2 (surf G)) (face G univ v) (face G univ w) := by
    intro v w
    have := strongChain_of_connected G h v w
    induction this with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hadj ih =>
      obtain ⟨c, -, rfl⟩ := hadj
      exact ih.trans (conn_line G _ c)
  intro u hu w hw
  obtain ⟨v, π, hu⟩ := (mem_verts2_surf G).1 hu
  obtain ⟨v', π', hw⟩ := (mem_verts2_surf G).1 hw
  refine (conn_top G hu).trans ((htops v v').trans ?_)
  exact (symm_of (Relation.ReflTransGen _) (conn_top G hw))

/-! ### The links of the vertices are connected -/

/-- Two flags through `x` share an edge through `x`. -/
def Share (x : DualSimplex G) (p q : V × Perm (Fin 3)) : Prop :=
  ∃ y, y ≠ x ∧ x ∈ flag G p.1 p.2 ∧ y ∈ flag G p.1 p.2 ∧ x ∈ flag G q.1 q.2 ∧ y ∈ flag G q.1 q.2

lemma mem_lk2_of_flag {x u w : DualSimplex G} {p : V × Perm (Fin 3)} (hx : x ∈ flag G p.1 p.2)
    (hu : u ∈ flag G p.1 p.2) (hw : w ∈ flag G p.1 p.2) (hux : u ≠ x) (hwx : w ≠ x) (huw : u ≠ w) :
    ({u, w} : Finset (DualSimplex G)) ∈ lk2 (surf G) x := by
  rw [mem_lk2]
  have hsub : ({x, u, w} : Finset (DualSimplex G)) ⊆ flag G p.1 p.2 := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have hcard : ({x, u, w} : Finset (DualSimplex G)).card = 3 := by
    rw [card_insert_of_notMem (by simp [Ne.symm hux, Ne.symm hwx]), card_pair huw]
  have heq : ({x, u, w} : Finset (DualSimplex G)) = flag G p.1 p.2 :=
    eq_of_subset_of_card_le hsub (by rw [card_flag, hcard])
  refine ⟨by simp [Ne.symm hux, Ne.symm hwx], ?_⟩
  rw [show insert x ({u, w} : Finset (DualSimplex G)) = {x, u, w} from rfl, heq]
  exact (mem_surf G).2 ⟨p.1, p.2, rfl⟩

/-- Link vertices in one flag through `x` are joined in the link of `x`. -/
lemma link_conn_flag {x u w : DualSimplex G} {p : V × Perm (Fin 3)} (hx : x ∈ flag G p.1 p.2)
    (hu : u ∈ flag G p.1 p.2) (hw : w ∈ flag G p.1 p.2) (hux : u ≠ x) (hwx : w ≠ x) :
    Relation.ReflTransGen (fun a b => ({a, b} : Finset (DualSimplex G)) ∈ lk2 (surf G) x) u w := by
  by_cases huw : u = w
  · rw [huw]
  · exact Relation.ReflTransGen.single (mem_lk2_of_flag G hx hu hw hux hwx huw)

/-- **If the flags through `x` are linked by shared edges through `x`, the link of `x` is connected.** -/
lemma isConnEdges_lk2 {x : DualSimplex G}
    (h : ∀ p q : V × Perm (Fin 3), x ∈ flag G p.1 p.2 → x ∈ flag G q.1 q.2 →
      Relation.ReflTransGen (Share G x) p q) : IsConnEdges (lk2 (surf G) x) := by
  have hv : ∀ u ∈ verts2 (lk2 (surf G) x), ∃ p : V × Perm (Fin 3), x ∈ flag G p.1 p.2 ∧
      u ∈ flag G p.1 p.2 ∧ u ≠ x := by
    intro u hu
    obtain ⟨e, he, hue⟩ := mem_verts2.1 hu
    obtain ⟨hxe, he'⟩ := mem_lk2.1 he
    obtain ⟨v, π, hπ⟩ := (mem_surf G).1 he'
    refine ⟨(v, π), ?_, ?_, ?_⟩
    · rw [hπ]; exact mem_insert_self _ _
    · show u ∈ flag G v π
      rw [hπ]; exact mem_insert_of_mem hue
    · rintro rfl; exact hxe hue
  intro u hu w hw
  obtain ⟨p, hxp, hup, hux⟩ := hv u hu
  obtain ⟨q, hxq, hwq, hwx⟩ := hv w hw
  have hch := h p q hxp hxq
  have key : ∀ q', Relation.ReflTransGen (Share G x) p q' → x ∈ flag G q'.1 q'.2 →
      ∀ w' ∈ flag G q'.1 q'.2, w' ≠ x →
      Relation.ReflTransGen (fun a b => ({a, b} : Finset (DualSimplex G)) ∈ lk2 (surf G) x) u w' := by
    intro q' hq'
    induction hq' with
    | refl => intro hx w' hw' hw'x; exact link_conn_flag G hxp hup hw' hux hw'x
    | tail _ hs ih =>
      rename_i b c
      obtain ⟨y, hyx, hxb, hyb, hxc, hyc⟩ := hs
      intro hx w' hw' hw'x
      exact (ih hxb y hyb hyx).trans (link_conn_flag G hxc hyc hw' hyx hw'x)
  exact key q hch hxq w hwq hwx

/-! #### Moves between flags through a vertex -/

lemma ne_12 (v : V) (π : Perm (Fin 3)) : face G {π 0} v ≠ face G {π 0, π 1} v := fun h => by
  have := face_card_eq G h; have := card_pair_colors π; simp at *

lemma ne_13 (v : V) (π : Perm (Fin 3)) : face G {π 0} v ≠ face G univ v := fun h => by
  have := face_card_eq G h; simp at this

lemma ne_23 (v : V) (π : Perm (Fin 3)) : face G {π 0, π 1} v ≠ face G univ v := fun h => by
  have := face_card_eq G h; have := card_pair_colors π; simp at *

lemma r1_mem (v : V) (π : Perm (Fin 3)) : face G {π 0} v ∈ flag G v π := (mem_flag G).2 (Or.inl rfl)
lemma r2_mem (v : V) (π : Perm (Fin 3)) : face G {π 0, π 1} v ∈ flag G v π :=
  (mem_flag G).2 (Or.inr (Or.inl rfl))
lemma r3_mem (v : V) (π : Perm (Fin 3)) : face G univ v ∈ flag G v π :=
  (mem_flag G).2 (Or.inr (Or.inr rfl))

lemma inv_mem_bubble_2 (v : V) (π : Perm (Fin 3)) :
    G.inv (π 2) v ∈ G.bubble (univ \ {π 0, π 1}) v := by
  rw [compl_pair, bubble_singleton]; simp

lemma inv_mem_bubble_1 (v : V) (π : Perm (Fin 3)) :
    G.inv (π 2) v ∈ G.bubble (univ \ {π 0}) v := by
  refine bubble_mono G ?_ v (inv_mem_bubble_2 G v π)
  intro x hx
  simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton] at hx ⊢
  exact fun h => hx (Or.inl h)

/-- The move `π ↦ π ∘ (0 1)` keeps `ρ₂` and `ρ₃`. -/
lemma share_01 {x : DualSimplex G} {v : V} {π : Perm (Fin 3)}
    (hx : x = face G {π 0, π 1} v ∨ x = face G univ v) : Share G x (v, π) (v, π * swap 0 1) := by
  rcases hx with rfl | rfl
  · exact ⟨face G univ v, (ne_23 G v π).symm, r2_mem G v π, r3_mem G v π, (flag_swap01 G v π).1,
      (flag_swap01 G v π).2⟩
  · exact ⟨face G {π 0, π 1} v, (ne_23 G v π), r3_mem G v π, r2_mem G v π, (flag_swap01 G v π).2,
      (flag_swap01 G v π).1⟩

/-- The move `π ↦ π ∘ (1 2)` keeps `ρ₁` and `ρ₃`. -/
lemma share_12 {x : DualSimplex G} {v : V} {π : Perm (Fin 3)}
    (hx : x = face G {π 0} v ∨ x = face G univ v) : Share G x (v, π) (v, π * swap 1 2) := by
  rcases hx with rfl | rfl
  · exact ⟨face G univ v, (ne_13 G v π).symm, r1_mem G v π, r3_mem G v π, (flag_swap12 G v π).1,
      (flag_swap12 G v π).2⟩
  · exact ⟨face G {π 0} v, (ne_13 G v π), r3_mem G v π, r1_mem G v π, (flag_swap12 G v π).2,
      (flag_swap12 G v π).1⟩

/-- The move `v ↦ the other end of the line of the third color` keeps `ρ₁` and `ρ₂`. -/
lemma share_2 {x : DualSimplex G} {v : V} {π : Perm (Fin 3)}
    (hx : x = face G {π 0} v ∨ x = face G {π 0, π 1} v) : Share G x (v, π) (G.inv (π 2) v, π) := by
  have e1 : face G {π 0} v = face G {π 0} (G.inv (π 2) v) :=
    (face_eq_face_iff G).2 ⟨rfl, inv_mem_bubble_1 G v π⟩
  have e2 : face G {π 0, π 1} v = face G {π 0, π 1} (G.inv (π 2) v) :=
    (face_eq_face_iff G).2 ⟨rfl, inv_mem_bubble_2 G v π⟩
  rcases hx with rfl | rfl
  · exact ⟨face G {π 0, π 1} v, (ne_12 G v π).symm, r1_mem G v π, r2_mem G v π,
      e1 ▸ r1_mem G (G.inv (π 2) v) π, e2 ▸ r2_mem G (G.inv (π 2) v) π⟩
  · exact ⟨face G {π 0} v, (ne_12 G v π), r2_mem G v π, r1_mem G v π,
      e2 ▸ r2_mem G (G.inv (π 2) v) π, e1 ▸ r1_mem G (G.inv (π 2) v) π⟩

/-! #### Reaching all flags through a vertex -/

lemma share_symm {x : DualSimplex G} {p q : V × Perm (Fin 3)} (h : Share G x p q) : Share G x q p := by
  obtain ⟨y, hy, a, b, c, d⟩ := h
  exact ⟨y, hy, c, d, a, b⟩

lemma rtg_share_symm {x : DualSimplex G} {p q : V × Perm (Fin 3)}
    (h : Relation.ReflTransGen (Share G x) p q) : Relation.ReflTransGen (Share G x) q p :=
  haveI : Std.Symm (Share G x) := ⟨fun _ _ h => share_symm G h⟩
  symm_of (Relation.ReflTransGen (Share G x)) h

/-- Any two flags reachable from one base flag are joined. -/
lemma rtg_of_base {x : DualSimplex G} {b p q : V × Perm (Fin 3)}
    (hp : Relation.ReflTransGen (Share G x) b p) (hq : Relation.ReflTransGen (Share G x) b q) :
    Relation.ReflTransGen (Share G x) p q :=
  (rtg_share_symm G hp).trans hq

lemma perm_reach_one : ∀ σ : Perm (Fin 3),
    Relation.ReflTransGen (fun a b : Perm (Fin 3) => b = a * swap 0 1 ∨ b = a * swap 1 2) 1 σ := by
  have h6 : ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 1 2 ∨ σ = swap 0 1 * swap 1 2 ∨
      σ = swap 1 2 * swap 0 1 ∨ σ = swap 0 1 * swap 1 2 * swap 0 1 := by decide
  intro σ
  have hs : Relation.ReflTransGen (fun a b : Perm (Fin 3) => b = a * swap 0 1 ∨ b = a * swap 1 2) 1
      (swap 0 1) := Relation.ReflTransGen.single (Or.inl (by simp))
  have ht : Relation.ReflTransGen (fun a b : Perm (Fin 3) => b = a * swap 0 1 ∨ b = a * swap 1 2) 1
      (swap 1 2) := Relation.ReflTransGen.single (Or.inr (by simp))
  rcases h6 σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact hs
  · exact ht
  · exact hs.tail (Or.inr rfl)
  · exact ht.tail (Or.inl rfl)
  · exact (hs.tail (Or.inr rfl)).tail (Or.inl rfl)

lemma exists_perm_zero_two : ∀ a c : Fin 3, a ≠ c → ∃ ρ : Perm (Fin 3), ρ 0 = a ∧ ρ 2 = c := by decide

/-- **The link of the top simplex of a vertex is connected.** -/
lemma isConnEdges_top (w : V) : IsConnEdges (lk2 (surf G) (face G univ w)) := by
  refine isConnEdges_lk2 G ?_
  rintro ⟨a, σ⟩ ⟨b, τ⟩ hp hq
  simp only at hp hq
  have ha := mem_flag_rank3 G hp
  have hb := mem_flag_rank3 G hq
  subst ha; subst hb
  have lift : ∀ ρ, Relation.ReflTransGen
      (fun a b : Perm (Fin 3) => b = a * swap 0 1 ∨ b = a * swap 1 2) 1 ρ →
      Relation.ReflTransGen (Share G (face G univ w)) (w, 1) (w, ρ) := by
    intro ρ h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hs ih =>
      rename_i c d
      rcases hs with rfl | rfl
      · exact ih.tail (share_01 G (Or.inr rfl))
      · exact ih.tail (share_12 G (Or.inr rfl))
  exact rtg_of_base G (lift σ (perm_reach_one σ)) (lift τ (perm_reach_one τ))

/-- **The link of a simplex of rank two is connected.** -/
lemma isConnEdges_two (v : V) (π : Perm (Fin 3)) :
    IsConnEdges (lk2 (surf G) (face G {π 0, π 1} v)) := by
  refine isConnEdges_lk2 G ?_
  have reach : ∀ a σ, face G {π 0, π 1} v ∈ flag G a σ →
      Relation.ReflTransGen (Share G (face G {π 0, π 1} v)) (v, π) (a, σ) := by
    intro a σ h
    obtain ⟨e, hb⟩ := mem_flag_rank2 G (card_pair_colors π) h
    rw [compl_pair, bubble_singleton] at hb
    simp only [mem_insert, mem_singleton] at hb
    have hx2 : face G {π 0, π 1} v = face G {π 0, π 1} (G.inv (π 2) v) :=
      (face_eq_face_iff G).2 ⟨rfl, inv_mem_bubble_2 G v π⟩
    rcases perm_pair_swap01 π σ e with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (share_2 G (Or.inr rfl))
    · exact Relation.ReflTransGen.single (share_01 G (Or.inl rfl))
    · exact (Relation.ReflTransGen.single (share_2 G (Or.inr rfl))).tail
        (share_01 G (Or.inl hx2))
  rintro ⟨a, σ⟩ ⟨b, τ⟩ hp hq
  exact rtg_of_base G (reach a σ hp) (reach b τ hq)

/-- **The link of a simplex of rank one is connected.** -/
lemma isConnEdges_one (v : V) (a : Fin 3) : IsConnEdges (lk2 (surf G) (face G {a} v)) := by
  refine isConnEdges_lk2 G ?_
  obtain ⟨π0, hπ0⟩ : ∃ π : Perm (Fin 3), π 0 = a := ⟨swap 0 a, by simp⟩
  have xe : ∀ u, u ∈ G.bubble (univ \ {a}) v → ∀ σ : Perm (Fin 3), σ 0 = a →
      face G {a} v = face G {σ 0} u := fun u hu σ hσ => by
    rw [hσ]; exact (face_eq_face_iff G).2 ⟨rfl, hu⟩
  have reach : ∀ u, Relation.ReflTransGen (G.Adj (univ \ {a})) v u → ∀ σ : Perm (Fin 3), σ 0 = a →
      Relation.ReflTransGen (Share G (face G {a} v)) (v, π0) (u, σ) := by
    intro u hu
    induction hu with
    | refl =>
      intro σ hσ
      have hvb : v ∈ G.bubble (univ \ {a}) v := mem_bubble_self G _ v
      rcases perm_single_swap12 π0 σ (by rw [hπ0, hσ]) with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (share_12 G (Or.inl (xe v hvb π0 hπ0)))
    | tail hab hadj ih =>
      rename_i b c
      obtain ⟨d, hd, rfl⟩ := hadj
      have hd' : d ≠ a := by simpa using hd
      have hb : b ∈ G.bubble (univ \ {a}) v := (mem_bubble_iff G _ v b).2 hab
      have hc : G.inv d b ∈ G.bubble (univ \ {a}) v := inv_mem_bubble_of_mem G (by simpa using hd) hb
      obtain ⟨ρ, hρ0, hρ2⟩ := exists_perm_zero_two a d (Ne.symm hd')
      intro σ hσ
      have h1 : Relation.ReflTransGen (Share G (face G {a} v)) (v, π0) (G.inv d b, ρ) := by
        have := (ih ρ hρ0).tail (share_2 G (Or.inl (xe b hb ρ hρ0)))
        rwa [hρ2] at this
      rcases perm_single_swap12 ρ σ (by rw [hρ0, hσ]) with rfl | rfl
      · exact h1
      · exact h1.tail (share_12 G (Or.inl (xe _ hc ρ hρ0)))
  rintro ⟨u, σ⟩ ⟨u', σ'⟩ hp hq
  obtain ⟨e, hu⟩ := mem_flag_rank1 G (by simp) hp
  obtain ⟨e', hu'⟩ := mem_flag_rank1 G (by simp) hq
  have h0 : σ 0 = a := by simpa using e.symm
  have h0' : σ' 0 = a := by simpa using e'.symm
  exact rtg_of_base G (reach u ((mem_bubble_iff G _ v u).1 hu) σ h0)
    (reach u' ((mem_bubble_iff G _ v u').1 hu') σ' h0')

/-- **The link of every vertex of the subdivision is connected.** -/
lemma isLinkConn_surf : IsLinkConn (surf G) := by
  intro x hx
  obtain ⟨u, τ, hxf⟩ := (mem_verts2_surf G).1 hx
  rcases (mem_flag G).1 hxf with rfl | rfl | rfl
  · exact isConnEdges_one G u (τ 0)
  · exact isConnEdges_two G u τ
  · exact isConnEdges_top G u

/-- **The subdivision of the dual of a connected colored graph in dimension `2` is a closed surface.** -/
theorem isSurface_surf [Nonempty V] (h : G.IsConnected) : Lightlike.Surfaces.IsSurface (surf G) where
  nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨flag G v 1, (mem_surf G).2 ⟨v, 1, rfl⟩⟩
  card := isTri2_surf G
  closed := isClosed2_surf G
  link := isLinkConn_surf G
  connected := isConnected2_surf G h

/-! ### The Euler characteristic -/

/-- Three times the number of triangles is twice the number of edges. -/
lemma two_mul_card_edges2 : 2 * (edges2 (surf G)).card = 3 * (surf G).card := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := edges2 (surf G)) (t := surf G) (fun f τ => f ⊆ τ)
  have h1 : ∀ f ∈ edges2 (surf G), ((surf G).bipartiteAbove (fun f τ => f ⊆ τ) f).card = 2 := fun f hf => by
    exact isClosed2_surf G f hf
  have h2 : ∀ τ ∈ surf G, ((edges2 (surf G)).bipartiteBelow (fun f τ => f ⊆ τ) τ).card = 3 := fun τ hτ => by
    have : (edges2 (surf G)).bipartiteBelow (fun f τ => f ⊆ τ) τ = powersetCard 2 τ := by
      ext f
      simp only [Finset.bipartiteBelow, mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨hf, hfτ⟩
        obtain ⟨-, -, -, hc⟩ := mem_edges2.1 hf
        exact ⟨hfτ, hc⟩
      · rintro ⟨hf, hc⟩
        exact ⟨mem_edges2.2 ⟨τ, hτ, hf, hc⟩, hf⟩
    rw [this, card_powersetCard, isTri2_surf G τ hτ]; rfl
  rw [sum_congr rfl h1, sum_congr rfl h2] at h
  simpa [mul_comm] using h

lemma exists_perm_card1 : ∀ S : Finset (Fin 3), S.card = 1 → ∃ π : Perm (Fin 3), S = {π 0} := by decide
lemma exists_perm_card2 : ∀ S : Finset (Fin 3), S.card = 2 → ∃ π : Perm (Fin 3), S = {π 0, π 1} := by
  decide

/-- **The vertices of the subdivision are the simplices of `Δ_G` with at least one color.** -/
lemma verts2_surf : verts2 (surf G) = univ.filter (fun σ : DualSimplex G => σ.colors.Nonempty) := by
  ext σ
  rw [mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · intro hσ
    obtain ⟨v, π, hx⟩ := (mem_verts2_surf G).1 hσ
    rcases (mem_flag G).1 hx with rfl | rfl | rfl
    · exact ⟨π 0, by simp⟩
    · exact ⟨π 0, by simp⟩
    · exact ⟨0, by simp⟩
  · intro hne
    obtain ⟨v, hv⟩ := σ.exists_mem_bub
    have hσ : σ = face G σ.colors v := DualSimplex.ext' rfl (DualSimplex.bub_eq_of_mem' σ hv)
    rw [mem_verts2_surf]
    have hle : σ.colors.card ≤ 3 := by simpa using card_le_univ σ.colors
    have hpos : 0 < σ.colors.card := card_pos.2 hne
    have : σ.colors.card = 1 ∨ σ.colors.card = 2 ∨ σ.colors.card = 3 := by omega
    rcases this with h | h | h
    · obtain ⟨π, hπ⟩ := exists_perm_card1 _ h
      exact ⟨v, π, (mem_flag G).2 (Or.inl (by rw [hσ, hπ]))⟩
    · obtain ⟨π, hπ⟩ := exists_perm_card2 _ h
      exact ⟨v, π, (mem_flag G).2 (Or.inr (Or.inl (by rw [hσ, hπ])))⟩
    · have : σ.colors = univ := eq_univ_of_card _ (by simpa using h)
      exact ⟨v, 1, (mem_flag G).2 (Or.inr (Or.inr (by rw [hσ, this])))⟩

lemma card_surf : (surf G).card = 6 * Fintype.card V := by
  unfold surf
  rw [card_image_of_injective _ (flag_injective G), card_univ, Fintype.card_prod, Fintype.card_perm,
    Fintype.card_fin, show Nat.factorial 3 = 6 from rfl, mul_comm]

lemma f_eq_card (p : ℕ) :
    (dual G).f p = (univ.filter fun σ : DualSimplex G => σ.colors.card = p + 1).card := by
  unfold GradedPoset.f
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- Twice the number of rank-two simplices of the dual is three times the number of vertices. -/
lemma two_mul_f1 : 2 * (dual G).f 1 = 3 * Fintype.card V := by
  have h1 : (dual G).f 1 = G.nBubbles {2} + G.nBubbles {1} + G.nBubbles {0} := by
    rw [dual_f]
    have : powersetCard (1 + 1) (univ : Finset (Fin (2 + 1))) = {{0, 1}, {0, 2}, {1, 2}} := by decide
    rw [this, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have e0 : (univ : Finset (Fin 3)) \ {0, 1} = {2} := by decide
    have e1 : (univ : Finset (Fin 3)) \ {0, 2} = {1} := by decide
    have e2 : (univ : Finset (Fin 3)) \ {1, 2} = {0} := by decide
    rw [e0, e1, e2]
    omega
  have t0 := G.two_mul_nBubbles_singleton 0
  have t1 := G.two_mul_nBubbles_singleton 1
  have t2 := G.two_mul_nBubbles_singleton 2
  omega

lemma card_verts2_surf : (verts2 (surf G)).card = (dual G).f 0 + (dual G).f 1 + (dual G).f 2 := by
  rw [verts2_surf, f_eq_card, f_eq_card, f_eq_card]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : DualSimplex G => σ.colors.card) (t := {1, 2, 3})]
  · rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    have e : ∀ b ∈ ({1, 2, 3} : Finset ℕ), (univ.filter fun σ : DualSimplex G => σ.colors.Nonempty).filter
        (fun σ => σ.colors.card = b) = univ.filter fun σ : DualSimplex G => σ.colors.card = b := by
      intro b hb
      ext σ
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hb ⊢
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨card_pos.1 (by omega), h⟩
    rw [e 1 (by simp), e 2 (by simp), e 3 (by simp)]
    simp only [zero_add, Nat.reduceAdd]
    omega
  · intro σ hσ
    have hσ' : σ.colors.Nonempty := by simpa using hσ
    have hle : σ.colors.card ≤ 3 := by simpa using card_le_univ σ.colors
    have hpos : 0 < σ.colors.card := card_pos.2 hσ'
    simp only [Finset.mem_coe, mem_insert, mem_singleton]
    omega

/-- **The subdivision has the Euler characteristic of the dual.** -/
theorem euler2_surf : euler2 (surf G) = (dual G).eulerChar 3 := by
  have h1 := card_verts2_surf G
  have h2 := two_mul_card_edges2 G
  have h3 := card_surf G
  have h4 := two_mul_f1 G
  have h5 : (dual G).f 2 = Fintype.card V := dual_f_top G
  unfold euler2 GradedPoset.eulerChar
  simp only [sum_range_succ, sum_range_zero]
  push_cast
  omega

/-- **The Euler characteristic of the dual of a connected colored graph in dimension `2` is at most `2`**
(the genus side of Gurau 2010, Section 2): the subdivision of `Δ_G` is a closed surface, whose Euler
characteristic is at most `2` (`Lightlike.Surfaces.IsSurface.euler_le`), and equals that of `Δ_G`. -/
theorem euler_le_two [Nonempty V] (h : G.IsConnected) : G.euler ≤ 2 := by
  rw [← eulerChar_dual_eq_euler, ← euler2_surf]
  exact (isSurface_surf G h).euler_le

end ColoredGraph

/-- **Trust check**: the theta graph (the sphere) is a closed surface of Euler characteristic `2`, and the
torus graph one of Euler characteristic `0`, so the bound is attained and the characteristic is read off. -/
example : Lightlike.Surfaces.IsSurface (ColoredGraph.surf theta) ∧
    euler2 (ColoredGraph.surf theta) = 2 ∧ euler2 (ColoredGraph.surf torus) = 0 := by
  have ht : theta.IsConnected := by unfold ColoredGraph.IsConnected; decide +kernel
  have hto : torus.IsConnected := by unfold ColoredGraph.IsConnected; decide +kernel
  have e : theta.euler = 2 ∧ torus.euler = 0 ∧ theta.euler ≠ torus.euler := by decide +kernel
  refine ⟨ColoredGraph.isSurface_surf theta ht, ?_, ?_⟩
  · rw [ColoredGraph.euler2_surf, ColoredGraph.eulerChar_dual_eq_euler]; exact e.1
  · rw [ColoredGraph.euler2_surf, ColoredGraph.eulerChar_dual_eq_euler]; exact e.2.1

end Lightlike.GFT
