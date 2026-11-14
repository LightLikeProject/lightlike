module

public import Lightlike.PonzanoRegge.Manifold

/-!
# Invariants of combinatorial 2-spheres

`IsSphere2` defines combinatorial 2-spheres by 2-dimensional bistellar moves from the boundary of
a tetrahedron. This file proves that every such complex has the properties of a triangulated
2-sphere that can be read off combinatorially:

* `IsSphere2.euler`: its Euler characteristic `#vertices - #edges + #triangles` is `2`;
* `IsSphere2.connected`: its 1-skeleton is connected;
* `IsSphere2.closed`: every edge lies in exactly two triangles.

Each property holds for the boundary of a tetrahedron and is preserved by both moves in both
directions: subdividing a triangle adds one vertex, three edges and two triangles; flipping an
edge replaces one edge by another.

These are the conditions that, by the classification of surfaces, characterise the 2-sphere among
closed connected surfaces; the remaining surface condition (the link of each vertex is a single
cycle) and the converse (every triangulated 2-sphere is reached by bistellar moves, a theorem of
Steinitz and Wagner) are not formalised. The invariants give strong rejection tests: a complex
with Euler characteristic other than `2` (two spheres glued at a vertex, a torus, a disk) is not a
combinatorial 2-sphere.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- The edges of a 2-complex: the 2-element subsets of its triangles. -/
def edges2 (L : Finset (Finset V)) : Finset (Finset V) := L.biUnion (powersetCard 2)

lemma mem_edges2 {L : Finset (Finset V)} {e : Finset V} :
    e ∈ edges2 L ↔ ∃ τ ∈ L, e ⊆ τ ∧ #e = 2 := by
  simp [edges2, mem_powersetCard]

/-- A 2-element subset of `{p, q, r}` is one of its three edges. -/
lemma pair_of_sub3 {e : Finset V} {p q r : V} (he : e ⊆ {p, q, r}) (hc : #e = 2) :
    e = {p, q} ∨ e = {p, r} ∨ e = {q, r} := by
  obtain ⟨u, w, huw, rfl⟩ := card_eq_two.mp hc
  have hu : u ∈ ({p, q, r} : Finset V) := he (by simp)
  have hw : w ∈ ({p, q, r} : Finset V) := he (by simp)
  simp only [mem_insert, mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first
    | exact absurd rfl huw
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; rfl)
    | (left; exact pair_comm _ _)
    | (right; left; exact pair_comm _ _)
    | (right; right; exact pair_comm _ _)

lemma mem_verts2_of_sub {L : Finset (Finset V)} {e τ : Finset V} {y : V} (hτ : τ ∈ L) (he : e ⊆ τ)
    (hy : y ∈ e) : y ∈ verts2 L :=
  mem_verts2.mpr ⟨τ, hτ, he hy⟩

/-! ## Subdividing a triangle -/

section sub13

variable {L : Finset (Finset V)} {b c d x : V}

lemma sub13_fresh (hτ : {b, c, d} ∈ L) (hx : x ∉ verts2 L) : x ≠ b ∧ x ≠ c ∧ x ≠ d :=
  ⟨fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩),
    fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩),
    fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩)⟩

/-- Subdividing a triangle adds the new vertex. -/
lemma verts2_sub13 (hτ : {b, c, d} ∈ L) :
    verts2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) =
      insert x (verts2 L) := by
  ext y
  simp only [mem_verts2, mem_insert, mem_erase]
  constructor
  · rintro ⟨τ, hτ', hy⟩
    rcases hτ' with rfl | rfl | rfl | ⟨-, hτL⟩
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inl rfl
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inl rfl
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inr ⟨_, hτ, by simp⟩
      · exact Or.inl rfl
    · exact Or.inr ⟨τ, hτL, hy⟩
  · rintro (rfl | ⟨τ, hτL, hy⟩)
    · exact ⟨{b, c, y}, Or.inl rfl, by simp⟩
    · by_cases h : τ = {b, c, d}
      · subst h
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact ⟨{y, c, x}, Or.inl rfl, by simp⟩
        · exact ⟨{b, y, x}, Or.inl rfl, by simp⟩
        · exact ⟨{c, y, x}, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨τ, Or.inr (Or.inr (Or.inr ⟨h, hτL⟩)), hy⟩

/-- Subdividing a triangle adds the three edges through the new vertex. -/
lemma edges2_sub13 (hτ : {b, c, d} ∈ L) (hx : x ∉ verts2 L) :
    edges2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) =
      insert {b, x} (insert {c, x} (insert {d, x} (edges2 L))) := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have old : ∀ e : Finset V, e ⊆ {b, c, d} → #e = 2 → e ∈ edges2 L := fun e he hc =>
    mem_edges2.mpr ⟨_, hτ, he, hc⟩
  ext e
  simp only [mem_insert, mem_edges2 (L := insert _ _), mem_erase]
  constructor
  · rintro ⟨τ, hτ', hsub, hc⟩
    rcases hτ' with rfl | rfl | rfl | ⟨-, hτL⟩
    · rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (old _ (by small_subset) hc)))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (old _ (by small_subset) hc)))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (old _ (by small_subset) hc)))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (mem_edges2.mpr ⟨τ, hτL, hsub, hc⟩)))
  · rintro (rfl | rfl | rfl | he)
    · exact ⟨{b, c, x}, Or.inl rfl, by small_subset, card_pair hxb.symm⟩
    · exact ⟨{b, c, x}, Or.inl rfl, by small_subset, card_pair hxc.symm⟩
    · exact ⟨{c, d, x}, Or.inr (Or.inl rfl), by small_subset, card_pair hxd.symm⟩
    · obtain ⟨τ, hτL, hsub, hc⟩ := mem_edges2.mp he
      by_cases h : τ = {b, c, d}
      · subst h
        rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
        · exact ⟨{b, c, x}, Or.inl rfl, by small_subset, hc⟩
        · exact ⟨{b, d, x}, Or.inr (Or.inr (Or.inl rfl)), by small_subset, hc⟩
        · exact ⟨{c, d, x}, Or.inr (Or.inl rfl), by small_subset, hc⟩
      · exact ⟨τ, Or.inr (Or.inr (Or.inr ⟨h, hτL⟩)), hsub, hc⟩

lemma card_edges2_sub13 (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hτ : {b, c, d} ∈ L)
    (hx : x ∉ verts2 L) :
    #(edges2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d}))))) =
      #(edges2 L) + 3 := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have hnew : ∀ y : V, ({y, x} : Finset V) ∉ edges2 L := fun y hm => by
    obtain ⟨τ, hτL, hsub, -⟩ := mem_edges2.mp hm
    exact hx (mem_verts2_of_sub hτL hsub (by simp))
  rw [edges2_sub13 hτ hx, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem (hnew d)]
  · simp only [mem_insert, not_or]
    exact ⟨fun h => hcd (by rw [pair_eq_pair_iff'] at h; tauto), hnew c⟩
  · simp only [mem_insert, not_or]
    exact ⟨fun h => hbc (by rw [pair_eq_pair_iff'] at h; tauto),
      fun h => hbd (by rw [pair_eq_pair_iff'] at h; tauto), hnew b⟩

lemma card_sub13 (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hτ : {b, c, d} ∈ L)
    (hx : x ∉ verts2 L) :
    #(insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) = #L + 2 := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have hnew : ∀ y z : V, ({y, z, x} : Finset V) ∉ L := fun y z hm =>
    hx (mem_verts2.mpr ⟨_, hm, by simp⟩)
  have n1 : ({b, d, x} : Finset V) ∉ L.erase {b, c, d} := fun h' => hnew _ _ (mem_of_mem_erase h')
  have n2 : ({c, d, x} : Finset V) ∉ insert {b, d, x} (L.erase {b, c, d}) := by
    rw [mem_insert, not_or]
    refine ⟨fun h' => ?_, fun h' => hnew _ _ (mem_of_mem_erase h')⟩
    have : c ∈ ({b, d, x} : Finset V) := h' ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h'' | h'' | h''
    · exact hbc h''.symm
    · exact hcd h''
    · exact hxc h''.symm
  have n3 : ({b, c, x} : Finset V) ∉ insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})) := by
    simp only [mem_insert, not_or]
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => hnew _ _ (mem_of_mem_erase h')⟩
    · have : b ∈ ({c, d, x} : Finset V) := h' ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h'' | h'' | h''
      · exact hbc h''
      · exact hbd h''
      · exact hxb h''.symm
    · have : d ∈ ({b, c, x} : Finset V) := h' ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h'' | h'' | h''
      · exact hbd h''.symm
      · exact hcd h''.symm
      · exact hxd h''.symm
  rw [card_insert_of_notMem n3, card_insert_of_notMem n2, card_insert_of_notMem n1,
    card_erase_of_mem hτ]
  have : 0 < #L := card_pos.mpr ⟨_, hτ⟩
  omega

end sub13

/-! ## Flipping an edge -/

section flip22

variable {L : Finset (Finset V)} {b c d e : V}

/-- Flipping an edge keeps the vertices. -/
lemma verts2_flip22 (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L) :
    verts2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) =
      verts2 L := by
  ext y
  simp only [mem_verts2, mem_insert, mem_erase]
  constructor
  · rintro ⟨τ, hτ', hy⟩
    rcases hτ' with rfl | rfl | ⟨-, -, hτL⟩
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨_, h₁, by simp⟩
      · exact ⟨_, h₁, by simp⟩
      · exact ⟨_, h₂, by simp⟩
    · simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨_, h₁, by simp⟩
      · exact ⟨_, h₁, by simp⟩
      · exact ⟨_, h₂, by simp⟩
    · exact ⟨τ, hτL, hy⟩
  · rintro ⟨τ, hτL, hy⟩
    by_cases h1 : τ = {b, c, d}
    · subst h1
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨{y, d, e}, Or.inl rfl, by simp⟩
      · exact ⟨{y, d, e}, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨{b, y, e}, Or.inl rfl, by simp⟩
    by_cases h2 : τ = {b, c, e}
    · subst h2
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨{y, d, e}, Or.inl rfl, by simp⟩
      · exact ⟨{y, d, e}, Or.inr (Or.inl rfl), by simp⟩
      · exact ⟨{b, d, y}, Or.inl rfl, by simp⟩
    · exact ⟨τ, Or.inr (Or.inr ⟨h2, h1, hτL⟩), hy⟩

/-- Flipping an edge replaces the edge `bc` by `de`. -/
lemma edges2_flip22 (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L)
    (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e}) :
    edges2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) =
      insert {d, e} ((edges2 L).erase {b, c}) := by
  have old : ∀ τ ∈ L, ∀ f : Finset V, f ⊆ τ → #f = 2 → f ∈ edges2 L := fun τ hτ f hf hc =>
    mem_edges2.mpr ⟨τ, hτ, hf, hc⟩
  have hne : ∀ f : Finset V, f ≠ {b, c} → f ∈ edges2 L → f ∈ (edges2 L).erase {b, c} :=
    fun f hf hm => mem_erase.mpr ⟨hf, hm⟩
  ext f
  simp only [mem_insert, mem_edges2 (L := insert _ _), mem_erase]
  constructor
  · rintro ⟨τ, hτ', hsub, hc⟩
    rcases hτ' with rfl | rfl | ⟨hne2, hne1, hτL⟩
    · rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
      · exact Or.inr ⟨fun h => hcd (by rw [pair_eq_pair_iff'] at h; tauto),
          old _ h₁ _ (by small_subset) hc⟩
      · exact Or.inr ⟨fun h => hce (by rw [pair_eq_pair_iff'] at h; tauto),
          old _ h₂ _ (by small_subset) hc⟩
      · exact Or.inl rfl
    · rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
      · exact Or.inr ⟨fun h => hbd (by rw [pair_eq_pair_iff'] at h; tauto),
          old _ h₁ _ (by small_subset) hc⟩
      · exact Or.inr ⟨fun h => hbe (by rw [pair_eq_pair_iff'] at h; tauto),
          old _ h₂ _ (by small_subset) hc⟩
      · exact Or.inl rfl
    · refine Or.inr ⟨fun h => ?_, old τ hτL f hsub hc⟩
      subst h
      rcases hstar τ hτL hsub with rfl | rfl
      · exact hne1 rfl
      · exact hne2 rfl
  · rintro (rfl | ⟨hf, hm⟩)
    · exact ⟨{b, d, e}, Or.inl rfl, by small_subset, card_pair hde⟩
    · obtain ⟨τ, hτL, hsub, hc⟩ := mem_edges2.mp hm
      by_cases h1 : τ = {b, c, d}
      · subst h1
        rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
        · exact absurd rfl hf
        · exact ⟨{b, d, e}, Or.inl rfl, by small_subset, hc⟩
        · exact ⟨{c, d, e}, Or.inr (Or.inl rfl), by small_subset, hc⟩
      by_cases h2 : τ = {b, c, e}
      · subst h2
        rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
        · exact absurd rfl hf
        · exact ⟨{b, d, e}, Or.inl rfl, by small_subset, hc⟩
        · exact ⟨{c, d, e}, Or.inr (Or.inl rfl), by small_subset, hc⟩
      · exact ⟨τ, Or.inr (Or.inr ⟨h2, h1, hτL⟩), hsub, hc⟩

lemma card_edges2_flip22 (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L)
    (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e})
    (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ) :
    #(edges2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e})))) =
      #(edges2 L) := by
  have hbcE : ({b, c} : Finset V) ∈ edges2 L := mem_edges2.mpr ⟨_, h₁, by small_subset, card_pair hbc⟩
  have hdeE : ({d, e} : Finset V) ∉ (edges2 L).erase {b, c} := fun hm => by
    obtain ⟨τ, hτL, hsub, -⟩ := mem_edges2.mp (mem_of_mem_erase hm)
    exact hfresh τ hτL hsub
  rw [edges2_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar, card_insert_of_notMem hdeE,
    card_erase_of_mem hbcE]
  have : 0 < #(edges2 L) := card_pos.mpr ⟨_, hbcE⟩
  omega

lemma card_flip22 (hde : d ≠ e) (hbd : b ≠ d) (hbe : b ≠ e) (hbc : b ≠ c) (hcd : c ≠ d)
    (h₁ : {b, c, d} ∈ L)
    (h₂ : {b, c, e} ∈ L) (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ) :
    #(insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) = #L := by
  have hne : ({b, c, d} : Finset V) ≠ {b, c, e} := fun h => hde (by
    have : d ∈ ({b, c, e} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h' | h'
    · exact absurd h'.symm hbd
    · exact absurd h'.symm hcd
    · exact h')
  have n1 : ({c, d, e} : Finset V) ∉ (L.erase {b, c, d}).erase {b, c, e} := fun h' =>
    hfresh _ (mem_of_mem_erase (mem_of_mem_erase h')) (by small_subset)
  have n2 : ({b, d, e} : Finset V) ∉ insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}) := by
    rw [mem_insert, not_or]
    refine ⟨fun h' => hbc ?_, fun h' =>
      hfresh _ (mem_of_mem_erase (mem_of_mem_erase h')) (by small_subset)⟩
    have : b ∈ ({c, d, e} : Finset V) := h' ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h'' | h'' | h''
    · exact h''
    · exact absurd h'' hbd
    · exact absurd h'' hbe
  rw [card_insert_of_notMem n2, card_insert_of_notMem n1,
    card_erase_of_mem (mem_erase.mpr ⟨hne.symm, h₂⟩), card_erase_of_mem h₁]
  have : 1 < #L := one_lt_card.mpr ⟨_, h₁, _, h₂, hne⟩
  omega

end flip22

/-! ## Euler characteristic -/

/-- The **Euler characteristic** `#vertices - #edges + #triangles` of a 2-complex. -/
def euler2 (L : Finset (Finset V)) : ℤ := #(verts2 L) - #(edges2 L) + #L

/-- A 2-dimensional move keeps the Euler characteristic. -/
theorem Move2.euler2_eq {L L' : Finset (Finset V)} (h : Move2 L L') : euler2 L = euler2 L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx =>
    unfold euler2
    rw [verts2_sub13 hτ, card_insert_of_notMem hx, card_edges2_sub13 hbc hbd hcd hτ hx,
      card_sub13 hbc hbd hcd hτ hx]
    push_cast
    ring
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    unfold euler2
    rw [verts2_flip22 h₁ h₂, card_edges2_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh,
      card_flip22 hde hbd hbe hbc hcd h₁ h₂ hfresh]

omit [DecidableEq V] in
/-- Two sets differ if one contains an element the other lacks. -/
lemma ne_of_mem_notMem {s t : Finset V} {y : V} (hy : y ∈ s) (hy' : y ∉ t) : s ≠ t :=
  fun h => hy' (h ▸ hy)

section bdry

-- These proofs pass all six distinctness facts to `simp`; each step uses only some of them.
set_option linter.unusedSimpArgs false

variable {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
  (hcd : c ≠ d)
include hab hac had hbc hbd hcd

lemma card_bdry : #(bdry a b c d) = 4 := by
  rw [bdry, card_insert_of_notMem, card_insert_of_notMem, card_pair]
  · exact ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm])
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨ne_of_mem_notMem (y := b) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]),
      ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm])⟩
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨ne_of_mem_notMem (y := c) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]),
      ne_of_mem_notMem (y := b) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]),
      ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm])⟩

lemma card_verts2_bdry : #(verts2 (bdry a b c d)) = 4 := by
  have : verts2 (bdry a b c d) = {a, b, c, d} := by
    ext y
    simp only [mem_verts2, bdry, mem_insert, mem_singleton]
    constructor
    · rintro ⟨τ, hτ, hy⟩
      rcases hτ with rfl | rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hy <;>
        tauto
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨{y, b, c}, Or.inl rfl, by simp⟩
      · exact ⟨{a, y, c}, Or.inl rfl, by simp⟩
      · exact ⟨{a, b, y}, Or.inl rfl, by simp⟩
      · exact ⟨{a, b, y}, Or.inr (Or.inl rfl), by simp⟩
  rw [this, card_four hab hac had hbc hbd hcd]

lemma card_edges2_bdry : #(edges2 (bdry a b c d)) = 6 := by
  have : edges2 (bdry a b c d) = {{a, b}, {a, c}, {a, d}, {b, c}, {b, d}, {c, d}} := by
    ext f
    simp only [mem_edges2, bdry, mem_insert, mem_singleton]
    constructor
    · rintro ⟨τ, hτ, hsub, hc⟩
      rcases hτ with rfl | rfl | rfl | rfl <;> rcases pair_of_sub3 hsub hc with rfl | rfl | rfl <;>
        simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨{a, b, c}, Or.inl rfl, by small_subset, card_pair hab⟩
      · exact ⟨{a, b, c}, Or.inl rfl, by small_subset, card_pair hac⟩
      · exact ⟨{a, b, d}, Or.inr (Or.inl rfl), by small_subset, card_pair had⟩
      · exact ⟨{a, b, c}, Or.inl rfl, by small_subset, card_pair hbc⟩
      · exact ⟨{a, b, d}, Or.inr (Or.inl rfl), by small_subset, card_pair hbd⟩
      · exact ⟨{a, c, d}, Or.inr (Or.inr (Or.inl rfl)), by small_subset, card_pair hcd⟩
  rw [this]
  repeat rw [card_insert_of_notMem (by simp [pair_eq_pair_iff', hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm])]
  rw [card_singleton]

/-- The boundary of a tetrahedron has Euler characteristic `4 - 6 + 4 = 2`. -/
theorem euler2_bdry : euler2 (bdry a b c d) = 2 := by
  unfold euler2
  rw [card_verts2_bdry hab hac had hbc hbd hcd, card_edges2_bdry hab hac had hbc hbd hcd,
    card_bdry hab hac had hbc hbd hcd]
  norm_num

end bdry

/-- **A combinatorial 2-sphere has Euler characteristic `2`.** -/
theorem IsSphere2.euler {L : Finset (Finset V)} (hL : IsSphere2 L) : euler2 L = 2 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩ := hL
  have key : ∀ L L' : Finset (Finset V), Relation.EqvGen Move2 L L' → euler2 L = euler2 L' := by
    intro L L' h
    induction h with
    | rel _ _ h => exact h.euler2_eq
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  rw [← key _ _ h, euler2_bdry hab hac had hbc hbd hcd]

/-- The vertices of the boundary of a tetrahedron are its four corners. -/
lemma mem_verts2_bdry {a b c d w : V} (hw : w ∈ verts2 (bdry a b c d)) :
    w = a ∨ w = b ∨ w = c ∨ w = d := by
  obtain ⟨τ, hτ, hwτ⟩ := mem_verts2.mp hw
  clear hw
  simp only [bdry, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hwτ <;>
    rcases hwτ with h | h | h <;> simp [h]

/-! ## Connectivity -/

/-- The 1-skeleton of `L` is **connected**: any two vertices are joined by a path of edges. -/
def IsConnected2 (L : Finset (Finset V)) : Prop :=
  ∀ u ∈ verts2 L, ∀ v ∈ verts2 L,
    Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 L) u v

lemma pair_mem_edges2 {L : Finset (Finset V)} {τ : Finset V} {u w : V} (hτ : τ ∈ L) (hu : u ∈ τ)
    (hw : w ∈ τ) (huw : u ≠ w) : ({u, w} : Finset V) ∈ edges2 L :=
  mem_edges2.mpr ⟨τ, hτ, fun y hy => by
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption, card_pair huw⟩

/-- Subdividing a triangle keeps the 1-skeleton connected, in both directions. -/
lemma connected_sub13 {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hτ : {b, c, d} ∈ L) (hx : x ∉ verts2 L) :
    IsConnected2 L ↔
      IsConnected2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  unfold IsConnected2
  rw [verts2_sub13 hτ, edges2_sub13 hτ hx]
  have hb : b ∈ verts2 L := mem_verts2.mpr ⟨_, hτ, by simp⟩
  have hbx : ({b, x} : Finset V) ∈ insert {b, x} (insert {c, x} (insert {d, x} (edges2 L))) :=
    mem_insert_self _ _
  have hxb' : ({x, b} : Finset V) ∈ insert {b, x} (insert {c, x} (insert {d, x} (edges2 L))) := by
    rw [pair_comm x b]; exact hbx
  have mono : ∀ {u v}, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 L) u v →
      Relation.ReflTransGen (fun y z => ({y, z} : Finset V) ∈
        insert {b, x} (insert {c, x} (insert {d, x} (edges2 L)))) u v :=
    fun h => Relation.ReflTransGen.mono
      (fun _ _ hm => mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem hm))) _ _ h
  constructor
  · intro H u hu v hv
    have toB : ∀ w ∈ insert x (verts2 L), Relation.ReflTransGen (fun y z => ({y, z} : Finset V) ∈
        insert {b, x} (insert {c, x} (insert {d, x} (edges2 L)))) w b := by
      intro w hw
      rcases mem_insert.mp hw with h | h
      · rw [h]; exact .single hxb'
      · exact mono (H w h b hb)
    have fromB : ∀ w ∈ insert x (verts2 L), Relation.ReflTransGen (fun y z => ({y, z} : Finset V) ∈
        insert {b, x} (insert {c, x} (insert {d, x} (edges2 L)))) b w := by
      intro w hw
      rcases mem_insert.mp hw with h | h
      · rw [h]; exact .single hbx
      · exact mono (H b hb w h)
    exact (toB u hu).trans (fromB v hv)
  · intro H u hu v hv
    have hux : u ≠ x := fun h => hx (h ▸ hu)
    have hvx : v ≠ x := fun h => hx (h ▸ hv)
    let f : V → V := fun y => if y = x then b else y
    have hf : ∀ y, y ≠ x → f y = y := fun y hy => by simp [f, hy]
    have step : ∀ p q, ({p, q} : Finset V) ∈ insert {b, x} (insert {c, x} (insert {d, x} (edges2 L))) →
        Relation.ReflTransGen (fun y z => ({y, z} : Finset V) ∈ edges2 L) (f p) (f q) := by
      intro p q hpq
      have fx : f x = b := by simp [f]
      have hcE : ({b, c} : Finset V) ∈ edges2 L := pair_mem_edges2 hτ (by simp) (by simp) hbc
      have hdE : ({b, d} : Finset V) ∈ edges2 L := pair_mem_edges2 hτ (by simp) (by simp) hbd
      have hcE' : ({c, b} : Finset V) ∈ edges2 L := by rw [pair_comm]; exact hcE
      have hdE' : ({d, b} : Finset V) ∈ edges2 L := by rw [pair_comm]; exact hdE
      rcases mem_insert.mp hpq with h | h
      · rcases pair_eq_pair_iff'.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hf _ hxb.symm, fx]
        · rw [hf _ hxb.symm, fx]
      rcases mem_insert.mp h with h | h
      · rcases pair_eq_pair_iff'.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hf _ hxc.symm, fx]; exact .single hcE'
        · rw [hf _ hxc.symm, fx]; exact .single hcE
      rcases mem_insert.mp h with h | h
      · rcases pair_eq_pair_iff'.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hf _ hxd.symm, fx]; exact .single hdE'
        · rw [hf _ hxd.symm, fx]; exact .single hdE
      · have hp : p ≠ x := fun e => hx (mem_verts2_of_sub (mem_edges2.mp h).choose_spec.1
          (mem_edges2.mp h).choose_spec.2.1 (by simp [e]))
        have hq : q ≠ x := fun e => hx (mem_verts2_of_sub (mem_edges2.mp h).choose_spec.1
          (mem_edges2.mp h).choose_spec.2.1 (by simp [e]))
        rw [hf _ hp, hf _ hq]
        exact .single h
    have := Relation.ReflTransGen.lift' f step _ _ (H u (mem_insert_of_mem hu) v (mem_insert_of_mem hv))
    simp only [Function.onFun, hf _ hux, hf _ hvx] at this
    exact this

/-- Flipping an edge keeps the 1-skeleton connected, in both directions. -/
lemma connected_flip22 {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) (h₁ : {b, c, d} ∈ L)
    (h₂ : {b, c, e} ∈ L) (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e}) :
    IsConnected2 L ↔
      IsConnected2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) := by
  unfold IsConnected2
  rw [verts2_flip22 h₁ h₂, edges2_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar]
  have keep : ∀ {p q : V}, ({p, q} : Finset V) ∈ edges2 L → ({p, q} : Finset V) ≠ {b, c} →
      ({p, q} : Finset V) ∈ insert {d, e} ((edges2 L).erase {b, c}) :=
    fun h hne => mem_insert_of_mem (mem_erase.mpr ⟨hne, h⟩)
  have ne_bc : ∀ {p q : V}, p ≠ b ∧ p ≠ c ∨ q ≠ b ∧ q ≠ c → ({p, q} : Finset V) ≠ {b, c} := by
    intro p q h heq
    rw [pair_eq_pair_iff'] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have bd : ({b, d} : Finset V) ∈ edges2 L := pair_mem_edges2 h₁ (by simp) (by simp) hbd
  have db : ({d, b} : Finset V) ∈ edges2 L := pair_mem_edges2 h₁ (by simp) (by simp) hbd.symm
  have cd : ({c, d} : Finset V) ∈ edges2 L := pair_mem_edges2 h₁ (by simp) (by simp) hcd
  have be : ({b, e} : Finset V) ∈ edges2 L := pair_mem_edges2 h₂ (by simp) (by simp) hbe
  have eb : ({e, b} : Finset V) ∈ edges2 L := pair_mem_edges2 h₂ (by simp) (by simp) hbe.symm
  have bd' := keep bd (ne_bc (Or.inr ⟨hbd.symm, hcd.symm⟩))
  have db' := keep db (ne_bc (Or.inl ⟨hbd.symm, hcd.symm⟩))
  have cd' := keep cd (ne_bc (Or.inr ⟨hbd.symm, hcd.symm⟩))
  have dc' : ({d, c} : Finset V) ∈ insert {d, e} ((edges2 L).erase {b, c}) := by
    rw [pair_comm d c]; exact cd'
  constructor
  · intro H u hu v hv
    refine Relation.ReflTransGen.lift' id (fun p q hpq => ?_) _ _ (H u hu v hv)
    show Relation.ReflTransGen _ p q
    by_cases h : ({p, q} : Finset V) = {b, c}
    · -- the step `bc` becomes `b d c`
      rcases pair_eq_pair_iff'.mp h with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · rw [hp, hq]; exact .tail (.single bd') dc'
      · rw [hp, hq]; exact .tail (.single cd') db'
    · exact .single (keep hpq h)
  · intro H u hu v hv
    refine Relation.ReflTransGen.lift' id (fun p q hpq => ?_) _ _ (H u hu v hv)
    show Relation.ReflTransGen _ p q
    rcases mem_insert.mp hpq with h | h
    · -- the step `de` becomes `d b e`
      rcases pair_eq_pair_iff'.mp h with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · rw [hp, hq]; exact .tail (.single db) be
      · rw [hp, hq]; exact .tail (.single eb) bd
    · exact .single (mem_of_mem_erase h)

/-- A 2-dimensional move keeps the 1-skeleton connected, in both directions. -/
theorem Move2.connected_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    IsConnected2 L ↔ IsConnected2 L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx => exact connected_sub13 hbc hbd hcd hτ hx
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    exact connected_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar

/-- **A combinatorial 2-sphere is connected.** -/
theorem IsSphere2.connected {L : Finset (Finset V)} (hL : IsSphere2 L) : IsConnected2 L := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩ := hL
  have key : ∀ L L' : Finset (Finset V), Relation.EqvGen Move2 L L' →
      (IsConnected2 L ↔ IsConnected2 L') := by
    intro L L' h
    induction h with
    | rel _ _ h => exact h.connected_iff
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  refine (key _ _ h).mp fun u hu v hv => ?_
  -- in the boundary of a tetrahedron every vertex is joined to `a` by an edge
  have hverts : ∀ w ∈ verts2 (bdry a b c d), w = a ∨ w = b ∨ w = c ∨ w = d :=
    fun w hw => mem_verts2_bdry hw
  have habc : ({a, b, c} : Finset V) ∈ bdry a b c d := by simp [bdry]
  have habd : ({a, b, d} : Finset V) ∈ bdry a b c d := by simp [bdry]
  have toA : ∀ w ∈ verts2 (bdry a b c d),
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (bdry a b c d)) w a := by
    intro w hw
    rcases hverts w hw with h | h | h | h <;> subst h
    · exact .refl
    · exact .single (pair_mem_edges2 habc (by simp) (by simp) hab.symm)
    · exact .single (pair_mem_edges2 habc (by simp) (by simp) hac.symm)
    · exact .single (pair_mem_edges2 habd (by simp) (by simp) had.symm)
  have fromA : ∀ w ∈ verts2 (bdry a b c d),
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (bdry a b c d)) a w := by
    intro w hw
    rcases hverts w hw with h | h | h | h <;> subst h
    · exact .refl
    · exact .single (pair_mem_edges2 habc (by simp) (by simp) hab)
    · exact .single (pair_mem_edges2 habc (by simp) (by simp) hac)
    · exact .single (pair_mem_edges2 habd (by simp) (by simp) had)
  exact (toA u hu).trans (fromA v hv)

/-! ## Closedness: every edge lies in exactly two triangles -/

/-- Every edge of `L` lies in exactly two triangles (`L` is a closed pseudo-surface). -/
def IsClosed2 (L : Finset (Finset V)) : Prop := ∀ f ∈ edges2 L, #(L.filter (f ⊆ ·)) = 2

omit [DecidableEq V] in
lemma card_filter_insert_of_notMem [DecidableEq V] {s : Finset (Finset V)} {a : Finset V}
    (ha : a ∉ s) (f : Finset V) :
    #((insert a s).filter (f ⊆ ·)) = #(s.filter (f ⊆ ·)) + if f ⊆ a then 1 else 0 := by
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hm => ha (mem_of_mem_filter _ hm))]
  · rfl

omit [DecidableEq V] in
lemma card_filter_erase_of_mem [DecidableEq V] {s : Finset (Finset V)} {a : Finset V} (ha : a ∈ s)
    (f : Finset V) :
    #((s.erase a).filter (f ⊆ ·)) + (if f ⊆ a then 1 else 0) = #(s.filter (f ⊆ ·)) := by
  rw [filter_erase]
  split_ifs with h
  · exact card_erase_add_one (mem_filter.mpr ⟨ha, h⟩)
  · rw [erase_eq_of_notMem (fun hm => h (mem_filter.mp hm).2), add_zero]

omit [DecidableEq V] in
lemma not_sub_of_notMem {f t : Finset V} {y : V} (hy : y ∈ f) (hy' : y ∉ t) : ¬ f ⊆ t :=
  fun h => hy' (h hy)

/-- Subdividing a triangle keeps every edge in exactly two triangles, in both directions. -/
lemma closed_sub13 {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hτ : {b, c, d} ∈ L) (hx : x ∉ verts2 L) :
    IsClosed2 L ↔
      IsClosed2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) := by
  obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
  have hnew : ∀ y z : V, ({y, z, x} : Finset V) ∉ L := fun y z hm =>
    hx (mem_verts2.mpr ⟨_, hm, by simp⟩)
  have n1 : ({b, d, x} : Finset V) ∉ L.erase {b, c, d} := fun h' => hnew _ _ (mem_of_mem_erase h')
  have n2 : ({c, d, x} : Finset V) ∉ insert {b, d, x} (L.erase {b, c, d}) := by
    rw [mem_insert, not_or]
    exact ⟨ne_of_mem_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hxc.symm]),
      fun h' => hnew _ _ (mem_of_mem_erase h')⟩
  have n3 : ({b, c, x} : Finset V) ∉ insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})) := by
    simp only [mem_insert, not_or]
    exact ⟨ne_of_mem_notMem (y := b) (by simp) (by simp [hbc, hbd, hxb.symm]),
      ne_of_mem_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hxc.symm]),
      fun h' => hnew _ _ (mem_of_mem_erase h')⟩
  have deg : ∀ f : Finset V,
      #((insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))).filter
        (f ⊆ ·)) + (if f ⊆ {b, c, d} then 1 else 0) =
      #(L.filter (f ⊆ ·)) + (if f ⊆ {b, c, x} then 1 else 0) + (if f ⊆ {c, d, x} then 1 else 0) +
        (if f ⊆ {b, d, x} then 1 else 0) := by
    intro f
    rw [card_filter_insert_of_notMem n3, card_filter_insert_of_notMem n2,
      card_filter_insert_of_notMem n1, ← card_filter_erase_of_mem hτ f]
    ring
  have old : ∀ f ∈ edges2 L,
      #((insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))).filter
        (f ⊆ ·)) = #(L.filter (f ⊆ ·)) := by
    intro f hf
    obtain ⟨τ0, hτ0, hsub0, hc⟩ := mem_edges2.mp hf
    have hxf : x ∉ f := fun h => hx (mem_verts2_of_sub hτ0 hsub0 h)
    have h := deg f
    by_cases hfs : f ⊆ {b, c, d}
    · rcases pair_of_sub3 hfs hc with rfl | rfl | rfl
      · have s1 : ({b, c} : Finset V) ⊆ {b, c, x} := by small_subset
        have e1 : ¬ ({b, c} : Finset V) ⊆ {c, d, x} :=
          not_sub_of_notMem (y := b) (by simp) (by simp [hbc, hbd, hxb.symm])
        have e2 : ¬ ({b, c} : Finset V) ⊆ {b, d, x} :=
          not_sub_of_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hxc.symm])
        simp only [hfs, s1, e1, e2, ite_true, ite_false] at h
        omega
      · have s1 : ({b, d} : Finset V) ⊆ {b, d, x} := by small_subset
        have e1 : ¬ ({b, d} : Finset V) ⊆ {b, c, x} :=
          not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hxd.symm])
        have e2 : ¬ ({b, d} : Finset V) ⊆ {c, d, x} :=
          not_sub_of_notMem (y := b) (by simp) (by simp [hbc, hbd, hxb.symm])
        simp only [hfs, s1, e1, e2, ite_true, ite_false] at h
        omega
      · have s1 : ({c, d} : Finset V) ⊆ {c, d, x} := by small_subset
        have e1 : ¬ ({c, d} : Finset V) ⊆ {b, c, x} :=
          not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hxd.symm])
        have e2 : ¬ ({c, d} : Finset V) ⊆ {b, d, x} :=
          not_sub_of_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hxc.symm])
        simp only [hfs, s1, e1, e2, ite_true, ite_false] at h
        omega
    · -- `f` avoids `x`, so it lies in no new triangle
      have n_bcx : ¬ f ⊆ {b, c, x} := fun h' => hfs fun y hy => by
        have := h' hy
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact absurd hy hxf
      have n_cdx : ¬ f ⊆ {c, d, x} := fun h' => hfs fun y hy => by
        have := h' hy
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact absurd hy hxf
      have n_bdx : ¬ f ⊆ {b, d, x} := fun h' => hfs fun y hy => by
        have := h' hy
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
        · exact absurd hy hxf
      simp only [hfs, n_bcx, n_cdx, n_bdx, ite_false] at h
      omega
  have zeroL : ∀ y : V, #(L.filter (({y, x} : Finset V) ⊆ ·)) = 0 := fun y => by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro τ hτL hsub
    exact hx (mem_verts2.mpr ⟨τ, hτL, hsub (by simp)⟩)
  have newdeg : ∀ f ∈ ({{b, x}, {c, x}, {d, x}} : Finset (Finset V)),
      #((insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))).filter
        (f ⊆ ·)) = 2 := by
    intro f hf
    have h := deg f
    simp only [mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · have s1 : ({b, x} : Finset V) ⊆ {b, c, x} := by small_subset
      have s2 : ({b, x} : Finset V) ⊆ {b, d, x} := by small_subset
      have e1 : ¬ ({b, x} : Finset V) ⊆ {c, d, x} :=
        not_sub_of_notMem (y := b) (by simp) (by simp [hbc, hbd, hxb.symm])
      have e2 : ¬ ({b, x} : Finset V) ⊆ {b, c, d} :=
        not_sub_of_notMem (y := x) (by simp) (by simp [hxb, hxc, hxd])
      simp only [zeroL, s1, s2, e1, e2, ite_true, ite_false] at h
      omega
    · have s1 : ({c, x} : Finset V) ⊆ {b, c, x} := by small_subset
      have s2 : ({c, x} : Finset V) ⊆ {c, d, x} := by small_subset
      have e1 : ¬ ({c, x} : Finset V) ⊆ {b, d, x} :=
        not_sub_of_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hxc.symm])
      have e2 : ¬ ({c, x} : Finset V) ⊆ {b, c, d} :=
        not_sub_of_notMem (y := x) (by simp) (by simp [hxb, hxc, hxd])
      simp only [zeroL, s1, s2, e1, e2, ite_true, ite_false] at h
      omega
    · have s1 : ({d, x} : Finset V) ⊆ {c, d, x} := by small_subset
      have s2 : ({d, x} : Finset V) ⊆ {b, d, x} := by small_subset
      have e1 : ¬ ({d, x} : Finset V) ⊆ {b, c, x} :=
        not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hxd.symm])
      have e2 : ¬ ({d, x} : Finset V) ⊆ {b, c, d} :=
        not_sub_of_notMem (y := x) (by simp) (by simp [hxb, hxc, hxd])
      simp only [zeroL, s1, s2, e1, e2, ite_true, ite_false] at h
      omega
  unfold IsClosed2
  rw [edges2_sub13 hτ hx]
  constructor
  · intro H f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact newdeg _ (by simp)
    rcases mem_insert.mp hf with rfl | hf
    · exact newdeg _ (by simp)
    rcases mem_insert.mp hf with rfl | hf
    · exact newdeg _ (by simp)
    · rw [old f hf]; exact H f hf
  · intro H f hf
    rw [← old f hf]
    exact H f (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem hf)))

/-- Flipping an edge keeps every edge in exactly two triangles, in both directions. -/
lemma closed_flip22 {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) (h₁ : {b, c, d} ∈ L)
    (h₂ : {b, c, e} ∈ L) (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e})
    (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ) :
    IsClosed2 L ↔
      IsClosed2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) := by
  have hne : ({b, c, e} : Finset V) ≠ {b, c, d} :=
    ne_of_mem_notMem (y := e) (by simp) (by simp [hbe.symm, hce.symm, hde.symm])
  have n1 : ({c, d, e} : Finset V) ∉ (L.erase {b, c, d}).erase {b, c, e} := fun h' =>
    hfresh _ (mem_of_mem_erase (mem_of_mem_erase h')) (by small_subset)
  have n2 : ({b, d, e} : Finset V) ∉ insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}) := by
    rw [mem_insert, not_or]
    exact ⟨ne_of_mem_notMem (y := b) (by simp) (by simp [hbc, hbd, hbe]),
      fun h' => hfresh _ (mem_of_mem_erase (mem_of_mem_erase h')) (by small_subset)⟩
  have deg : ∀ f : Finset V,
      #((insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))).filter
        (f ⊆ ·)) + (if f ⊆ {b, c, e} then 1 else 0) + (if f ⊆ {b, c, d} then 1 else 0) =
      #(L.filter (f ⊆ ·)) + (if f ⊆ {b, d, e} then 1 else 0) + (if f ⊆ {c, d, e} then 1 else 0) := by
    intro f
    rw [card_filter_insert_of_notMem n2, card_filter_insert_of_notMem n1,
      ← card_filter_erase_of_mem h₁ f,
      ← card_filter_erase_of_mem (mem_erase.mpr ⟨hne, h₂⟩) f]
    ring
  have hdeL : #(L.filter (({d, e} : Finset V) ⊆ ·)) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun τ hτ => hfresh τ hτ
  have hbcL : #(L.filter (({b, c} : Finset V) ⊆ ·)) = 2 := by
    have : L.filter (({b, c} : Finset V) ⊆ ·) = {{b, c, d}, {b, c, e}} := by
      ext τ
      simp only [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hτ, hsub⟩
        exact hstar τ hτ hsub
      · rintro (rfl | rfl)
        · exact ⟨h₁, by small_subset⟩
        · exact ⟨h₂, by small_subset⟩
    rw [this, card_pair hne.symm]
  have old : ∀ f ∈ edges2 L, f ≠ {b, c} →
      #((insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))).filter
        (f ⊆ ·)) = #(L.filter (f ⊆ ·)) := by
    intro f hf hfbc
    obtain ⟨τ0, hτ0, hsub0, hc⟩ := mem_edges2.mp hf
    have h := deg f
    by_cases h1 : f ⊆ {b, c, d}
    · rcases pair_of_sub3 h1 hc with rfl | rfl | rfl
      · exact absurd rfl hfbc
      · have s1 : ({b, d} : Finset V) ⊆ {b, d, e} := by small_subset
        have e1 : ¬ ({b, d} : Finset V) ⊆ {c, d, e} :=
          not_sub_of_notMem (y := b) (by simp) (by simp [hbc, hbd, hbe])
        have e2 : ¬ ({b, d} : Finset V) ⊆ {b, c, e} :=
          not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hde])
        simp only [h1, s1, e1, e2, ite_true, ite_false] at h
        omega
      · have s1 : ({c, d} : Finset V) ⊆ {c, d, e} := by small_subset
        have e1 : ¬ ({c, d} : Finset V) ⊆ {b, d, e} :=
          not_sub_of_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hce])
        have e2 : ¬ ({c, d} : Finset V) ⊆ {b, c, e} :=
          not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hde])
        simp only [h1, s1, e1, e2, ite_true, ite_false] at h
        omega
    by_cases h2 : f ⊆ {b, c, e}
    · rcases pair_of_sub3 h2 hc with rfl | rfl | rfl
      · exact absurd rfl hfbc
      · have s1 : ({b, e} : Finset V) ⊆ {b, d, e} := by small_subset
        have e1 : ¬ ({b, e} : Finset V) ⊆ {c, d, e} :=
          not_sub_of_notMem (y := b) (by simp) (by simp [hbc, hbd, hbe])
        simp only [h1, h2, s1, e1, ite_true, ite_false] at h
        omega
      · have s1 : ({c, e} : Finset V) ⊆ {c, d, e} := by small_subset
        have e1 : ¬ ({c, e} : Finset V) ⊆ {b, d, e} :=
          not_sub_of_notMem (y := c) (by simp) (by simp [hbc.symm, hcd, hce])
        simp only [h1, h2, s1, e1, ite_true, ite_false] at h
        omega
    · -- `f` is in neither old triangle, so in neither new one
      have k1 : ¬ f ⊆ {b, d, e} := fun h' => by
        rcases pair_of_sub3 h' hc with rfl | rfl | rfl
        · exact h1 (by small_subset)
        · exact h2 (by small_subset)
        · exact hfresh τ0 hτ0 hsub0
      have k2 : ¬ f ⊆ {c, d, e} := fun h' => by
        rcases pair_of_sub3 h' hc with rfl | rfl | rfl
        · exact h1 (by small_subset)
        · exact h2 (by small_subset)
        · exact hfresh τ0 hτ0 hsub0
      simp only [h1, h2, k1, k2, ite_false] at h
      omega
  have newdeg : #((insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))).filter
      (({d, e} : Finset V) ⊆ ·)) = 2 := by
    have h := deg {d, e}
    have s1 : ({d, e} : Finset V) ⊆ {b, d, e} := by small_subset
    have s2 : ({d, e} : Finset V) ⊆ {c, d, e} := by small_subset
    have e1 : ¬ ({d, e} : Finset V) ⊆ {b, c, e} :=
      not_sub_of_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hde])
    have e2 : ¬ ({d, e} : Finset V) ⊆ {b, c, d} :=
      not_sub_of_notMem (y := e) (by simp) (by simp [hbe.symm, hce.symm, hde.symm])
    simp only [hdeL, s1, s2, e1, e2, ite_true, ite_false] at h
    omega
  unfold IsClosed2
  rw [edges2_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar]
  constructor
  · intro H f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact newdeg
    · obtain ⟨hfbc, hf⟩ := mem_erase.mp hf
      rw [old f hf hfbc]
      exact H f hf
  · intro H f hf
    by_cases hfbc : f = {b, c}
    · rw [hfbc]; exact hbcL
    · rw [← old f hf hfbc]
      exact H f (mem_insert_of_mem (mem_erase.mpr ⟨hfbc, hf⟩))

/-- A 2-dimensional move keeps every edge in exactly two triangles, in both directions. -/
theorem Move2.closed_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    IsClosed2 L ↔ IsClosed2 L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx => exact closed_sub13 hbc hbd hcd hτ hx
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    exact closed_flip22 hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh

section bdryClosed

-- The generated case analysis passes the same simp lemmas everywhere; not every case uses all.
set_option linter.unusedSimpArgs false

variable {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
  (hcd : c ≠ d)
include hab hac had hbc hbd hcd

/-- In the boundary of a tetrahedron every edge lies in exactly two triangles. -/
lemma closed_bdry : IsClosed2 (bdry a b c d) := by
  have n1 : ({a, c, d} : Finset V) ∉ ({{b, c, d}} : Finset (Finset V)) := by
    rw [mem_singleton]; exact ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had])
  have n2 : ({a, b, d} : Finset V) ∉ ({{a, c, d}, {b, c, d}} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨ne_of_mem_notMem (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had])⟩
  have n3 : ({a, b, c} : Finset V) ∉ ({{a, b, d}, {a, c, d}, {b, c, d}} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨ne_of_mem_notMem (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      ne_of_mem_notMem (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      ne_of_mem_notMem (y := a) (by simp) (by simp [hab, hac, had])⟩
  have deg : ∀ f : Finset V, #((bdry a b c d).filter (f ⊆ ·)) =
      (if f ⊆ {a, b, c} then 1 else 0) + (if f ⊆ {a, b, d} then 1 else 0) +
        (if f ⊆ {a, c, d} then 1 else 0) + (if f ⊆ {b, c, d} then 1 else 0) := by
    intro f
    rw [bdry, card_filter_insert_of_notMem n3, card_filter_insert_of_notMem n2,
      card_filter_insert_of_notMem n1, filter_singleton]
    split_ifs <;> simp
  intro f hf
  obtain ⟨τ, hτ, hsub, hc⟩ := mem_edges2.mp hf
  simp only [bdry, mem_insert, mem_singleton] at hτ
  rw [deg]
  rcases hτ with rfl | rfl | rfl | rfl <;> rcases pair_of_sub3 hsub hc with rfl | rfl | rfl
  · -- edge ab
    simp only [show ({a, b} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      show ({a, b} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, b}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      not_sub_of_notMem (f := {a, b}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge ac
    simp only [show ({a, c} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, c}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      show ({a, c} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, c}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge bc
    simp only [show ({b, c} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {b, c}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      not_sub_of_notMem (f := {b, c}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      show ({b, c} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]
  · -- edge ab
    simp only [show ({a, b} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      show ({a, b} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, b}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      not_sub_of_notMem (f := {a, b}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge ad
    simp only [not_sub_of_notMem (f := {a, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      show ({a, d} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      show ({a, d} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, d}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge bd
    simp only [not_sub_of_notMem (f := {b, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      show ({b, d} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {b, d}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      show ({b, d} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]
  · -- edge ac
    simp only [show ({a, c} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, c}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      show ({a, c} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, c}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge ad
    simp only [not_sub_of_notMem (f := {a, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      show ({a, d} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      show ({a, d} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {a, d}) (t := {b, c, d}) (y := a) (by simp) (by simp [hab, hac, had]), ite_true, ite_false]
  · -- edge cd
    simp only [not_sub_of_notMem (f := {c, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      not_sub_of_notMem (f := {c, d}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      show ({c, d} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      show ({c, d} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]
  · -- edge bc
    simp only [show ({b, c} : Finset V) ⊆ {a, b, c} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {b, c}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      not_sub_of_notMem (f := {b, c}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      show ({b, c} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]
  · -- edge bd
    simp only [not_sub_of_notMem (f := {b, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      show ({b, d} : Finset V) ⊆ {a, b, d} by simp [insert_subset_iff],
      not_sub_of_notMem (f := {b, d}) (t := {a, c, d}) (y := b) (by simp) (by simp [hab.symm, hbc, hbd]),
      show ({b, d} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]
  · -- edge cd
    simp only [not_sub_of_notMem (f := {c, d}) (t := {a, b, c}) (y := d) (by simp) (by simp [had.symm, hbd.symm, hcd.symm]),
      not_sub_of_notMem (f := {c, d}) (t := {a, b, d}) (y := c) (by simp) (by simp [hac.symm, hbc.symm, hcd]),
      show ({c, d} : Finset V) ⊆ {a, c, d} by simp [insert_subset_iff],
      show ({c, d} : Finset V) ⊆ {b, c, d} by simp [insert_subset_iff], ite_true, ite_false]

end bdryClosed

/-- **In a combinatorial 2-sphere every edge lies in exactly two triangles.** -/
theorem IsSphere2.closed {L : Finset (Finset V)} (hL : IsSphere2 L) : IsClosed2 L := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩ := hL
  have key : ∀ L L' : Finset (Finset V), Relation.EqvGen Move2 L L' →
      (IsClosed2 L ↔ IsClosed2 L') := by
    intro L L' h
    induction h with
    | rel _ _ h => exact h.closed_iff
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key _ _ h).mp (closed_bdry hab hac had hbc hbd hcd)

/-- **Summary: a combinatorial 2-sphere is a connected closed pseudo-surface with Euler
characteristic `2`.** -/
theorem IsSphere2.invariants {L : Finset (Finset V)} (hL : IsSphere2 L) :
    euler2 L = 2 ∧ IsConnected2 L ∧ IsClosed2 L :=
  ⟨hL.euler, hL.connected, hL.closed⟩

end Lightlike.PR
