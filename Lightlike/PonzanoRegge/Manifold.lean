module

public import Lightlike.PonzanoRegge.InverseMoves

/-!
# Combinatorial 3-manifolds, and the Pachner moves preserve them

The amplitude theorems hold for every pure 3-complex (`Complex3`). Here we single out the
complexes that triangulate a closed 3-manifold and show that the 2-3, 1-4, 3-2 and 4-1 moves keep
a complex in that class.

* **Combinatorial 2-spheres.** A 2-complex is a finite set of triangles (3-element vertex sets).
  `Move2` is a 2-dimensional bistellar move: `sub13` subdivides a triangle by a new vertex, and
  `flip22` replaces two triangles `bcd, bce` sharing the edge `bc` by `bde, cde`. `IsSphere2 L`
  says that `L` is obtained from the boundary of a tetrahedron by such moves and their inverses.
  By Pachner's theorem in dimension 2 (a classical result, not formalised here), these are exactly
  the combinatorial triangulations of the 2-sphere. `IsSphere2.even_card`: such a complex has an
  even number of triangles; `SphereInvariants.lean` proves that it is connected, has Euler
  characteristic 2 and every edge in exactly two triangles.
* **Links and manifolds.** `Complex3.link K v` is the set of triangles opposite `v` in the
  tetrahedra through `v`. `IsCombManifold K` says that the link of every vertex is a combinatorial
  2-sphere: this is the standard definition of a closed combinatorial (PL) 3-manifold.
* **The moves preserve it.** In each move the link of a vertex either stays the same or changes by
  one 2-dimensional move (`link_move14_*`, `link_move23_*`), and the new vertex of a 1-4 move has
  the boundary of a tetrahedron as its link. Hence `isCombManifold_move23_iff`,
  `isCombManifold_move14_iff`, `isCombManifold_move32_iff`, `isCombManifold_move41_iff`.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Combinatorial 2-spheres -/

/-- The vertices of a 2-complex (a finite set of triangles). -/
def verts2 (L : Finset (Finset V)) : Finset V := L.biUnion id

lemma mem_verts2 {L : Finset (Finset V)} {x : V} : x ∈ verts2 L ↔ ∃ τ ∈ L, x ∈ τ := by
  simp [verts2]

/-- The boundary of the tetrahedron `abcd`: its four triangles. -/
def bdry (a b c d : V) : Finset (Finset V) := {{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}}

/-- A **2-dimensional bistellar move** on a 2-complex.
* `sub13`: subdivide the triangle `bcd` by a new vertex `x` (three triangles replace one).
* `flip22`: the edge `bc` lies in exactly the triangles `bcd`, `bce`, and `de` is not an edge;
  replace them by `bde`, `cde`. -/
inductive Move2 : Finset (Finset V) → Finset (Finset V) → Prop
  | sub13 {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
      (hτ : {b, c, d} ∈ L) (hx : x ∉ verts2 L) :
      Move2 L (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d}))))
  | flip22 {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
      (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L)
      (hstar : ∀ τ ∈ L, {b, c} ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e})
      (hfresh : ∀ τ ∈ L, ¬ {d, e} ⊆ τ) :
      Move2 L (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e})))

/-- `L` is a **combinatorial 2-sphere**: it is obtained from the boundary of a tetrahedron by
2-dimensional bistellar moves and their inverses. -/
def IsSphere2 (L : Finset (Finset V)) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    Relation.EqvGen Move2 (bdry a b c d) L

/-- The boundary of a tetrahedron is a combinatorial 2-sphere. -/
theorem isSphere2_bdry {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : IsSphere2 (bdry a b c d) :=
  ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, .refl _⟩

/-- Combinatorial 2-spheres are closed under 2-dimensional moves, in both directions. -/
theorem IsSphere2.of_eqvGen {L L' : Finset (Finset V)} (hL : IsSphere2 L)
    (h : Relation.EqvGen Move2 L L') : IsSphere2 L' := by
  obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, hL⟩ := hL
  exact ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, hL.trans _ _ _ h⟩

/-- A 2-dimensional move changes the number of triangles by an even number. -/
lemma Move2.even_iff {L L' : Finset (Finset V)} (h : Move2 L L') : Even #L ↔ Even #L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx =>
    have hnew : ∀ y z : V, ({y, z, x} : Finset V) ∉ L := fun y z hm =>
      hx (mem_verts2.mpr ⟨_, hm, by simp⟩)
    have hxb : x ≠ b := fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩)
    have hxc : x ≠ c := fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩)
    have hxd : x ≠ d := fun h => hx (mem_verts2.mpr ⟨_, hτ, by simp [h]⟩)
    have n1 : ({b, d, x} : Finset V) ∉ L.erase {b, c, d} := fun h' => hnew _ _ (mem_of_mem_erase h')
    have n2 : ({c, d, x} : Finset V) ∉ insert {b, d, x} (L.erase {b, c, d}) := by
      rw [mem_insert, not_or]
      refine ⟨fun h' => hbc ?_, fun h' => hnew _ _ (mem_of_mem_erase h')⟩
      have : c ∈ ({b, d, x} : Finset V) := h' ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h'' | h'' | h''
      · exact h''.symm
      · exact absurd h'' hcd
      · exact absurd h''.symm hxc
    have n3 : ({b, c, x} : Finset V) ∉ insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})) := by
      simp only [mem_insert, not_or]
      refine ⟨fun h' => hbc ?_, fun h' => hcd ?_, fun h' => hnew _ _ (mem_of_mem_erase h')⟩
      · have : b ∈ ({c, d, x} : Finset V) := h' ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h''
        · exact h''
        · exact absurd h'' hbd
        · exact absurd h''.symm hxb
      · have : d ∈ ({b, c, x} : Finset V) := h' ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h'' | h'' | h''
        · exact absurd h''.symm hbd
        · exact h''.symm
        · exact absurd h''.symm hxd
    rw [card_insert_of_notMem n3, card_insert_of_notMem n2, card_insert_of_notMem n1,
      card_erase_of_mem hτ]
    have : 0 < #L := card_pos.mpr ⟨_, hτ⟩
    rw [show #L - 1 + 1 + 1 + 1 = #L + 2 by omega, Nat.even_add]
    simp
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
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
    rw [show #L - 1 - 1 + 1 + 1 = #L by omega]

/-- **A combinatorial 2-sphere has an even number of triangles** (the boundary of a tetrahedron
has four, and every move changes the number by `0` or `±2`). -/
theorem IsSphere2.even_card {L : Finset (Finset V)} (hL : IsSphere2 L) : Even #L := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩ := hL
  have h0 : #(bdry a b c d) = 4 := by
    have n1 : ({a, b, c} : Finset V) ∉ ({{a, b, d}, {a, c, d}, {b, c, d}} : Finset (Finset V)) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h => hcd ?_, fun h => hbd ?_, fun h => hab ?_⟩
      · have : c ∈ ({a, b, d} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        · exact absurd h'.symm hac
        · exact absurd h'.symm hbc
        · exact h'
      · have : b ∈ ({a, c, d} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        · exact absurd h'.symm hab
        · exact absurd h' hbc
        · exact h'
      · have : a ∈ ({b, c, d} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        · exact h'
        · exact absurd h' hac
        · exact absurd h' had
    have n2 : ({a, b, d} : Finset V) ∉ ({{a, c, d}, {b, c, d}} : Finset (Finset V)) := by
      simp only [mem_insert, mem_singleton, not_or]
      refine ⟨fun h => hbc ?_, fun h => hab ?_⟩
      · have : b ∈ ({a, c, d} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        · exact absurd h'.symm hab
        · exact h'
        · exact absurd h' hbd
      · have : a ∈ ({b, c, d} : Finset V) := h ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        · exact h'
        · exact absurd h' hac
        · exact absurd h' had
    have n3 : ({a, c, d} : Finset V) ≠ {b, c, d} := fun h => hab (by
      have : a ∈ ({b, c, d} : Finset V) := h ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      · exact h'
      · exact absurd h' hac
      · exact absurd h' had)
    rw [bdry, card_insert_of_notMem n1, card_insert_of_notMem n2, card_pair n3]
  have key : ∀ L L' : Finset (Finset V), Relation.EqvGen Move2 L L' → (Even #L ↔ Even #L') := by
    intro L L' h
    induction h with
    | rel _ _ h => exact h.even_iff
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key _ _ h).mp (by rw [h0]; decide)

/-! ## Links and combinatorial 3-manifolds -/

/-- The **link** of a vertex `v` in `K`: the triangles opposite `v` in the tetrahedra through `v`. -/
def Complex3.link (K : Complex3 V) (v : V) : Finset (Finset V) :=
  (K.tets.filter (v ∈ ·)).image (·.erase v)

lemma Complex3.mem_link {K : Complex3 V} {v : V} {τ : Finset V} :
    τ ∈ K.link v ↔ v ∉ τ ∧ insert v τ ∈ K.tets := by
  simp only [Complex3.link, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hv⟩, rfl⟩
    exact ⟨notMem_erase v t, by rwa [insert_erase hv]⟩
  · rintro ⟨hv, ht⟩
    exact ⟨insert v τ, ⟨ht, mem_insert_self v τ⟩, erase_insert hv⟩

/-- `K` is a **closed combinatorial 3-manifold**: the link of every vertex is a combinatorial
2-sphere. -/
def IsCombManifold (K : Complex3 V) : Prop := ∀ v ∈ K.verts, IsSphere2 (K.link v)

/-! ## How links change under the moves -/

-- The link computations pass every distinctness fact to `simp`; each proof uses only some of them.
set_option linter.unusedSimpArgs false

lemma insert_eq_iff_of_notMem {v : V} {τ s : Finset V} (hv : v ∉ τ) :
    insert v τ = s ↔ v ∈ s ∧ τ = s.erase v := by
  constructor
  · rintro rfl
    exact ⟨mem_insert_self v τ, (erase_insert hv).symm⟩
  · rintro ⟨hs, rfl⟩
    exact insert_erase hs

/-- Equality of small explicit vertex sets. -/
macro "fset_eq" : tactic =>
  `(tactic| (ext x; simp only [mem_insert, mem_singleton, mem_erase, ne_eq]; aesop))

/-- Under a 1-4 move, the link of the new vertex `E` is the boundary of the tetrahedron `ABCD`. -/
theorem link_move14_new {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    (move14 K h).link E = bdry A B C D := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, -, -⟩ := id h
  ext τ
  rw [Complex3.mem_link]
  by_cases hE : E ∈ τ
  · simp only [hE, not_true_eq_false, false_and, false_iff, bdry, mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | rfl) <;> simp [h.hAE.symm, h.hBE.symm, h.hCE.symm, h.hDE.symm] at hE
  simp only [hE, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
    mem_erase, insert_eq_iff_of_notMem hE, bdry]
  have e1 : ({A, B, C, E} : Finset V).erase E = {A, B, C} := by fset_eq
  have e2 : ({A, B, D, E} : Finset V).erase E = {A, B, D} := by fset_eq
  have e3 : ({A, C, D, E} : Finset V).erase E = {A, C, D} := by fset_eq
  have e4 : ({B, C, D, E} : Finset V).erase E = {B, C, D} := by fset_eq
  simp only [e1, e2, e3, e4, or_true, true_and]
  constructor
  · rintro ((h1 | h1 | h1 | h1) | ⟨-, ht⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
    · exact absurd (mem_insert_self E τ) (h.fresh _ ht)
  · rintro (h1 | h1 | h1 | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h1))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h1)))

/-- Under a 1-4 move, the link of `A` changes by subdividing the triangle `BCD` with `E`. -/
theorem link_move14_A {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    Move2 (K.link A) ((move14 K h).link A) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem, hfresh⟩ := id h
  have hlink : (move14 K h).link A = insert {B, C, E} (insert {C, D, E} (insert {B, D, E}
      ((K.link A).erase {B, C, D}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : A ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, C, E} : Finset V).erase A = {B, C, E} := by fset_eq
    have e1 : ({A, B, D, E} : Finset V).erase A = {B, D, E} := by fset_eq
    have e2 : ({A, C, D, E} : Finset V).erase A = {C, D, E} := by fset_eq
    have e3 : ({A, B, C, D} : Finset V).erase A = {B, C, D} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and, false_or,
      true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hBC hBD hCD (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], hmem⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hEτ⟩ := mem_verts2.mp hm
      exact hfresh _ (Complex3.mem_link.mp hτ).2 (mem_insert_of_mem hEτ))

/-- Under a 1-4 move, the link of `B` changes by subdividing the triangle `ACD` with `E`. -/
theorem link_move14_B {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    Move2 (K.link B) ((move14 K h).link B) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem, hfresh⟩ := id h
  have hlink : (move14 K h).link B = insert {A, C, E} (insert {C, D, E} (insert {A, D, E}
      ((K.link B).erase {A, C, D}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : B ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, C, E} : Finset V).erase B = {A, C, E} := by fset_eq
    have e1 : ({A, B, D, E} : Finset V).erase B = {A, D, E} := by fset_eq
    have e2 : ({B, C, D, E} : Finset V).erase B = {C, D, E} := by fset_eq
    have e3 : ({A, B, C, D} : Finset V).erase B = {A, C, D} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hAC hAD hCD
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert B {A, C, D} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem)⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hm
      exact hfresh _ (Complex3.mem_link.mp hτ).2 (mem_insert_of_mem hxτ))

/-- Under a 1-4 move, the link of `C` changes by subdividing the triangle `ABD` with `E`. -/
theorem link_move14_C {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    Move2 (K.link C) ((move14 K h).link C) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem, hfresh⟩ := id h
  have hlink : (move14 K h).link C = insert {A, B, E} (insert {B, D, E} (insert {A, D, E}
      ((K.link C).erase {A, B, D}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : C ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, C, E} : Finset V).erase C = {A, B, E} := by fset_eq
    have e1 : ({A, C, D, E} : Finset V).erase C = {A, D, E} := by fset_eq
    have e2 : ({B, C, D, E} : Finset V).erase C = {B, D, E} := by fset_eq
    have e3 : ({A, B, C, D} : Finset V).erase C = {A, B, D} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hAB hAD hBD
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert C {A, B, D} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem)⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hm
      exact hfresh _ (Complex3.mem_link.mp hτ).2 (mem_insert_of_mem hxτ))

/-- Under a 1-4 move, the link of `D` changes by subdividing the triangle `ABC` with `E`. -/
theorem link_move14_D {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    Move2 (K.link D) ((move14 K h).link D) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem, hfresh⟩ := id h
  have hlink : (move14 K h).link D = insert {A, B, E} (insert {B, C, E} (insert {A, C, E}
      ((K.link D).erase {A, B, C}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : D ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, D, E} : Finset V).erase D = {A, B, E} := by fset_eq
    have e1 : ({A, C, D, E} : Finset V).erase D = {A, C, E} := by fset_eq
    have e2 : ({B, C, D, E} : Finset V).erase D = {B, C, E} := by fset_eq
    have e3 : ({A, B, C, D} : Finset V).erase D = {A, B, C} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hAB hAC hBC
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert D {A, B, C} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem)⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hm
      exact hfresh _ (Complex3.mem_link.mp hτ).2 (mem_insert_of_mem hxτ))

/-- Under a 1-4 move, the link of any vertex other than `A, B, C, D, E` is unchanged. -/
theorem link_move14_other {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E)
    {v : V} (hvA : v ≠ A) (hvB : v ≠ B) (hvC : v ≠ C) (hvD : v ≠ D) (hvE : v ≠ E) :
    (move14 K h).link v = K.link v := by
  ext τ
  rw [Complex3.mem_link, Complex3.mem_link]
  by_cases hv : v ∈ τ
  · simp [hv]
  simp only [hv, not_false_eq_true, true_and, move14, mem_union, mem_insert, mem_singleton,
    mem_erase, ne_eq, insert_eq_iff_of_notMem hv, hvA, hvB, hvC, hvD, hvE, false_or, or_false,
    false_and, not_false_eq_true]

/-- Under a 2-3 move, the link of `D` changes by subdividing the triangle `ABC` with `E`. -/
theorem link_move23_D {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    Move2 (K.link D) ((move23 K h).link D) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem₁, hmem₂, hface, hfresh⟩ := id h
  have hlink : (move23 K h).link D = insert {A, B, E} (insert {B, C, E} (insert {A, C, E}
      ((K.link D).erase {A, B, C}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : D ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, D, E} : Finset V).erase D = {A, B, E} := by fset_eq
    have e1 : ({B, C, D, E} : Finset V).erase D = {B, C, E} := by fset_eq
    have e2 : ({C, A, D, E} : Finset V).erase D = {A, C, E} := by fset_eq
    have e3 : ({A, B, C, D} : Finset V).erase D = {A, B, C} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hAB hAC hBC
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert D {A, B, C} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem₁)⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hm
      refine hfresh _ (Complex3.mem_link.mp hτ).2 ?_
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem hxτ)

/-- Under a 2-3 move, the link of `E` changes by subdividing the triangle `ABC` with `D`. -/
theorem link_move23_E {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    Move2 (K.link E) ((move23 K h).link E) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem₁, hmem₂, hface, hfresh⟩ := id h
  have hlink : (move23 K h).link E = insert {A, B, D} (insert {B, C, D} (insert {A, C, D}
      ((K.link E).erase {A, B, C}))) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : E ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | rfl | ⟨-, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, D, E} : Finset V).erase E = {A, B, D} := by fset_eq
    have e1 : ({B, C, D, E} : Finset V).erase E = {B, C, D} := by fset_eq
    have e2 : ({C, A, D, E} : Finset V).erase E = {A, C, D} := by fset_eq
    have e3 : ({A, B, C, E} : Finset V).erase E = {A, B, C} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  exact Move2.sub13 hAB hAC hBC
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert E {A, B, C} : Finset V) = {A, B, C, E} by fset_eq]; exact hmem₂)⟩)
    (fun hm => by
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hm
      refine hfresh _ (Complex3.mem_link.mp hτ).2 ?_
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact mem_insert_of_mem hxτ
      · exact mem_insert_self _ _)

/-- Under a 2-3 move, the link of `A` changes by flipping the edge `BC` to `DE`. -/
theorem link_move23_A {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    Move2 (K.link A) ((move23 K h).link A) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem₁, hmem₂, hface, hfresh⟩ := id h
  have hlink : (move23 K h).link A = insert {B, D, E} (insert {C, D, E}
      (((K.link A).erase {B, C, D}).erase {B, C, E})) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : A ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | ⟨-, -, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, D, E} : Finset V).erase A = {B, D, E} := by fset_eq
    have e1 : ({C, A, D, E} : Finset V).erase A = {C, D, E} := by fset_eq
    have e2 : ({A, B, C, D} : Finset V).erase A = {B, C, D} := by fset_eq
    have e3 : ({A, B, C, E} : Finset V).erase A = {B, C, E} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  refine Move2.flip22 hBC hBD hBE hCD hCE hDE
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], hmem₁⟩)
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], hmem₂⟩) ?_ ?_
  · intro τ hτ hsub
    obtain ⟨hXτ, hτK⟩ := Complex3.mem_link.mp hτ
    have hsub' : ({A, B, C} : Finset V) ⊆ insert A τ := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr (hsub (by simp))
    rcases hface _ hτK hsub' with h1 | h1
    · left
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
    · right
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
  · intro τ hτ hsub
    exact hfresh _ (Complex3.mem_link.mp hτ).2 (hsub.trans (subset_insert _ _))

/-- Under a 2-3 move, the link of `B` changes by flipping the edge `AC` to `DE`. -/
theorem link_move23_B {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    Move2 (K.link B) ((move23 K h).link B) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem₁, hmem₂, hface, hfresh⟩ := id h
  have hlink : (move23 K h).link B = insert {A, D, E} (insert {C, D, E}
      (((K.link B).erase {A, C, D}).erase {A, C, E})) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : B ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | ⟨-, -, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({A, B, D, E} : Finset V).erase B = {A, D, E} := by fset_eq
    have e1 : ({B, C, D, E} : Finset V).erase B = {C, D, E} := by fset_eq
    have e2 : ({A, B, C, D} : Finset V).erase B = {A, C, D} := by fset_eq
    have e3 : ({A, B, C, E} : Finset V).erase B = {A, C, E} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  refine Move2.flip22 hAC hAD hAE hCD hCE hDE
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert B {A, C, D} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem₁)⟩)
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert B {A, C, E} : Finset V) = {A, B, C, E} by fset_eq]; exact hmem₂)⟩) ?_ ?_
  · intro τ hτ hsub
    obtain ⟨hXτ, hτK⟩ := Complex3.mem_link.mp hτ
    have hsub' : ({A, B, C} : Finset V) ⊆ insert B τ := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr (hsub (by simp))
    rcases hface _ hτK hsub' with h1 | h1
    · left
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
    · right
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
  · intro τ hτ hsub
    exact hfresh _ (Complex3.mem_link.mp hτ).2 (hsub.trans (subset_insert _ _))

/-- Under a 2-3 move, the link of `C` changes by flipping the edge `AB` to `DE`. -/
theorem link_move23_C {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    Move2 (K.link C) ((move23 K h).link C) := by
  obtain ⟨hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hmem₁, hmem₂, hface, hfresh⟩ := id h
  have hlink : (move23 K h).link C = insert {A, D, E} (insert {B, D, E}
      (((K.link C).erase {A, B, D}).erase {A, B, E})) := by
    ext τ
    rw [Complex3.mem_link]
    by_cases hX : C ∈ τ
    · simp only [hX, not_true_eq_false, false_and, false_iff]
      intro hm
      simp only [mem_insert, mem_erase, Complex3.mem_link] at hm
      rcases hm with rfl | rfl | ⟨-, -, hX', -⟩ <;>
        first | exact hX' hX | simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm] at hX
    simp only [hX, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
      mem_erase, ne_eq, insert_eq_iff_of_notMem hX, Complex3.mem_link]
    have e0 : ({B, C, D, E} : Finset V).erase C = {B, D, E} := by fset_eq
    have e1 : ({C, A, D, E} : Finset V).erase C = {A, D, E} := by fset_eq
    have e2 : ({A, B, C, D} : Finset V).erase C = {A, B, D} := by fset_eq
    have e3 : ({A, B, C, E} : Finset V).erase C = {A, B, E} := by fset_eq
    simp only [e0, e1, e2, e3, hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, or_true, true_and, or_false, false_and,
      false_or, true_or, and_true, ne_eq]
    tauto
  rw [hlink]
  refine Move2.flip22 hAB hAD hAE hBD hBE hDE
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert C {A, B, D} : Finset V) = {A, B, C, D} by fset_eq]; exact hmem₁)⟩)
    (Complex3.mem_link.mpr ⟨by simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm], (by rw [show (insert C {A, B, E} : Finset V) = {A, B, C, E} by fset_eq]; exact hmem₂)⟩) ?_ ?_
  · intro τ hτ hsub
    obtain ⟨hXτ, hτK⟩ := Complex3.mem_link.mp hτ
    have hsub' : ({A, B, C} : Finset V) ⊆ insert C τ := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy ⊢
      rcases hy with rfl | rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr (hsub (by simp))
    rcases hface _ hτK hsub' with h1 | h1
    · left
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
    · right
      rw [((insert_eq_iff_of_notMem hXτ).mp h1).2]
      fset_eq
  · intro τ hτ hsub
    exact hfresh _ (Complex3.mem_link.mp hτ).2 (hsub.trans (subset_insert _ _))

/-- Under a 2-3 move, the link of any vertex other than `A, B, C, D, E` is unchanged. -/
theorem link_move23_other {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E)
    {v : V} (hvA : v ≠ A) (hvB : v ≠ B) (hvC : v ≠ C) (hvD : v ≠ D) (hvE : v ≠ E) :
    (move23 K h).link v = K.link v := by
  ext τ
  rw [Complex3.mem_link, Complex3.mem_link]
  by_cases hv : v ∈ τ
  · simp [hv]
  simp only [hv, not_false_eq_true, true_and, move23, mem_union, mem_insert, mem_singleton,
    mem_erase, ne_eq, insert_eq_iff_of_notMem hv, hvA, hvB, hvC, hvD, hvE, false_or, or_false,
    false_and, not_false_eq_true]

/-! ## The moves preserve combinatorial 3-manifolds -/

/-- Under a 1-4 move, the link of every old vertex is its old link, or differs from it by one
2-dimensional move. -/
theorem link_move14_eqvGen {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) {v : V}
    (hvE : v ≠ E) : Relation.EqvGen Move2 (K.link v) ((move14 K h).link v) := by
  by_cases hA : v = A
  · rw [hA]; exact .rel _ _ (link_move14_A h)
  by_cases hB : v = B
  · rw [hB]; exact .rel _ _ (link_move14_B h)
  by_cases hC : v = C
  · rw [hC]; exact .rel _ _ (link_move14_C h)
  by_cases hD : v = D
  · rw [hD]; exact .rel _ _ (link_move14_D h)
  rw [link_move14_other h hA hB hC hD hvE]
  exact .refl _

/-- Under a 2-3 move, the link of every vertex is its old link, or differs from it by one
2-dimensional move. -/
theorem link_move23_eqvGen {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) (v : V) :
    Relation.EqvGen Move2 (K.link v) ((move23 K h).link v) := by
  by_cases hA : v = A
  · rw [hA]; exact .rel _ _ (link_move23_A h)
  by_cases hB : v = B
  · rw [hB]; exact .rel _ _ (link_move23_B h)
  by_cases hC : v = C
  · rw [hC]; exact .rel _ _ (link_move23_C h)
  by_cases hD : v = D
  · rw [hD]; exact .rel _ _ (link_move23_D h)
  by_cases hE : v = E
  · rw [hE]; exact .rel _ _ (link_move23_E h)
  rw [link_move23_other h hA hB hC hD hE]
  exact .refl _

/-- **The 2-3 move preserves closed combinatorial 3-manifolds**, in both directions. -/
theorem isCombManifold_move23_iff {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    IsCombManifold (move23 K h) ↔ IsCombManifold K := by
  unfold IsCombManifold
  rw [verts_move23]
  exact forall₂_congr fun v _ =>
    ⟨fun hs => hs.of_eqvGen (.symm _ _ (link_move23_eqvGen h v)),
      fun hs => hs.of_eqvGen (link_move23_eqvGen h v)⟩

/-- **The 1-4 move preserves closed combinatorial 3-manifolds**, in both directions. The new
vertex has the boundary of the tetrahedron `ABCD` as its link. -/
theorem isCombManifold_move14_iff {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    IsCombManifold (move14 K h) ↔ IsCombManifold K := by
  unfold IsCombManifold
  rw [verts_move14]
  have hE : E ∉ K.verts := fun hm => by
    obtain ⟨t, ht, hEt⟩ := Complex3.mem_verts.mp hm
    exact h.fresh t ht hEt
  constructor
  · intro H v hv
    have hvE : v ≠ E := fun h' => hE (h' ▸ hv)
    exact (H v (mem_insert_of_mem hv)).of_eqvGen (.symm _ _ (link_move14_eqvGen h hvE))
  · intro H v hv
    by_cases hvE : v = E
    · rw [hvE, link_move14_new h]
      exact isSphere2_bdry h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD
    · have hv' : v ∈ K.verts := (mem_insert.mp hv).resolve_left hvE
      exact (H v hv').of_eqvGen (link_move14_eqvGen h hvE)

/-- **The 3-2 move preserves closed combinatorial 3-manifolds**, in both directions. -/
theorem isCombManifold_move32_iff {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    IsCombManifold (move32 K h) ↔ IsCombManifold K := by
  have := isCombManifold_move23_iff (isMove23_move32 h)
  rw [move23_move32] at this
  exact this.symm

/-- **The 4-1 move preserves closed combinatorial 3-manifolds**, in both directions. -/
theorem isCombManifold_move41_iff {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    IsCombManifold (move41 K h) ↔ IsCombManifold K := by
  have := isCombManifold_move14_iff (isMove14_move41 h)
  rw [move14_move41] at this
  exact this.symm

/-- **Along every chain of the gauge-fixed amplitude's steps** (`amplitudeGF_eqvGen`), a complex
stays a closed combinatorial 3-manifold if it starts as one. -/
theorem isCombManifold_iff_of_eqvGen {x y : Complex3 V × Finset (Finset V) × (Finset V → ℕ)}
    (hxy : Relation.EqvGen GFStep x y) : IsCombManifold x.1 ↔ IsCombManifold y.1 := by
  induction hxy with
  | rel _ _ hs =>
    cases hs with
    | move23 h => exact (isCombManifold_move23_iff h).symm
    | move14 h => exact (isCombManifold_move14_iff h).symm
    | recut => rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Lightlike.PR
