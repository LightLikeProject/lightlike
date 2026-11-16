import Mathlib

/-!
# Gratings and mod-2 chains in the plane

A **grating** is a rectangular grid in the plane with strictly increasing vertical and horizontal
coordinates (Alexander). A 1-chain on it is a finite set of its edges, added by symmetric difference
(chains mod 2); the **boundary** of a chain is the set of vertices at which an odd number of its edges
end. A chain whose boundary is two vertices joins them: the two lie in one component of the chain,
because a component contains an even number of vertices of odd degree.

This is the combinatorial setting of the proof that an arc does not separate the plane. The proof
follows chapter 9 of J. McCleary, *A First Course in Topology: Continuity and Dimension* (AMS,
2006), after M. H. A. Newman; the numbering used here is that of the lecture-notes version of the
chapter (`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against
the printed book. The statements and proofs are Lean's own. The part proved here is the direction
from chains to paths of Proposition 9.8 of the notes.

## Main results

* `Grating`, `Grating.Edge`, `Grating.locus`: the grid, its edges and the locus of a chain.
* `Grating.bdy`, `Grating.bdy_symmDiff`: the boundary of a chain, and its additivity mod 2.
* `Grating.reach_of_bdy`: the ends of a chain with boundary `{x, y}` are linked by the chain.
* `Grating.joinedIn_of_bdy`: a chain with boundary `{x, y}` joins the points `x` and `y` inside its
  locus.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes
  version and is not checked).
-/

open Set Finset

namespace Lightlike.PL

theorem card_symmDiff_add {α : Type*} [DecidableEq α] (S T : Finset α) :
    (symmDiff S T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have h1 := Finset.card_union_add_card_inter S T
  have h3 : (S ∩ T).card ≤ (S ∪ T).card := card_le_card inter_subset_union
  have h2 : (symmDiff S T).card = (S ∪ T).card - (S ∩ T).card := by
    rw [symmDiff_eq_sup_sdiff_inf]
    exact card_sdiff_of_subset inter_subset_union
  omega


/-- A **grating**: a grid with `n + 1` vertical lines and `m + 1` horizontal lines. -/
structure Grating where
  /-- The number of columns. -/
  n : ℕ
  /-- The number of rows. -/
  m : ℕ
  /-- The `x`-coordinates of the vertical lines. -/
  a : Fin (n + 1) → ℝ
  /-- The `y`-coordinates of the horizontal lines. -/
  b : Fin (m + 1) → ℝ
  /-- The coordinates increase. -/
  ha : StrictMono a
  /-- The coordinates increase. -/
  hb : StrictMono b

namespace Grating

variable (G : Grating)

/-- The vertices of the grating. -/
abbrev Vert := Fin (G.n + 1) × Fin (G.m + 1)

/-- The edges: horizontal ones join `(i, j)` to `(i + 1, j)`, vertical ones `(i, j)` to `(i, j + 1)`. -/
inductive Edge : Type
  | h (i : Fin G.n) (j : Fin (G.m + 1))
  | v (i : Fin (G.n + 1)) (j : Fin G.m)
  deriving DecidableEq

/-- The point of the plane at a vertex. -/
def pt (x : G.Vert) : ℝ × ℝ := (G.a x.1, G.b x.2)

/-- The two ends of an edge. -/
def ends : G.Edge → G.Vert × G.Vert
  | .h i j => ((i.castSucc, j), (i.succ, j))
  | .v i j => ((i, j.castSucc), (i, j.succ))

/-- The segment of an edge. -/
def seg (e : G.Edge) : Set (ℝ × ℝ) := segment ℝ (G.pt (G.ends e).1) (G.pt (G.ends e).2)

/-- The locus of a chain: the union of its segments. -/
def locus (c : Finset G.Edge) : Set (ℝ × ℝ) := ⋃ e ∈ c, G.seg e

/-- The number of edges of the chain that end at `x`. -/
def deg (c : Finset G.Edge) (x : G.Vert) : ℕ :=
  (c.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2).card

/-- The **boundary** of a chain: the vertices at which an odd number of its edges end. -/
def bdy (c : Finset G.Edge) : Finset G.Vert := univ.filter fun x => Odd (G.deg c x)

/-- **The boundary of a sum of chains is the sum of the boundaries** (mod 2). -/
theorem bdy_symmDiff (c₁ c₂ : Finset G.Edge) : G.bdy (symmDiff c₁ c₂) = symmDiff (G.bdy c₁) (G.bdy c₂) := by
  ext x
  have hf : (symmDiff c₁ c₂).filter (fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) =
      symmDiff (c₁.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2)
        (c₂.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_symmDiff]
    tauto
  have hi : (c₁ ∩ c₂).filter (fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) =
      (c₁.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) ∩
        (c₂.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  have hd := card_symmDiff_add (c₁.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2)
    (c₂.filter fun e => x = (G.ends e).1 ∨ x = (G.ends e).2)
  rw [← hf] at hd
  simp only [bdy, deg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff, Nat.odd_iff]
  omega

/-- The two ends of an edge are different vertices. -/
lemma ends_ne (e : G.Edge) : (G.ends e).1 ≠ (G.ends e).2 := by
  cases e with
  | h i j =>
    intro h
    exact absurd (congrArg Prod.fst h) (Fin.castSucc_lt_succ.ne)
  | v i j =>
    intro h
    exact absurd (congrArg Prod.snd h) (Fin.castSucc_lt_succ.ne)

/-- Two vertices are **linked by the chain** `c` when a path of its edges joins them. -/
def Reach (c : Finset G.Edge) : G.Vert → G.Vert → Prop :=
  Relation.ReflTransGen fun u w => ∃ e ∈ c, G.ends e = (u, w) ∨ G.ends e = (w, u)

lemma reach_symm {c : Finset G.Edge} {x y : G.Vert} (h : G.Reach c x y) : G.Reach c y x := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨e, he, h'⟩ := hs
    exact Relation.ReflTransGen.head ⟨e, he, h'.symm⟩ ih

lemma seg_subset_locus {c : Finset G.Edge} {e : G.Edge} (he : e ∈ c) : G.seg e ⊆ G.locus c := by
  intro z hz
  simp only [locus, mem_iUnion]
  exact ⟨e, he, hz⟩

/-- Linked vertices are joined inside the locus of the chain. -/
lemma joinedIn_of_reach {c : Finset G.Edge} {x y : G.Vert} (hx : G.pt x ∈ G.locus c)
    (h : G.Reach c x y) : JoinedIn (G.locus c) (G.pt x) (G.pt y) := by
  induction h with
  | refl => exact JoinedIn.refl hx
  | tail _ hs ih =>
    obtain ⟨e, he, h'⟩ := hs
    refine ih.trans (JoinedIn.of_segment_subset ?_)
    rcases h' with h' | h'
    · have := G.seg_subset_locus he
      simpa [seg, h'] using this
    · have := G.seg_subset_locus he
      simpa [seg, h', segment_symm] using this

/-- **The ends of a chain with boundary `{x, y}` are linked**, by the parity of the degrees in a
component. -/
theorem reach_of_bdy {c : Finset G.Edge} {x y : G.Vert} (h : G.bdy c = {x, y}) : G.Reach c x y := by
  classical
  by_contra hn
  set C : Finset G.Vert := univ.filter (fun v => G.Reach c x v) with hC
  have hxC : x ∈ C := by
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hyC : y ∉ C := by simpa [hC] using hn
  have hedge : ∀ e ∈ c, (G.ends e).1 ∈ C ↔ (G.ends e).2 ∈ C := by
    intro e he
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1
      exact Relation.ReflTransGen.tail h1 ⟨e, he, Or.inl rfl⟩
    · intro h2
      exact Relation.ReflTransGen.tail h2 ⟨e, he, Or.inr rfl⟩
  have hsum : ∑ v ∈ C, G.deg c v =
      ∑ e ∈ c, (C.filter fun v => v = (G.ends e).1 ∨ v = (G.ends e).2).card := by
    simp only [deg, Finset.card_filter]
    rw [Finset.sum_comm]
  have heven : ∀ e ∈ c, Even (C.filter fun v => v = (G.ends e).1 ∨ v = (G.ends e).2).card := by
    intro e he
    by_cases h1 : (G.ends e).1 ∈ C
    · have h2 := (hedge e he).1 h1
      have : (C.filter fun v => v = (G.ends e).1 ∨ v = (G.ends e).2) =
          {(G.ends e).1, (G.ends e).2} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun hv => hv.2
        · rintro (rfl | rfl)
          · exact ⟨h1, Or.inl rfl⟩
          · exact ⟨h2, Or.inr rfl⟩
      rw [this, Finset.card_pair (G.ends_ne e)]
      exact even_two
    · have h2 : (G.ends e).2 ∉ C := fun h2 => h1 ((hedge e he).2 h2)
      have : (C.filter fun v => v = (G.ends e).1 ∨ v = (G.ends e).2) = ∅ := by
        ext v
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro hv (rfl | rfl)
        · exact h1 hv
        · exact h2 hv
      rw [this]
      simp
  have hEven : Even (∑ v ∈ C, G.deg c v) := by
    rw [hsum]; exact Finset.even_sum _ heven
  have hodd : ((∑ v ∈ C, G.deg c v : ℕ) : ZMod 2) = 1 := by
    push_cast
    have : ∀ v ∈ C, ((G.deg c v : ℕ) : ZMod 2) = if v ∈ G.bdy c then 1 else 0 := by
      intro v _
      by_cases hv : Odd (G.deg c v)
      · simp only [bdy, Finset.mem_filter, Finset.mem_univ, true_and, hv, ite_true]
        exact (ZMod.natCast_eq_one_iff_odd).2 hv
      · simp only [bdy, Finset.mem_filter, Finset.mem_univ, true_and, hv, ite_false]
        exact (ZMod.natCast_eq_zero_iff_even).2 (Nat.not_odd_iff_even.1 hv)
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
    have hfil : C.filter (fun v => v ∈ G.bdy c) = {x} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_singleton, h, Finset.mem_insert]
      constructor
      · rintro ⟨hv, rfl | rfl⟩
        · rfl
        · exact absurd hv hyC
      · rintro rfl
        exact ⟨hxC, Or.inl rfl⟩
    rw [hfil]
    simp
  have h0 := (ZMod.natCast_eq_zero_iff_even).2 hEven
  rw [hodd] at h0
  exact one_ne_zero h0

/-- **A chain with boundary `{x, y}` joins `x` to `y`** (Newman; McCleary, Prop. 9.8, the easy half):
the vertices `x` and `y` lie in one component of the chain, by the parity of the degrees in a
component. -/
theorem joinedIn_of_bdy {c : Finset G.Edge} {x y : G.Vert} (h : G.bdy c = {x, y}) :
    JoinedIn (G.locus c) (G.pt x) (G.pt y) := by
  have hx : x ∈ G.bdy c := by rw [h]; simp
  have hodd : Odd (G.deg c x) := by simpa [bdy] using hx
  obtain ⟨e, he⟩ : ∃ e ∈ c, x = (G.ends e).1 ∨ x = (G.ends e).2 := by
    by_contra hcon
    push Not at hcon
    have : G.deg c x = 0 := by
      unfold deg
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun e he => by simpa using hcon e he
    rw [this] at hodd
    exact absurd hodd (by decide)
  have hpt : G.pt x ∈ G.locus c := by
    have := G.seg_subset_locus he.1
    refine this ?_
    rcases he.2 with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  exact G.joinedIn_of_reach hpt (G.reach_of_bdy h)

end Grating

end Lightlike.PL
