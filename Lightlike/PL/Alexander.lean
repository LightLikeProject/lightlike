import Lightlike.PL.GratingPath

/-!
# Two-chains on a grating, a cycle bounds, and Alexander's theorem

A **2-chain** of a grating is a finite set of its cells, added by symmetric difference (modulo 2).
Its boundary `bdy₂` is the set of edges that are a side of an odd number of its cells; the boundary
of a boundary is empty (`bdy_bdy₂`), and every chain without boundary is the boundary of a 2-chain
(`exists_bdy₂`: the cells that have an odd number of edges of the chain to their left in their band,
and a check of the remaining edges by the degrees of the vertices).

**Alexander's theorem** (`alexander`): if `x`, `y` are the boundary of a chain `l₁` that avoids `K` and
of a chain `l₂` that avoids `L`, the sum `l₁ + l₂` is the boundary of a 2-chain `w` up to a set `E` of
edges that avoid `K ∪ L`, and no cell of `w` meets both `K` and `L`, then `x` is joined to `y` off
`K ∪ L`. The set `E` records the outer cell of Theorem 9.10 of the notes (a cycle bounds exactly two
2-chains, a 2-chain and its complement, the complement using an outer cell): it is the outer rectangle
when `w` is a complement.

The proof follows "The Alexander Theorem" of chapter 9 of J. McCleary, *A First Course in Topology:
Continuity and Dimension* (AMS, 2006), after M. H. A. Newman; the numbering is that of the
lecture-notes version of the chapter (`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`),
not checked against the printed book. The statements and proofs are Lean's own. The grating is
assumed fine in the hypothesis on the cells of `w`, so no refinement of chains is needed.

## Main results

* `Grating.bdy₂`, `Grating.bdy₂_symmDiff`, `Grating.bdy_bdy₂`: the boundary of 2-chains.
* `Grating.mem_bdy₂_v`: when a vertical edge is in the boundary of a 2-chain.
* `Grating.exists_bdy₂`: a cycle bounds a 2-chain.
* `Grating.alexander`: Alexander's theorem on a fine grating.
-/

open Set Finset

namespace Lightlike.PL

namespace Grating

variable (G : Grating)

/-- A cell of the grating: the closed rectangle between two consecutive vertical and two consecutive
horizontal lines. -/
abbrev Cell := Fin G.n × Fin G.m

/-- The four sides of a cell. -/
def sides (c : G.Cell) : Finset G.Edge :=
  {.h c.1 c.2.castSucc, .h c.1 c.2.succ, .v c.1.castSucc c.2, .v c.1.succ c.2}

/-- The closed rectangle of a cell. -/
def cellSet (c : G.Cell) : Set (ℝ × ℝ) :=
  Set.Icc (G.a c.1.castSucc) (G.a c.1.succ) ×ˢ Set.Icc (G.b c.2.castSucc) (G.b c.2.succ)

/-- The **boundary of a 2-chain** (a finite set of cells): the edges that are a side of an odd number
of its cells. -/
def bdy₂ (w : Finset G.Cell) : Finset G.Edge :=
  Finset.univ.filter fun e => Odd (w.filter fun c => e ∈ G.sides c).card

/-- The locus of a 2-chain: the union of its closed cells. -/
def locus₂ (w : Finset G.Cell) : Set (ℝ × ℝ) := ⋃ c ∈ w, G.cellSet c

/-- The boundary of a 2-chain is additive modulo 2. -/
theorem bdy₂_symmDiff (w₁ w₂ : Finset G.Cell) :
    G.bdy₂ (symmDiff w₁ w₂) = symmDiff (G.bdy₂ w₁) (G.bdy₂ w₂) := by
  classical
  ext e
  have hf : (symmDiff w₁ w₂).filter (fun c => e ∈ G.sides c) =
      symmDiff (w₁.filter fun c => e ∈ G.sides c) (w₂.filter fun c => e ∈ G.sides c) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  have hi : (w₁ ∩ w₂).filter (fun c => e ∈ G.sides c) =
      (w₁.filter fun c => e ∈ G.sides c) ∩ (w₂.filter fun c => e ∈ G.sides c) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
  have hd := card_symmDiff_add (w₁.filter fun c => e ∈ G.sides c) (w₂.filter fun c => e ∈ G.sides c)
  rw [← hf] at hd
  simp only [bdy₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff, Nat.odd_iff]
  omega

/-- The boundary of a single cell is its four sides. -/
theorem bdy₂_singleton (c : G.Cell) : G.bdy₂ {c} = G.sides c := by
  classical
  ext e
  by_cases h : e ∈ G.sides c <;> simp [bdy₂, h, Finset.filter_singleton]

/-- An edge of the boundary of a 2-chain is a side of one of its cells. -/
theorem exists_mem_of_mem_bdy₂ {w : Finset G.Cell} {e : G.Edge} (h : e ∈ G.bdy₂ w) :
    ∃ c ∈ w, e ∈ G.sides c := by
  by_contra hc
  push Not at hc
  simp only [bdy₂, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [Finset.filter_eq_empty_iff.2 (fun c hcw => by simpa using hc c hcw)] at h
  simp at h

lemma insert_eq_symmDiff {α : Type*} [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    insert a s = symmDiff {a} s := by
  ext x; simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨hx, fun h' => h (h' ▸ hx)⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
    · exact Or.inl hx
    · exact Or.inr hx

lemma bdy_insert (e : G.Edge) {s : Finset G.Edge} (h : e ∉ s) :
    G.bdy (insert e s) = symmDiff (symmDiff {(G.ends e).1} {(G.ends e).2}) (G.bdy s) := by
  rw [insert_eq_symmDiff h, bdy_symmDiff, bdy_singleton]

/-- The four sides of a cell form a cycle. -/
theorem bdy_sides (c : G.Cell) : G.bdy (G.sides c) = ∅ := by
  classical
  obtain ⟨i, j⟩ := c
  have h1 : (Edge.h i j.castSucc : G.Edge) ∉ ({.h i j.succ, .v i.castSucc j, .v i.succ j} : Finset G.Edge) := by
    simp [Fin.castSucc_lt_succ.ne]
  have h2 : (Edge.h i j.succ : G.Edge) ∉ ({.v i.castSucc j, .v i.succ j} : Finset G.Edge) := by simp
  have h3 : (Edge.v i.castSucc j : G.Edge) ∉ ({.v i.succ j} : Finset G.Edge) := by
    simp [Fin.castSucc_lt_succ.ne]
  simp only [sides]
  rw [bdy_insert G _ h1, bdy_insert G _ h2, bdy_insert G _ h3, bdy_singleton]
  simp only [ends]
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
  tauto

/-- **The boundary of a 2-chain has no boundary.** -/
theorem bdy_bdy₂ (w : Finset G.Cell) : G.bdy (G.bdy₂ w) = ∅ := by
  classical
  induction w using Finset.induction_on with
  | empty => simp [bdy₂, bdy, deg]
  | insert c w hc ih =>
    rw [insert_eq_symmDiff hc, bdy₂_symmDiff, bdy_symmDiff, ih, bdy₂_singleton, bdy_sides]
    simp

lemma pt_mem_cellSet (c : G.Cell) {p : Fin (G.n + 1)} {q : Fin (G.m + 1)}
    (hp : p = c.1.castSucc ∨ p = c.1.succ) (hq : q = c.2.castSucc ∨ q = c.2.succ) :
    G.pt (p, q) ∈ G.cellSet c := by
  have h1 : G.a c.1.castSucc ≤ G.a c.1.succ := G.ha.monotone Fin.castSucc_lt_succ.le
  have h2 : G.b c.2.castSucc ≤ G.b c.2.succ := G.hb.monotone Fin.castSucc_lt_succ.le
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    first | exact le_rfl | exact h1 | exact h2

lemma seg_subset_cellSet {c : G.Cell} {e : G.Edge} (he : e ∈ G.sides c) : G.seg e ⊆ G.cellSet c := by
  have hconv : Convex ℝ (G.cellSet c) := (convex_Icc _ _).prod (convex_Icc _ _)
  obtain ⟨i, j⟩ := c
  simp only [sides, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp only [seg, ends] <;>
    exact hconv.segment_subset (G.pt_mem_cellSet (i, j) (by simp) (by simp))
      (G.pt_mem_cellSet (i, j) (by simp) (by simp))

lemma symmDiff_singleton_ne {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) :
    symmDiff {x} {y} = ({x, y} : Finset α) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> simp
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, h.symm⟩

lemma eq_symmDiff_sdiff {α : Type*} [DecidableEq α] {w wK : Finset α} (h : wK ⊆ w) :
    w = symmDiff wK (w \ wK) := by
  ext c
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
  constructor
  · intro hc; by_cases h' : c ∈ wK
    · exact Or.inl ⟨h', fun h'' => h''.2 h'⟩
    · exact Or.inr ⟨⟨hc, h'⟩, h'⟩
  · rintro (⟨h1, _⟩ | ⟨⟨h1, _⟩, _⟩)
    · exact h h1
    · exact h1

lemma symmDiff_identity {α : Type*} [DecidableEq α] {l₁ l₂ A B : Finset α}
    (h : symmDiff A B = symmDiff l₁ l₂) : symmDiff l₂ A = symmDiff l₁ B := by
  ext e
  have := congrArg (fun s => e ∈ s) h
  simp only [Finset.mem_symmDiff, eq_iff_iff] at this ⊢
  have key : ∀ a b A B : Prop, ((A ∧ ¬B) ∨ (B ∧ ¬A) ↔ (a ∧ ¬b) ∨ (b ∧ ¬a)) →
      ((b ∧ ¬A) ∨ (A ∧ ¬b) ↔ (a ∧ ¬B) ∨ (B ∧ ¬a)) := by
    intro a b A B h
    by_cases ha : a <;> by_cases hb : b <;> by_cases hA : A <;> by_cases hB : B <;> simp_all
  exact key _ _ _ _ this

/-- **Alexander's theorem** (chapter 9 of McCleary, the lecture-notes version, "The Alexander
Theorem"), for a grating that is already fine: if `x` and `y` are the boundary of a chain `l₁` that
avoids `K` and of a chain `l₂` that avoids `L`, the sum `l₁ + l₂` is the boundary of a 2-chain `w` up
to a set `E` of edges that avoid `K ∪ L` (the edges of the outer rectangle, when `w` is the
complement of a 2-chain), and no cell of `w` meets both `K` and `L`, then `x` and `y` are joined off
`K ∪ L`. -/
theorem alexander {K L : Set (ℝ × ℝ)} {x y : G.Vert} {l₁ l₂ : Finset G.Edge} {w : Finset G.Cell}
    (hx : G.pt x ∉ K ∪ L)
    (h₁ : G.bdy l₁ = symmDiff {x} {y}) (h₁K : ∀ e ∈ l₁, Disjoint (G.seg e) K)
    (h₂ : G.bdy l₂ = symmDiff {x} {y}) (h₂L : ∀ e ∈ l₂, Disjoint (G.seg e) L)
    {E : Finset G.Edge} (hE : ∀ e ∈ E, Disjoint (G.seg e) (K ∪ L))
    (hw : symmDiff (G.bdy₂ w) E = symmDiff l₁ l₂)
    (hfine : ∀ c ∈ w, ¬ ((G.cellSet c ∩ K).Nonempty ∧ (G.cellSet c ∩ L).Nonempty)) :
    JoinedIn (K ∪ L)ᶜ (G.pt x) (G.pt y) := by
  classical
  by_cases hxy : x = y
  · subst hxy; exact JoinedIn.refl hx
  obtain ⟨wK, hwK⟩ : ∃ wK : Finset G.Cell, wK = w.filter fun c => (G.cellSet c ∩ K).Nonempty :=
    ⟨_, rfl⟩
  have hmK : ∀ c, c ∈ wK ↔ c ∈ w ∧ (G.cellSet c ∩ K).Nonempty := by
    intro c; rw [hwK, Finset.mem_filter]
  have hsub : wK ⊆ w := fun c hc => ((hmK c).1 hc).1
  have hsplit := eq_symmDiff_sdiff hsub
  have hid : symmDiff l₂ (G.bdy₂ wK) = symmDiff l₁ (symmDiff (G.bdy₂ (w \ wK)) E) := by
    apply symmDiff_identity
    rw [← symmDiff_assoc, ← bdy₂_symmDiff, ← hsplit]
    exact hw
  have hb : G.bdy (symmDiff l₂ (G.bdy₂ wK)) = {x, y} := by
    rw [bdy_symmDiff, bdy_bdy₂, h₂]; simp [symmDiff_singleton_ne hxy]
  have hLavoid : ∀ e ∈ symmDiff l₂ (G.bdy₂ wK), Disjoint (G.seg e) L := by
    intro e he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact h₂L e h
    · obtain ⟨c, hc, hec⟩ := G.exists_mem_of_mem_bdy₂ h
      have hcw := (hmK c).1 hc
      refine Set.disjoint_left.2 fun p hp hpL => ?_
      exact hfine c hcw.1 ⟨hcw.2, ⟨p, G.seg_subset_cellSet hec hp, hpL⟩⟩
  have hKavoid : ∀ e ∈ symmDiff l₂ (G.bdy₂ wK), Disjoint (G.seg e) K := by
    intro e he
    rw [hid] at he
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · exact h₁K e h
    · rcases Finset.mem_symmDiff.1 h with ⟨h', _⟩ | ⟨h', _⟩
      · obtain ⟨c, hc, hec⟩ := G.exists_mem_of_mem_bdy₂ h'
        have hcw := Finset.mem_sdiff.1 hc
        refine Set.disjoint_left.2 fun p hp hpK => ?_
        exact hcw.2 ((hmK c).2 ⟨hcw.1, ⟨p, G.seg_subset_cellSet hec hp, hpK⟩⟩)
      · exact (hE e h').mono_right Set.subset_union_left
  refine (G.joinedIn_of_bdy hb).mono ?_
  intro p hp
  simp only [locus, Set.mem_iUnion] at hp
  obtain ⟨e, he, hpe⟩ := hp
  rintro (hpK | hpL)
  · exact Set.disjoint_left.1 (hKavoid e he) hpe hpK
  · exact Set.disjoint_left.1 (hLavoid e he) hpe hpL


lemma card_eq_one_iff_of_le {α : Type*} {s : Finset α} (h : s.card ≤ 1) : s.card = 1 ↔ s.Nonempty := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by simp⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb => Finset.card_le_one.1 h b hb a ha⟩⟩

/-- A vertical edge is in the boundary of a 2-chain exactly when one of the two cells beside it is in
the chain and the other is not (a missing cell, at the border, counts as not in the chain). -/
theorem mem_bdy₂_v (w : Finset G.Cell) (a : Fin (G.n + 1)) (b : Fin G.m) :
    Edge.v a b ∈ G.bdy₂ w ↔
      Xor (∃ i : Fin G.n, i.succ = a ∧ (i, b) ∈ w) (∃ i : Fin G.n, i.castSucc = a ∧ (i, b) ∈ w) := by
  classical
  have hset : w.filter (fun c => Edge.v a b ∈ G.sides c) =
      w.filter (fun c => c.2 = b ∧ c.1.succ = a) ∪ w.filter (fun c => c.2 = b ∧ c.1.castSucc = a) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_union, sides, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, false_or, Edge.v.injEq]
    constructor
    · rintro ⟨hw, h1 | h1⟩
      · exact Or.inr ⟨hw, h1.2.symm, h1.1.symm⟩
      · exact Or.inl ⟨hw, h1.2.symm, h1.1.symm⟩
    · rintro (⟨hw, h1, h2⟩ | ⟨hw, h1, h2⟩)
      · exact ⟨hw, Or.inr ⟨h2.symm, h1.symm⟩⟩
      · exact ⟨hw, Or.inl ⟨h2.symm, h1.symm⟩⟩
  have hdisj : Disjoint (w.filter (fun c => c.2 = b ∧ c.1.succ = a))
      (w.filter (fun c => c.2 = b ∧ c.1.castSucc = a)) := by
    rw [Finset.disjoint_left]
    intro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact Fin.castSucc_lt_succ.ne (h2.2.2.trans h1.2.2.symm)
  have hle1 : (w.filter (fun c => c.2 = b ∧ c.1.succ = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ h1 ⟨i', j'⟩ h2
    simp only [Finset.mem_filter] at h1 h2
    exact Prod.ext (Fin.succ_injective _ (h1.2.2.trans h2.2.2.symm)) (h1.2.1.trans h2.2.1.symm)
  have hle2 : (w.filter (fun c => c.2 = b ∧ c.1.castSucc = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ h1 ⟨i', j'⟩ h2
    simp only [Finset.mem_filter] at h1 h2
    exact Prod.ext (Fin.castSucc_injective _ (h1.2.2.trans h2.2.2.symm)) (h1.2.1.trans h2.2.1.symm)
  have e1 := card_eq_one_iff_of_le hle1
  have e2 := card_eq_one_iff_of_le hle2
  have hP : (w.filter (fun c => c.2 = b ∧ c.1.succ = a)).Nonempty ↔
      ∃ i : Fin G.n, i.succ = a ∧ (i, b) ∈ w := by
    constructor
    · rintro ⟨⟨i, j⟩, h⟩
      simp only [Finset.mem_filter] at h
      exact ⟨i, h.2.2, by rw [← h.2.1]; exact h.1⟩
    · rintro ⟨i, hi, hw⟩
      exact ⟨(i, b), by simp [hi, hw]⟩
  have hQ : (w.filter (fun c => c.2 = b ∧ c.1.castSucc = a)).Nonempty ↔
      ∃ i : Fin G.n, i.castSucc = a ∧ (i, b) ∈ w := by
    constructor
    · rintro ⟨⟨i, j⟩, h⟩
      simp only [Finset.mem_filter] at h
      exact ⟨i, h.2.2, by rw [← h.2.1]; exact h.1⟩
    · rintro ⟨i, hi, hw⟩
      exact ⟨(i, b), by simp [hi, hw]⟩
  simp only [bdy₂, Finset.mem_filter, Finset.mem_univ, true_and, hset,
    Finset.card_union_of_disjoint hdisj, Nat.odd_iff]
  rw [← hP, ← hQ, ← e1, ← e2]
  generalize (w.filter (fun c => c.2 = b ∧ c.1.succ = a)).card = n1 at *
  generalize (w.filter (fun c => c.2 = b ∧ c.1.castSucc = a)).card = n2 at *
  simp only [Xor]
  omega

open Classical in
/-- The number of vertical edges of `c` in the band `b`, in the columns up to `k`. -/
noncomputable def Tc (c : Finset G.Edge) (b : Fin G.m) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (G.n + 1) => i.val ≤ k ∧ Edge.v i b ∈ c).card

open Classical in
/-- The 2-chain whose cells have an odd number of edges of `c` to their left, in their band. -/
noncomputable def cycleCells (c : Finset G.Edge) : Finset G.Cell :=
  Finset.univ.filter fun p => Odd (G.Tc c p.2 p.1.val)

lemma mem_cycleCells (c : Finset G.Edge) (p : G.Cell) :
    p ∈ G.cycleCells c ↔ Odd (G.Tc c p.2 p.1.val) := by
  classical
  simp [cycleCells]

lemma Tc_zero (c : Finset G.Edge) (b : Fin G.m) :
    G.Tc c b 0 = if Edge.v (0 : Fin (G.n + 1)) b ∈ c then 1 else 0 := by
  classical
  simp only [Tc, Finset.card_filter]
  rw [Finset.sum_eq_single (0 : Fin (G.n + 1))]
  · simp
  · intro i _ hi
    have : ¬ i.val ≤ 0 := fun h => hi (Fin.ext (by simpa using h))
    simp [this]
  · simp

lemma Tc_succ (c : Finset G.Edge) (b : Fin G.m) (k : ℕ) (hk : k + 1 < G.n + 1) :
    G.Tc c b (k + 1) = G.Tc c b k + if Edge.v (⟨k + 1, hk⟩ : Fin (G.n + 1)) b ∈ c then 1 else 0 := by
  classical
  simp only [Tc, Finset.card_filter]
  have : ∀ i : Fin (G.n + 1), (if i.val ≤ k + 1 ∧ Edge.v i b ∈ c then 1 else 0) =
      (if i.val ≤ k ∧ Edge.v i b ∈ c then 1 else 0) +
        (if i = (⟨k + 1, hk⟩ : Fin (G.n + 1)) then (if Edge.v i b ∈ c then 1 else 0) else 0) := by
    intro i
    by_cases h1 : i.val ≤ k
    · have : i ≠ (⟨k + 1, hk⟩ : Fin (G.n + 1)) := fun h => by simp [h] at h1
      simp [h1, this, show i.val ≤ k + 1 by omega]
    · by_cases h2 : i = (⟨k + 1, hk⟩ : Fin (G.n + 1))
      · subst h2; simp
      · have : ¬ i.val ≤ k + 1 := fun h => h2 (Fin.ext (by simp; omega))
        simp [h1, h2, this]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- The 2-chain `cycleCells c` has the same vertical edges as `c`, except possibly in the last
column. -/
theorem v_mem_bdy₂_cycleCells (c : Finset G.Edge) (a : Fin (G.n + 1)) (b : Fin G.m)
    (ha : a.val < G.n) : Edge.v a b ∈ G.bdy₂ (G.cycleCells c) ↔ Edge.v a b ∈ c := by
  classical
  rw [mem_bdy₂_v]
  have hQ : (∃ i : Fin G.n, i.castSucc = a ∧ (i, b) ∈ G.cycleCells c) ↔ Odd (G.Tc c b a.val) := by
    constructor
    · rintro ⟨i, hi, hw⟩
      rw [mem_cycleCells] at hw
      have : i.val = a.val := by rw [← hi]; simp
      simpa [this] using hw
    · intro h
      exact ⟨⟨a.val, ha⟩, Fin.ext rfl, by rw [mem_cycleCells]; exact h⟩
  rcases Nat.eq_zero_or_pos a.val with h0 | hpos
  · have hP : ¬ ∃ i : Fin G.n, i.succ = a ∧ (i, b) ∈ G.cycleCells c := by
      rintro ⟨i, hi, _⟩
      have : (i.succ).val = a.val := by rw [hi]
      simp at this; omega
    have ha0 : a = 0 := Fin.ext (by simpa using h0)
    subst ha0
    rw [hQ]
    simp only [Fin.val_zero, Tc_zero, Xor, hP, false_and, false_or]
    by_cases h : Edge.v (0 : Fin (G.n + 1)) b ∈ c <;> simp [h]
  · obtain ⟨k, hk⟩ : ∃ k, a.val = k + 1 := ⟨a.val - 1, by omega⟩
    have hP : (∃ i : Fin G.n, i.succ = a ∧ (i, b) ∈ G.cycleCells c) ↔ Odd (G.Tc c b k) := by
      constructor
      · rintro ⟨i, hi, hw⟩
        rw [mem_cycleCells] at hw
        have : i.val = k := by
          have : (i.succ).val = a.val := by rw [hi]
          simp at this; omega
        simpa [this] using hw
      · intro h
        exact ⟨⟨k, by omega⟩, Fin.ext (by simp [hk]), by rw [mem_cycleCells]; exact h⟩
    rw [hQ, hP, hk, Tc_succ G c b k (by omega)]
    have haeq : a = (⟨k + 1, by omega⟩ : Fin (G.n + 1)) := Fin.ext hk
    rw [← haeq]
    simp only [Xor]
    generalize G.Tc c b k = t
    by_cases h : Edge.v a b ∈ c <;> simp [h, Nat.odd_add_one]
    exact (Nat.even_or_odd t).symm

/-- If a chain without boundary has at a vertex only one possible edge, that edge is not in it. -/
lemma not_mem_of_bdy_empty {c' : Finset G.Edge} (hb : G.bdy c' = ∅) {x : G.Vert} {e₀ : G.Edge}
    (hx0 : x = (G.ends e₀).1 ∨ x = (G.ends e₀).2)
    (hall : ∀ e ∈ c', (x = (G.ends e).1 ∨ x = (G.ends e).2) → e = e₀) : e₀ ∉ c' := by
  classical
  intro h0
  have hf : c'.filter (fun e => x = (G.ends e).1 ∨ x = (G.ends e).2) = {e₀} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hx'⟩; exact hall e he hx'
    · rintro rfl; exact ⟨h0, hx0⟩
  have hodd : Odd (G.deg c' x) := by
    unfold deg; rw [hf]; simp
  have : x ∈ G.bdy c' := by
    simp only [bdy, Finset.mem_filter, Finset.mem_univ, true_and]; exact hodd
  rw [hb] at this
  simp at this

/-- A chain without boundary whose vertical edges, except those of the last column, are absent has
no edges. -/
theorem eq_empty_of_vertical {c' : Finset G.Edge} (hb : G.bdy c' = ∅)
    (hv : ∀ (a : Fin (G.n + 1)) (b : Fin G.m), a.val < G.n → Edge.v a b ∉ c') : c' = ∅ := by
  classical
  -- no horizontal edges
  have hh : ∀ k, ∀ a : Fin G.n, a.val = k → ∀ j, Edge.h a j ∉ c' := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro a hak j
      refine G.not_mem_of_bdy_empty hb (x := (a.castSucc, j)) (e₀ := Edge.h a j) (Or.inl rfl) ?_
      intro e he hx
      cases e with
      | h a' j' =>
        simp only [ends, Prod.ext_iff] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := Fin.castSucc_injective _ h1
          subst this; subst h2; rfl
        · exfalso
          have hlt : a'.val < k := by
            have := congrArg Fin.val h1; simp at this; omega
          exact ih a'.val hlt a' rfl j' he
      | v a' j' =>
        exfalso
        simp only [ends, Prod.ext_iff] at hx
        have h1 : a.castSucc = a' := by rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
        have hlt : a'.val < G.n := by
          have := congrArg Fin.val h1; simp at this; omega
        exact hv a' j' hlt he
  -- no vertical edges in the last column
  have hl : ∀ k, ∀ b : Fin G.m, b.val = k → ∀ a : Fin (G.n + 1), a.val = G.n → Edge.v a b ∉ c' := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro b hbk a han
      refine G.not_mem_of_bdy_empty hb (x := (a, b.castSucc)) (e₀ := Edge.v a b) (Or.inl rfl) ?_
      intro e he hx
      cases e with
      | h a' j' =>
        exact absurd he (hh a'.val a' rfl j')
      | v a' j' =>
        simp only [ends, Prod.ext_iff] at hx
        rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; have := Fin.castSucc_injective _ h2; subst this; rfl
        · exfalso
          have hlt : j'.val < k := by
            have := congrArg Fin.val h2; simp at this; omega
          have h1' : a' = a := h1.symm ▸ rfl
          exact ih j'.val hlt j' rfl a' (by rw [h1']; exact han) he
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  cases e with
  | h a j => exact hh a.val a rfl j he
  | v a b =>
    by_cases ha : a.val < G.n
    · exact hv a b ha he
    · exact hl b.val b rfl a (by have := a.2; omega) he

/-- **A cycle bounds** (in a grating, with chains modulo 2): a chain without boundary is the
boundary of a 2-chain. -/
theorem exists_bdy₂ {c : Finset G.Edge} (hb : G.bdy c = ∅) : ∃ w : Finset G.Cell, G.bdy₂ w = c := by
  classical
  refine ⟨G.cycleCells c, ?_⟩
  have h := G.eq_empty_of_vertical (c' := symmDiff c (G.bdy₂ (G.cycleCells c)))
    (by rw [bdy_symmDiff, hb, bdy_bdy₂]; simp)
    (by
      intro a b ha hmem
      have := G.v_mem_bdy₂_cycleCells c a b ha
      rw [Finset.mem_symmDiff] at hmem
      tauto)
  have := symmDiff_eq_bot.1 (by simpa using h : symmDiff c (G.bdy₂ (G.cycleCells c)) = ⊥)
  exact this.symm

end Grating

end Lightlike.PL
