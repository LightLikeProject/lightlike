import Lightlike.PL.Interlaced

/-!
# A hexagon with chords

A polygonal hexagon with three chords joining opposite vertices: six points `p k`, six simple
polygonal arcs `H k` from `p k` to `p (k + 1)`, and chords `D k` from `p k` to `p (k + 3)`, two
different arcs or chords meeting only in common endpoints. This is the shape of a polygonal
drawing of `K₃,₃`.
-/

open Set Lightlike.PL.Polygon

namespace Lightlike.PL

/-- The chain of the arc `H k`: the points `p k`, the interior points `h k`, the point `p (k+1)`. -/
def hexArc (p : Fin 6 → ℝ × ℝ) (h : Fin 6 → List (ℝ × ℝ)) (k : Fin 6) : List (ℝ × ℝ) :=
  p k :: h k ++ [p (k + 1)]

/-- The chain of the chord `D k`. -/
def hexChord (p : Fin 6 → ℝ × ℝ) (d : Fin 6 → List (ℝ × ℝ)) (k : Fin 6) : List (ℝ × ℝ) :=
  p k :: d k ++ [p (k + 3)]

/-- A **hexagon with three chords**. The chord `D (k + 3)` is the chord `D k` traversed backwards. -/
structure Hex where
  /-- The six corners. -/
  p : Fin 6 → ℝ × ℝ
  /-- The interior points of the six sides. -/
  h : Fin 6 → List (ℝ × ℝ)
  /-- The interior points of the chords. -/
  d : Fin 6 → List (ℝ × ℝ)
  inj : Function.Injective p
  hrev : ∀ k, d (k + 3) = (d k).reverse
  simpleH : ∀ k, IsSimpleChain (hexArc p h k)
  simpleD : ∀ k, IsSimpleChain (hexChord p d k)
  /-- Two different sides meet only in common endpoints. -/
  interHH : ∀ i j, i ≠ j →
    chainSet (hexArc p h i) ∩ chainSet (hexArc p h j) ⊆ {p i, p (i + 1)} ∩ {p j, p (j + 1)}
  /-- A side and a chord meet only in common endpoints. -/
  interHD : ∀ i j,
    chainSet (hexArc p h i) ∩ chainSet (hexChord p d j) ⊆ {p i, p (i + 1)} ∩ {p j, p (j + 3)}
  /-- Two different chords meet only in common endpoints. -/
  interDD : ∀ i j, i ≠ j → i ≠ j + 3 →
    chainSet (hexChord p d i) ∩ chainSet (hexChord p d j) ⊆ {p i, p (i + 3)} ∩ {p j, p (j + 3)}

/-- The set of three chains glued end to end. -/
lemma chainSet_glue3 (a b c d : ℝ × ℝ) (x y z : List (ℝ × ℝ)) :
    chainSet (a :: x ++ b :: y ++ c :: z ++ [d]) =
      chainSet (a :: x ++ [b]) ∪ chainSet (b :: y ++ [c]) ∪ chainSet (c :: z ++ [d]) := by
  have h1 := chainSet_append (a :: x ++ b :: y) c (z ++ [d])
  have h2 := chainSet_append (a :: x) b (y ++ [c])
  have e1 : a :: x ++ b :: y ++ c :: z ++ [d] = (a :: x ++ b :: y) ++ c :: (z ++ [d]) := by simp
  have e2 : a :: x ++ b :: y ++ [c] = (a :: x) ++ b :: (y ++ [c]) := by simp
  rw [e1, h1, e2, h2]
  simp [Set.union_assoc]

/-- Three simple chains meeting only at the points where they are glued give a simple chain. -/
lemma isSimpleChain_glue3 {a b c d : ℝ × ℝ} {x y z : List (ℝ × ℝ)}
    (h1 : IsSimpleChain (a :: x ++ [b])) (h2 : IsSimpleChain (b :: y ++ [c]))
    (h3 : IsSimpleChain (c :: z ++ [d]))
    (h12 : chainSet (a :: x ++ [b]) ∩ chainSet (b :: y ++ [c]) = {b})
    (h13 : (chainSet (a :: x ++ [b]) ∪ chainSet (b :: y ++ [c])) ∩ chainSet (c :: z ++ [d]) = {c}) :
    IsSimpleChain (a :: x ++ b :: y ++ c :: z ++ [d]) := by
  have e1 : a :: x ++ b :: y ++ c :: z ++ [d] = (a :: x ++ b :: y) ++ c :: (z ++ [d]) := by simp
  have e2 : a :: x ++ b :: y ++ [c] = (a :: x) ++ b :: (y ++ [c]) := by simp
  have hxy : IsSimpleChain (a :: x ++ b :: y ++ [c]) := by
    rw [e2]
    exact isSimpleChain_append (l₁ := a :: x) (l₂ := y ++ [c]) (b := b) h1 (by simpa using h2)
      (by simpa using h12)
  rw [e1]
  refine isSimpleChain_append hxy (by simpa using h3) ?_
  have hs : chainSet (a :: x ++ b :: y ++ [c]) = chainSet (a :: x ++ [b]) ∪ chainSet (b :: y ++ [c]) := by
    rw [e2, chainSet_append]; simp
  rw [hs]
  simpa using h13

namespace Hex

variable (H : Hex)

/-- Shifting the labels by one step. -/
def rot : Hex where
  p k := H.p (k + 1)
  h k := H.h (k + 1)
  d k := H.d (k + 1)
  inj := H.inj.comp (add_left_injective 1)
  hrev k := by
    have := H.hrev (k + 1)
    rw [show k + 1 + 3 = k + 3 + 1 by abel] at this
    exact this
  simpleH k := by
    have := H.simpleH (k + 1)
    simpa [hexArc] using this
  simpleD k := by
    have := H.simpleD (k + 1)
    simpa [hexChord, add_right_comm] using this
  interHH i j hij := by
    have := H.interHH (i + 1) (j + 1) (fun h => hij (add_right_cancel h))
    simpa [hexArc] using this
  interHD i j := by
    have := H.interHD (i + 1) (j + 1)
    simpa [hexArc, hexChord, add_right_comm] using this
  interDD i j hij hij3 := by
    have := H.interDD (i + 1) (j + 1) (fun h => hij (add_right_cancel h))
      (fun h => hij3 (by
        have : i + 1 = j + 3 + 1 := by rw [h]; abel
        exact add_right_cancel this))
    simpa [hexChord, add_right_comm] using this

lemma mem_S_head (k : Fin 6) : H.p k ∈ chainSet (hexArc H.p H.h k) := mem_chainSet_head _ _
lemma mem_S_last (k : Fin 6) : H.p (k + 1) ∈ chainSet (hexArc H.p H.h k) :=
  mem_chainSet_last (H.p k :: H.h k) _
lemma mem_T_head (k : Fin 6) : H.p k ∈ chainSet (hexChord H.p H.d k) := mem_chainSet_head _ _
lemma mem_T_last (k : Fin 6) : H.p (k + 3) ∈ chainSet (hexChord H.p H.d k) :=
  mem_chainSet_last (H.p k :: H.d k) _

-- Close a goal about a point `y` known to lie in two sets of corners.
set_option hygiene false in
local macro "ends_close" : tactic =>
  `(tactic| (rcases this with ⟨h1 | h1, h2 | h2⟩ <;>
    first
    | exact h1 | exact h2 | exact Or.inl h1 | exact Or.inr h1 | exact Or.inl h2 | exact Or.inr h2
    | exact absurd (H.inj (h1.symm.trans h2)) (by decide)
    | exact absurd (H.inj (h1.symm.trans h2)) (by decide)))

lemma ends_HH {y : ℝ × ℝ} {i j : Fin 6} (hij : i ≠ j) (h1 : y ∈ chainSet (hexArc H.p H.h i))
    (h2 : y ∈ chainSet (hexArc H.p H.h j)) :
    (y = H.p i ∨ y = H.p (i + 1)) ∧ (y = H.p j ∨ y = H.p (j + 1)) := by
  have := H.interHH i j hij ⟨h1, h2⟩
  simpa using this

lemma ends_HD {y : ℝ × ℝ} {i j : Fin 6} (h1 : y ∈ chainSet (hexArc H.p H.h i))
    (h2 : y ∈ chainSet (hexChord H.p H.d j)) :
    (y = H.p i ∨ y = H.p (i + 1)) ∧ (y = H.p j ∨ y = H.p (j + 3)) := by
  have := H.interHD i j ⟨h1, h2⟩
  simpa using this

lemma ends_DD {y : ℝ × ℝ} {i j : Fin 6} (hij : i ≠ j) (hij3 : i ≠ j + 3)
    (h1 : y ∈ chainSet (hexChord H.p H.d i)) (h2 : y ∈ chainSet (hexChord H.p H.d j)) :
    (y = H.p i ∨ y = H.p (i + 3)) ∧ (y = H.p j ∨ y = H.p (j + 3)) := by
  have := H.interDD i j hij hij3 ⟨h1, h2⟩
  simpa using this

lemma S01 : chainSet (hexArc H.p H.h 0) ∩ chainSet (hexArc H.p H.h 1) = {H.p 1} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨H.mem_S_last 0, H.mem_S_head 1⟩, fun y hy => ?_⟩
  have := H.ends_HH (by decide) hy.1 hy.2
  simp at this
  ends_close

lemma S012 : (chainSet (hexArc H.p H.h 0) ∪ chainSet (hexArc H.p H.h 1)) ∩
    chainSet (hexArc H.p H.h 2) = {H.p 2} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨Or.inr (H.mem_S_last 1), H.mem_S_head 2⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
  rcases hy1 with h | h
  · have := H.ends_HH (by decide) h hy2
    simp at this
    ends_close
  · have := H.ends_HH (by decide) h hy2
    simp at this
    ends_close

lemma S34 : chainSet (hexArc H.p H.h 3) ∩ chainSet (hexArc H.p H.h 4) = {H.p 4} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨H.mem_S_last 3, H.mem_S_head 4⟩, fun y hy => ?_⟩
  have := H.ends_HH (by decide) hy.1 hy.2
  simp at this
  ends_close

lemma S345 : (chainSet (hexArc H.p H.h 3) ∪ chainSet (hexArc H.p H.h 4)) ∩
    chainSet (hexArc H.p H.h 5) = {H.p 5} := by
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨Or.inr (H.mem_S_last 4), H.mem_S_head 5⟩, fun y ⟨hy1, hy2⟩ => ?_⟩
  rcases hy1 with h | h
  · have := H.ends_HH (by decide) h hy2
    simp at this
    ends_close
  · have := H.ends_HH (by decide) h hy2
    simp at this
    ends_close

/-- The two halves of the hexagon meet only in `p 0` and `p 3`. -/
lemma arcs_inter : ((chainSet (hexArc H.p H.h 0) ∪ chainSet (hexArc H.p H.h 1)) ∪
    chainSet (hexArc H.p H.h 2)) ∩ ((chainSet (hexArc H.p H.h 3) ∪ chainSet (hexArc H.p H.h 4)) ∪
    chainSet (hexArc H.p H.h 5)) = {H.p 3, H.p 0} := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨hy1, hy2⟩
    rcases hy1 with (h | h) | h <;> rcases hy2 with (h' | h') | h' <;>
    · have := H.ends_HH (by decide) h h'
      simp at this
      first
      | (rcases this with ⟨h1 | h1, h2 | h2⟩ <;>
          first
          | exact Or.inl h1 | exact Or.inr h1 | exact Or.inl h2 | exact Or.inr h2
          | exact absurd (H.inj (h1.symm.trans h2)) (by decide))
  · rintro y (rfl | rfl)
    · exact ⟨Or.inr (H.mem_S_last 2), Or.inl (Or.inl (H.mem_S_head 3))⟩
    · exact ⟨Or.inl (Or.inl (H.mem_S_head 0)), Or.inr (by simpa using H.mem_S_last 5)⟩

end Hex

end Lightlike.PL
