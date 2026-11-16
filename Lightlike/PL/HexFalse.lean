import Lightlike.PL.Hexagon

/-!
# A hexagon with three chords does not exist

The three chords of a polygonal hexagon cannot all be drawn: each chord lies inside or outside the
hexagon, two of the three lie on the same side, and any two of the three chords are neighbours
after a rotation of the labels, which does not change the inside and the outside of the hexagon.
-/

open Set Lightlike.PL.Polygon

namespace Lightlike.PL

/-- Cutting a polygon at a different vertex does not change its inside and outside. -/
theorem inside_swap (a b : ℝ × ℝ) (m₁ m₂ : List (ℝ × ℝ)) :
    (Polygon.ofList (b :: m₂ ++ a :: m₁)).inside = (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside ∧
    (Polygon.ofList (b :: m₂ ++ a :: m₁)).outside = (Polygon.ofList (a :: m₁ ++ b :: m₂)).outside := by
  have hc : (Polygon.ofList (b :: m₂ ++ a :: m₁)).carrier =
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier := by
    rw [carrier_two_arcs, carrier_two_arcs, Set.union_comm]
  have hp : ∀ x, (Polygon.ofList (b :: m₂ ++ a :: m₁)).parity x =
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).parity x := fun x => by
    rw [parity_two_arcs, parity_two_arcs, add_comm]
  constructor
  · ext x; simp only [Polygon.inside, Set.mem_ofPred_eq, hc, hp]
  · ext x; simp only [Polygon.outside, Set.mem_ofPred_eq, hc, hp]

namespace Hex

variable (H : Hex)

/-- The carrier of the hexagon is the union of its six sides. -/
lemma carrier_list : (Polygon.ofList H.list).carrier =
    ((chainSet (hexArc H.p H.h 0) ∪ chainSet (hexArc H.p H.h 1)) ∪ chainSet (hexArc H.p H.h 2)) ∪
      ((chainSet (hexArc H.p H.h 3) ∪ chainSet (hexArc H.p H.h 4)) ∪ chainSet (hexArc H.p H.h 5)) := by
  have hA0 : hexArc H.p H.h 0 = H.p 0 :: H.h 0 ++ [H.p 1] := rfl
  have hA1 : hexArc H.p H.h 1 = H.p 1 :: H.h 1 ++ [H.p 2] := rfl
  have hA2 : hexArc H.p H.h 2 = H.p 2 :: H.h 2 ++ [H.p 3] := rfl
  have hA3 : hexArc H.p H.h 3 = H.p 3 :: H.h 3 ++ [H.p 4] := rfl
  have hA4 : hexArc H.p H.h 4 = H.p 4 :: H.h 4 ++ [H.p 5] := rfl
  have hA5 : hexArc H.p H.h 5 = H.p 5 :: H.h 5 ++ [H.p 0] := rfl
  rw [hA0, hA1, hA2, hA3, hA4, hA5]
  have eL : H.list = H.p 0 :: (H.h 0 ++ H.p 1 :: H.h 1 ++ H.p 2 :: H.h 2) ++
      H.p 3 :: (H.h 3 ++ H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5) := by simp [Hex.list]
  rw [eL, carrier_two_arcs]
  have e1 : H.p 0 :: (H.h 0 ++ H.p 1 :: H.h 1 ++ H.p 2 :: H.h 2) ++ [H.p 3] =
      H.p 0 :: H.h 0 ++ H.p 1 :: H.h 1 ++ H.p 2 :: H.h 2 ++ [H.p 3] := by simp
  have e2 : H.p 3 :: (H.h 3 ++ H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5) ++ [H.p 0] =
      H.p 3 :: H.h 3 ++ H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5 ++ [H.p 0] := by simp
  rw [e1, e2, chainSet_glue3, chainSet_glue3]

/-- Each chord (with its ends removed) lies inside or outside the hexagon. -/
lemma chord_side (k : Fin 6) :
    (chainSet (hexChord H.p H.d k) \ {H.p k, H.p (k + 3)} ⊆ (Polygon.ofList H.list).inside) ∨
    (chainSet (hexChord H.p H.d k) \ {H.p k, H.p (k + 3)} ⊆ (Polygon.ofList H.list).outside) := by
  have hne : NeZero H.list.length := ⟨by simp [Hex.list]⟩
  have hpre : IsPreconnected (chainSet (hexChord H.p H.d k) \ {H.p k, H.p (k + 3)}) :=
    isPreconnected_chainSet_diff_ends' (H.simpleD k)
  have hsub : chainSet (hexChord H.p H.d k) \ {H.p k, H.p (k + 3)} ⊆
      (Polygon.ofList H.list).carrierᶜ := by
    intro z ⟨hz1, hz2⟩ hzc
    rw [H.carrier_list] at hzc
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz2
    have key : ∀ i, z ∈ chainSet (hexArc H.p H.h i) → False := fun i hi => by
      have := H.ends_HD hi hz1
      rcases this.2 with h | h
      · exact hz2.1 h
      · exact hz2.2 h
    rcases hzc with ((h | h) | h) | ((h | h) | h)
    exacts [key _ h, key _ h, key _ h, key _ h, key _ h, key _ h]
  rcases subset_outside_or_inside hpre hsub with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Rotating the labels does not change the inside and outside of the hexagon. -/
lemma rot_inside : (Polygon.ofList H.rot.list).inside = (Polygon.ofList H.list).inside ∧
    (Polygon.ofList H.rot.list).outside = (Polygon.ofList H.list).outside := by
  have e1 : H.list = H.p 0 :: H.h 0 ++ H.p 1 :: (H.h 1 ++ H.p 2 :: H.h 2 ++ H.p 3 :: H.h 3 ++
      H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5) := by simp [Hex.list]
  have e2 : H.rot.list = H.p 1 :: (H.h 1 ++ H.p 2 :: H.h 2 ++ H.p 3 :: H.h 3 ++
      H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5) ++ H.p 0 :: H.h 0 := by
    simp [Hex.list, Hex.rot]
  have := inside_swap (H.p 0) (H.p 1) (H.h 0)
    (H.h 1 ++ H.p 2 :: H.h 2 ++ H.p 3 :: H.h 3 ++ H.p 4 :: H.h 4 ++ H.p 5 :: H.h 5)
  rw [e1, e2]
  exact this

/-- The chords of the rotated hexagon are the chords of the hexagon, shifted by one. -/
lemma rot_chord (k : Fin 6) :
    chainSet (hexChord H.rot.p H.rot.d k) \ {H.rot.p k, H.rot.p (k + 3)} =
      chainSet (hexChord H.p H.d (k + 1)) \ {H.p (k + 1), H.p (k + 1 + 3)} := by
  have : hexChord H.rot.p H.rot.d k = hexChord H.p H.d (k + 1) := by
    simp [hexChord, Hex.rot, add_right_comm]
  rw [this]
  simp [Hex.rot, add_right_comm]

/-- The chord `D 3` is the chord `D 0` traversed backwards. -/
lemma chord_three : chainSet (hexChord H.p H.d 3) \ {H.p 3, H.p (3 + 3)} =
    chainSet (hexChord H.p H.d 0) \ {H.p 0, H.p (0 + 3)} := by
  have h3 : hexChord H.p H.d 3 = (hexChord H.p H.d 0).reverse := by
    have h := H.hrev 0
    rw [show (0 : Fin 6) + 3 = 3 from by decide] at h
    simp [hexChord, h]
  rw [h3, chainSet_reverse]
  have e : ((3 : Fin 6) + 3) = 0 := by decide
  have e' : ((0 : Fin 6) + 3) = 3 := by decide
  rw [e, e', Set.pair_comm]

/-- The chord `D k` without its ends. -/
def chordSet (k : Fin 6) : Set (ℝ × ℝ) := chainSet (hexChord H.p H.d k) \ {H.p k, H.p (k + 3)}

/-- The first two chords lie on the same side of the hexagon. -/
def SameSide : Prop :=
  (H.chordSet 0 ⊆ (Polygon.ofList H.list).inside ∧ H.chordSet 1 ⊆ (Polygon.ofList H.list).inside) ∨
    (H.chordSet 0 ⊆ (Polygon.ofList H.list).outside ∧
      H.chordSet 1 ⊆ (Polygon.ofList H.list).outside)

lemma false_of_sameSide (h : H.SameSide) : False := by
  apply H.pair_false
  simpa [SameSide, chordSet] using h

lemma sameSide_rot_iff : H.rot.SameSide ↔
    (H.chordSet 1 ⊆ (Polygon.ofList H.list).inside ∧ H.chordSet 2 ⊆ (Polygon.ofList H.list).inside) ∨
      (H.chordSet 1 ⊆ (Polygon.ofList H.list).outside ∧
        H.chordSet 2 ⊆ (Polygon.ofList H.list).outside) := by
  have e0 : H.rot.chordSet 0 = H.chordSet 1 := H.rot_chord 0
  have e1 : H.rot.chordSet 1 = H.chordSet 2 := H.rot_chord 1
  unfold SameSide
  rw [e0, e1, H.rot_inside.1, H.rot_inside.2]

lemma sameSide_rot_rot_iff : H.rot.rot.SameSide ↔
    (H.chordSet 2 ⊆ (Polygon.ofList H.list).inside ∧ H.chordSet 0 ⊆ (Polygon.ofList H.list).inside) ∨
      (H.chordSet 2 ⊆ (Polygon.ofList H.list).outside ∧
        H.chordSet 0 ⊆ (Polygon.ofList H.list).outside) := by
  have e0 : H.rot.rot.chordSet 0 = H.chordSet 2 := (H.rot.rot_chord 0).trans (H.rot_chord 1)
  have e1 : H.rot.rot.chordSet 1 = H.chordSet 0 :=
    ((H.rot.rot_chord 1).trans (H.rot_chord 2)).trans H.chord_three
  unfold SameSide
  rw [e0, e1, H.rot.rot_inside.1, H.rot.rot_inside.2, H.rot_inside.1, H.rot_inside.2]

end Hex

/-- **A polygonal hexagon cannot have three chords.** -/
theorem Hex.false (H : Hex) : False := by
  have s0 := H.chord_side 0
  have s1 := H.chord_side 1
  have s2 := H.chord_side 2
  have hA := H.false_of_sameSide
  have hB := H.rot.false_of_sameSide
  have hC := H.rot.rot.false_of_sameSide
  rw [H.sameSide_rot_iff] at hB
  rw [H.sameSide_rot_rot_iff] at hC
  change (H.chordSet 0 ⊆ _) ∨ (H.chordSet 0 ⊆ _) at s0
  change (H.chordSet 1 ⊆ _) ∨ (H.chordSet 1 ⊆ _) at s1
  change (H.chordSet 2 ⊆ _) ∨ (H.chordSet 2 ⊆ _) at s2
  rcases s0 with a | a <;> rcases s1 with b | b <;> rcases s2 with c | c
  · exact hA (Or.inl ⟨a, b⟩)
  · exact hA (Or.inl ⟨a, b⟩)
  · exact hC (Or.inl ⟨c, a⟩)
  · exact hB (Or.inr ⟨b, c⟩)
  · exact hB (Or.inl ⟨b, c⟩)
  · exact hC (Or.inr ⟨c, a⟩)
  · exact hA (Or.inr ⟨a, b⟩)
  · exact hA (Or.inr ⟨a, b⟩)

end Lightlike.PL
