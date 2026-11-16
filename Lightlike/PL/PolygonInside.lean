import Lightlike.PL.PolygonJordan

/-!
# The inside of a simple polygon

The bounded component of the complement of a simple closed polygon, defined as the points off the
polygon whose ray parity is odd (the class the Jordan theorem `polygon_jordan` produces), and
shown to be the only bounded one: any decomposition of the complement into two nonempty
preconnected sets, one bounded and one unbounded, has the inside as its bounded part.

## Main results

* `Polygon.inside`, `Polygon.outside`: the odd and the even parity class off the polygon.
* `Polygon.isBounded_inside`, `Polygon.not_isBounded_outside`.
* `Polygon.eq_inside_of_isBounded`: the inside is the bounded part of any such decomposition.
-/

open Set Filter Topology Metric

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- The **inside** of a polygon: the points off the polygon whose ray parity is odd. -/
def inside (p : Polygon n) : Set (ℝ × ℝ) := {y | y ∉ p.carrier ∧ p.parity y = 1}

/-- The **outside** of a polygon: the points off the polygon whose ray parity is even. -/
def outside (p : Polygon n) : Set (ℝ × ℝ) := {y | y ∉ p.carrier ∧ p.parity y = 0}

lemma isOpen_inside (p : Polygon n) : IsOpen p.inside :=
  isOpen_class (isClosed_carrier p) (fun _ hx => eventually_parity_eq p hx) 1

lemma isOpen_outside (p : Polygon n) : IsOpen p.outside :=
  isOpen_class (isClosed_carrier p) (fun _ hx => eventually_parity_eq p hx) 0

lemma disjoint_outside_inside (p : Polygon n) : Disjoint p.outside p.inside :=
  Set.disjoint_left.2 fun _ h1 h2 => by
    have := h1.2.symm.trans h2.2
    revert this; decide

lemma compl_carrier_eq (p : Polygon n) : p.carrierᶜ = p.outside ∪ p.inside := by
  ext y
  constructor
  · intro hy
    have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases h01 (p.parity y) with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h

lemma isPreconnected_inside [NeZero n] (hs : p.IsSimple) : IsPreconnected p.inside :=
  isPreconnected_parity_class hs 1

lemma isPreconnected_outside [NeZero n] (hs : p.IsSimple) : IsPreconnected p.outside :=
  isPreconnected_parity_class hs 0

lemma inside_nonempty [NeZero n] (hs : p.IsSimple) : p.inside.Nonempty := by
  obtain ⟨y₁, y₂, h1, h2, hne⟩ := exists_parity_pair hs
  have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h01 (p.parity y₁) with h | h
  · refine ⟨y₂, h2, ?_⟩
    rcases h01 (p.parity y₂) with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · exact h'
  · exact ⟨y₁, h1, h⟩

lemma outside_nonempty [NeZero n] (hs : p.IsSimple) : p.outside.Nonempty := by
  obtain ⟨y₁, y₂, h1, h2, hne⟩ := exists_parity_pair hs
  have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h01 (p.parity y₁) with h | h
  · exact ⟨y₁, h1, h⟩
  · refine ⟨y₂, h2, ?_⟩
    rcases h01 (p.parity y₂) with h' | h'
    · exact h'
    · exact absurd (h.trans h'.symm) hne

/-- **The inside of a polygon is bounded.** -/
theorem isBounded_inside (p : Polygon n) : Bornology.IsBounded p.inside := by
  obtain ⟨M, hM0, hM⟩ := exists_bound p
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := M)).subset fun y hy => ?_
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  have := parity_eq_zero_far hM0 hM (not_le.1 h)
  exact absurd (hy.2.symm.trans this) (by decide)

/-- **The outside of a polygon is unbounded.** -/
theorem not_isBounded_outside (p : Polygon n) : ¬ Bornology.IsBounded p.outside := by
  obtain ⟨M, hM0, hM⟩ := exists_bound p
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℝ × ℝ)
  have hH : 0 < max M R + 1 := by have := le_max_left M R; linarith
  have hn : ‖((0 : ℝ), max M R + 1)‖ = max M R + 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg hH.le]; exact max_eq_right hH.le
  have hy : p.parity (0, max M R + 1) = 0 :=
    parity_eq_zero_far hM0 hM (by rw [hn]; linarith [le_max_left M R])
  have hnot : ((0 : ℝ), max M R + 1) ∉ p.carrier := fun hc => by
    have := carrier_subset_closedBall hM hc
    rw [mem_closedBall, dist_zero_right, hn] at this
    linarith [le_max_left M R]
  have := hR ⟨hnot, hy⟩
  rw [mem_closedBall, dist_zero_right, hn] at this
  linarith [le_max_right M R]

/-- **The inside is the bounded part of any Jordan decomposition.** If the complement of a simple
polygon is the union of two preconnected sets `A` and `B`, with `A` unbounded, then `B` is the
inside. (Disjointness, nonemptiness and the boundedness of `B` are not needed.) -/
theorem eq_inside_of_isBounded [NeZero n] (hs : p.IsSimple) {A B : Set (ℝ × ℝ)}
    (hU : p.carrierᶜ = A ∪ B) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAb : ¬ Bornology.IsBounded A) : B = p.inside := by
  have hcov := p.compl_carrier_eq
  have hA' : A ⊆ p.outside ∨ A ⊆ p.inside :=
    hA.subset_or_subset (isOpen_outside p) (isOpen_inside p) (disjoint_outside_inside p)
      (by rw [← hcov, hU]; exact subset_union_left)
  have hB' : B ⊆ p.outside ∨ B ⊆ p.inside :=
    hB.subset_or_subset (isOpen_outside p) (isOpen_inside p) (disjoint_outside_inside p)
      (by rw [← hcov, hU]; exact subset_union_right)
  have key : ∀ y, y ∈ p.outside ∨ y ∈ p.inside → y ∈ A ∨ y ∈ B := fun y hy => by
    have : y ∈ A ∪ B := by rw [← hU, hcov]; exact hy
    exact this
  have hdis := disjoint_outside_inside p
  rcases hA' with hA' | hA' <;> rcases hB' with hB' | hB'
  · obtain ⟨y, hy⟩ := inside_nonempty hs
    rcases key y (Or.inr hy) with h | h
    · exact (disjoint_left.1 hdis (hA' h) hy).elim
    · exact (disjoint_left.1 hdis (hB' h) hy).elim
  · refine Subset.antisymm hB' fun y hy => ?_
    rcases key y (Or.inr hy) with h | h
    · exact (disjoint_left.1 hdis (hA' h) hy).elim
    · exact h
  · exact absurd ((isBounded_inside p).subset hA') hAb
  · obtain ⟨y, hy⟩ := outside_nonempty hs
    rcases key y (Or.inl hy) with h | h
    · exact (disjoint_left.1 hdis hy (hA' h)).elim
    · exact (disjoint_left.1 hdis hy (hB' h)).elim

/-- **Non-vacuity.** The theorem applies to the sets that `polygon_jordan` returns (whatever they
are): the bounded one is the inside. -/
example [NeZero n] (hs : p.IsSimple) : ∃ A B : Set (ℝ × ℝ), p.carrierᶜ = A ∪ B ∧
    IsPreconnected A ∧ IsPreconnected B ∧ ¬ Bornology.IsBounded A ∧ B = p.inside := by
  obtain ⟨A, B, hU, -, -, -, hA, hB, -, -, -, hAb⟩ := polygon_jordan hs
  exact ⟨A, B, hU, hA, hB, hAb, eq_inside_of_isBounded hs hU hA hB hAb⟩

end Polygon
end Lightlike.PL
