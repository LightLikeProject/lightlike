import Lightlike.PL.TwoArcs

/-!
# The carrier of the polygon on a list

The union of the edges of the polygon on a list `a :: l ++ [z]` is the set of the chain together with
the closing segment from `z` back to `a`.
-/

open Set

namespace Lightlike.PL

/-- A point is on the chain when it is on one of its segments (a chain with at least two points). -/
lemma mem_chainSet_iff {a b : ℝ × ℝ} {l : List (ℝ × ℝ)} {x : ℝ × ℝ} :
    x ∈ chainSet (a :: b :: l) ↔ ∃ k, k + 1 < (a :: b :: l).length ∧ x ∈ cseg (a :: b :: l) k := by
  induction l generalizing a b with
  | nil =>
    simp only [chainSet_pair]
    constructor
    · intro h; exact ⟨0, by simp, by simpa [cseg] using h⟩
    · rintro ⟨k, hk, hx⟩
      have : k = 0 := by simp at hk; omega
      subst this
      simpa [cseg] using hx
  | cons c l ih =>
    simp only [chainSet]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simp, by simpa [cseg] using h⟩
      · obtain ⟨k, hk, hx⟩ := (ih (a := b) (b := c)).1 h
        exact ⟨k + 1, by simpa using hk, by rwa [cseg_cons_succ]⟩
    · rintro ⟨k, hk, hx⟩
      cases k with
      | zero => exact Or.inl (by simpa [cseg] using hx)
      | succ k =>
        rw [cseg_cons_succ] at hx
        exact Or.inr ((ih (a := b) (b := c)).2 ⟨k, by simpa using hk, hx⟩)

lemma mem_chainSet_iff' {c : List (ℝ × ℝ)} (h : 2 ≤ c.length) {x : ℝ × ℝ} :
    x ∈ chainSet c ↔ ∃ k, k + 1 < c.length ∧ x ∈ cseg c k := by
  match c, h with
  | a :: b :: l, _ => exact mem_chainSet_iff

/-- **The carrier of the polygon on a list.** -/
theorem carrier_ofList {a z : ℝ × ℝ} {l : List (ℝ × ℝ)} :
    (Polygon.ofList (a :: l ++ [z])).carrier = chainSet (a :: l ++ [z]) ∪ segment ℝ z a := by
  set c : List (ℝ × ℝ) := a :: l ++ [z] with hc
  set n := c.length with hn
  have h2 : 2 ≤ n := by simp [hn, hc]
  have : NeZero n := ⟨by omega⟩
  have hc0 : c.getD 0 0 = a := by simp [hc]
  have hcl' : c.getD (n - 1) 0 = z := by
    have hn1 : n - 1 = (a :: l).length := by simp [hn, hc]
    rw [hn1, hc, List.getD_append_right _ _ _ _ le_rfl]
    simp
  have hcycL : ∀ i, i < n → (Polygon.ofList c).cyc i = c.getD i 0 := fun i hi => by
    rw [Polygon.ofList_cyc c 0, Nat.mod_eq_of_lt hi]
  have hcycN : (Polygon.ofList c).cyc n = a := by
    rw [Polygon.ofList_cyc c 0, Nat.mod_self, hc0]
  ext x
  rw [Polygon.mem_carrier_iff h2, Set.mem_union, mem_chainSet_iff' h2]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases Nat.lt_or_ge (k + 1) n with h | h
    · left
      refine ⟨k, h, ?_⟩
      rw [hcycL k hk, hcycL (k + 1) h] at hx
      exact hx
    · right
      have hk' : k = n - 1 := by omega
      subst hk'
      rw [hcycL (n - 1) hk, show n - 1 + 1 = n by omega, hcycN, hcl'] at hx
      exact hx
  · rintro (⟨k, hk, hx⟩ | hx)
    · exact ⟨k, by omega, by rw [hcycL k (by omega), hcycL (k + 1) hk]; exact hx⟩
    · refine ⟨n - 1, by omega, ?_⟩
      rw [hcycL (n - 1) (by omega), show n - 1 + 1 = n by omega, hcycN, hcl']
      exact hx

end Lightlike.PL
