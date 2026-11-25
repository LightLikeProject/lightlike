import Mathlib
import Lightlike.PL.Schoenflies.ChainCycle
import Lightlike.PL.TwoArcs
import Lightlike.PL.Theta

/-!
# The simple polygon of a trimmed cycle of chains

Row G3-188 (PL5), step 4d of the pass-4 plan.  `CycChains.exists_polygon`: a trimmed cycle of `N ≥ 4` simple
chains (`CycChains`) is the carrier of a simple polygon.  The polygon is made of two arcs: the first chain, and the
concatenation of the others (`isSimple_two_arcs`).
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

lemma getLast?_cons_append' (x z : ℝ × ℝ) (m : List (ℝ × ℝ)) : (x :: (m ++ [z])).getLast? = some z := by
  rw [List.getLast?_cons, List.getLast?_append_of_ne_nil]
  all_goals simp

lemma eq_cons_append_of {l : List (ℝ × ℝ)} {a b : ℝ × ℝ} (h1 : l.head? = some a) (h2 : l.getLast? = some b)
    (hab : a ≠ b) : ∃ m, l = a :: m ++ [b] := by
  cases l with
  | nil => simp at h1
  | cons x t =>
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rcases List.eq_nil_or_concat t with rfl | ⟨m, z, rfl⟩
    · simp at h2; exact absurd h2 hab
    · refine ⟨m, ?_⟩
      simp only [List.concat_eq_append] at h2 ⊢
      rw [getLast?_cons_append'] at h2
      have hz := Option.some.inj h2
      subst hz
      simp

/-- Concatenation of the chains `T 1, …, T (k+1)`, dropping the repeated junction points. -/
def chainJoin (T : ℕ → List (ℝ × ℝ)) : ℕ → List (ℝ × ℝ)
  | 0 => T 1
  | k + 1 => (chainJoin T k).dropLast ++ T (k + 2)

lemma chainJoin_spec {N : ℕ} {T : ℕ → List (ℝ × ℝ)} (hT : CycChains N T) :
    ∀ k, k + 2 ≤ N → IsSimpleChain (chainJoin T k) ∧ (chainJoin T k).head? = (T 1).head? ∧
      (chainJoin T k).getLast? = (T (k + 1)).getLast? ∧
      ∀ x, x ∈ chainSet (chainJoin T k) ↔ ∃ j, 1 ≤ j ∧ j ≤ k + 1 ∧ x ∈ chainSet (T j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨hT.simple 1 (by omega), rfl, rfl, fun x => ?_⟩
    simp only [chainJoin]
    constructor
    · intro hx; exact ⟨1, le_rfl, le_rfl, hx⟩
    · rintro ⟨j, h1, h2, hx⟩
      obtain rfl : j = 1 := by omega
      exact hx
  | succ k ih =>
    intro hk
    obtain ⟨hs, hh, hl, hmem⟩ := ih (by omega)
    obtain ⟨b, hb⟩ : ∃ b, (chainJoin T k).getLast? = some b := by
      cases h : (chainJoin T k).getLast? with
      | none =>
        have : chainJoin T k = [] := List.getLast?_eq_none_iff.1 h
        rw [this] at hh
        exact absurd hh.symm (hT.head 1 (by omega))
      | some b => exact ⟨b, rfl⟩
    obtain ⟨l₁, hl₁⟩ : ∃ l₁, chainJoin T k = l₁ ++ [b] := by
      rcases List.eq_nil_or_concat (chainJoin T k) with h | ⟨m, z, h⟩
      · rw [h] at hb; simp at hb
      · refine ⟨m, ?_⟩
        rw [h] at hb ⊢
        simp only [List.concat_eq_append] at hb ⊢
        simp at hb; rw [hb]
    have hbT : (T (k + 2)).head? = some b := by
      rw [← hT.link (k + 1) (by omega), ← hl]; exact hb
    obtain ⟨l₂, hl₂⟩ : ∃ l₂, T (k + 2) = b :: l₂ := by
      cases h : T (k + 2) with
      | nil => rw [h] at hbT; simp at hbT
      | cons x t => rw [h] at hbT; simp at hbT; subst hbT; exact ⟨t, rfl⟩
    have hjoin : chainJoin T (k + 1) = l₁ ++ b :: l₂ := by
      simp only [chainJoin, hl₁, List.dropLast_concat, hl₂]
    -- the intersection of the earlier chains with the next one is the junction point
    have hbmem : b ∈ chainSet (T (k + 1)) := mem_chainSet_of_getLast (by rw [← hl]; exact hb)
    have hd : chainSet (l₁ ++ [b]) ∩ chainSet (b :: l₂) = {b} := by
      rw [← hl₁, ← hl₂]
      apply Set.eq_singleton_iff_unique_mem.2
      refine ⟨⟨(hmem b).2 ⟨k + 1, by omega, le_rfl, hbmem⟩, mem_chainSet_of_head hbT⟩, fun x hx => ?_⟩
      obtain ⟨j, hj1, hj2, hxj⟩ := (hmem x).1 hx.1
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exfalso
        have := hT.disj j (k + 2) (by omega) (by omega) (by omega)
        exact Set.disjoint_left.1 this hxj hx.2
      · obtain rfl : j = k + 1 := by omega
        have := hT.adj (k + 1) (by omega) b hbT
        have hxx : x ∈ chainSet (T (k + 1)) ∩ chainSet (T (k + 1 + 1)) := ⟨hxj, hx.2⟩
        rw [this] at hxx; exact hxx
    refine ⟨?_, ?_, ?_, fun x => ?_⟩
    · rw [hjoin]
      exact isSimpleChain_append (by rw [← hl₁]; exact hs) (by rw [← hl₂]; exact hT.simple _ (by omega)) hd
    · rw [hjoin]
      have : (l₁ ++ [b]).head? = (T 1).head? := by rw [← hl₁]; exact hh
      rcases l₁ with _ | ⟨y, t⟩
      · simpa using this
      · simpa using this
    · rw [hjoin, List.getLast?_append_of_ne_nil _ (by simp), ← hl₂]
    · rw [hjoin, chainSet_append, mem_union, ← hl₁, ← hl₂]
      constructor
      · rintro (h | h)
        · obtain ⟨j, h1, h2, h3⟩ := (hmem x).1 h
          exact ⟨j, h1, by omega, h3⟩
        · exact ⟨k + 2, by omega, le_rfl, h⟩
      · rintro ⟨j, h1, h2, h3⟩
        rcases Nat.lt_or_ge j (k + 2) with hlt | hge
        · exact Or.inl ((hmem x).2 ⟨j, h1, by omega, h3⟩)
        · obtain rfl : j = k + 2 := by omega
          exact Or.inr h3

/-- **A trimmed cycle of at least four simple chains is the carrier of a simple polygon.** -/
theorem CycChains.exists_polygon {N : ℕ} (hN : 4 ≤ N) {T : ℕ → List (ℝ × ℝ)} (hT : CycChains N T) :
    ∃ (a b : ℝ × ℝ) (m₁ m₂ : List (ℝ × ℝ)),
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).IsSimple ∧
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier = {x | ∃ j, j < N ∧ x ∈ chainSet (T j)} := by
  obtain ⟨a, ha⟩ : ∃ a, (T 0).head? = some a := by
    cases h : (T 0).head? with
    | none => exact absurd h (hT.head 0 (by omega))
    | some a => exact ⟨a, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (T 1).head? = some b := by
    cases h : (T 1).head? with
    | none => exact absurd h (hT.head 1 (by omega))
    | some b => exact ⟨b, rfl⟩
  have hl0 : (T 0).getLast? = some b := by rw [hT.link 0 (by omega)]; exact hb
  obtain ⟨hQs, hQh, hQl, hQm⟩ := chainJoin_spec hT (N - 2) (by omega)
  have hQl' : (chainJoin T (N - 2)).getLast? = some a := by
    rw [hQl]
    have : N - 2 + 1 = N - 1 := by omega
    rw [this, hT.close]; exact ha
  have hQh' : (chainJoin T (N - 2)).head? = some b := by rw [hQh]; exact hb
  have hab : a ≠ b := by
    intro e
    have h1 : a ∈ chainSet (T (N - 1)) := mem_chainSet_of_getLast (by rw [hT.close]; exact ha)
    have h2 : b ∈ chainSet (T 1) := mem_chainSet_of_head hb
    rw [e] at h1
    exact Set.disjoint_left.1 (hT.disj 1 (N - 1) (by omega) (by omega) (by omega)) h2 h1
  obtain ⟨m₁, hm₁⟩ := eq_cons_append_of ha hl0 hab
  obtain ⟨m₂, hm₂⟩ := eq_cons_append_of hQh' hQl' hab.symm
  have hP : IsSimpleChain (a :: m₁ ++ [b]) := by rw [← hm₁]; exact hT.simple 0 (by omega)
  have hQ : IsSimpleChain (b :: m₂ ++ [a]) := by rw [← hm₂]; exact hQs
  have hset0 : chainSet (a :: m₁ ++ [b]) = chainSet (T 0) := by rw [← hm₁]
  have hsetQ : chainSet (b :: m₂ ++ [a]) = chainSet (chainJoin T (N - 2)) := by rw [← hm₂]
  have hPQ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b} := by
    rw [hset0, hsetQ]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx0, hxQ⟩
      obtain ⟨j, hj1, hj2, hxj⟩ := (hQm x).1 hxQ
      by_cases hj : j = 1
      · subst hj
        have := hT.adj 0 (by omega) b hb
        have hxx : x ∈ chainSet (T 0) ∩ chainSet (T (0 + 1)) := ⟨hx0, hxj⟩
        rw [this] at hxx; exact Or.inr hxx
      by_cases hj' : j = N - 1
      · subst hj'
        have := hT.adjClose a ha
        have hxx : x ∈ chainSet (T (N - 1)) ∩ chainSet (T 0) := ⟨hxj, hx0⟩
        rw [this] at hxx; exact Or.inl hxx
      · exfalso
        exact Set.disjoint_left.1 (hT.disj 0 j (by omega) (by omega) (by omega)) hx0 hxj
    · rintro (rfl | rfl)
      · exact ⟨mem_chainSet_of_head ha, mem_chainSet_of_getLast hQl'⟩
      · exact ⟨mem_chainSet_of_getLast hl0, mem_chainSet_of_head hQh'⟩
  refine ⟨a, b, m₁, m₂, isSimple_two_arcs hP hQ hPQ hab, ?_⟩
  rw [carrier_two_arcs, hset0, hsetQ]
  ext x
  simp only [mem_union, mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact ⟨0, by omega, h⟩
    · obtain ⟨j, hj1, hj2, hxj⟩ := (hQm x).1 h
      exact ⟨j, by omega, hxj⟩
  · rintro ⟨j, hj, hxj⟩
    by_cases h0 : j = 0
    · subst h0; exact Or.inl hxj
    · exact Or.inr ((hQm x).2 ⟨j, by omega, by omega, hxj⟩)

end Lightlike.PL.Schoenflies
