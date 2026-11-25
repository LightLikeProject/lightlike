import Mathlib
import Lightlike.PL.Schoenflies.ChainHit

/-!
# Fixing the junctions of a cycle of simple chains

Row G3-188 (PL5), step 4c of the pass-4 plan.  A cyclic family of simple chains `S 0, …, S (N-1)` (each ending
where the next one starts, `S (N-1)` ending where `S 0` starts), non-adjacent members disjoint, is replaced by
sub-chains `T j` whose consecutive members meet exactly in the common endpoint (`exists_cyc_of_raw`).  Each
junction is fixed by `fix_junction`, the junctions `0|1, 1|2, …` in order and the closing junction last.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- A cyclic family of simple chains, each ending where the next begins, non-adjacent ones disjoint. -/
structure RawChains (N : ℕ) (S : ℕ → List (ℝ × ℝ)) : Prop where
  simple : ∀ j < N, IsSimpleChain (S j)
  head : ∀ j < N, (S j).head? ≠ none
  link : ∀ j, j + 1 < N → (S j).getLast? = (S (j + 1)).head?
  close : (S (N - 1)).getLast? = (S 0).head?
  disj : ∀ j k, j + 2 ≤ k → k < N → ¬ (j = 0 ∧ k = N - 1) → Disjoint (chainSet (S j)) (chainSet (S k))

/-- A cyclic family of simple chains whose consecutive members meet exactly at the common endpoint. -/
structure CycChains (N : ℕ) (T : ℕ → List (ℝ × ℝ)) : Prop where
  simple : ∀ j < N, IsSimpleChain (T j)
  head : ∀ j < N, (T j).head? ≠ none
  link : ∀ j, j + 1 < N → (T j).getLast? = (T (j + 1)).head?
  close : (T (N - 1)).getLast? = (T 0).head?
  adj : ∀ j, j + 1 < N → ∀ h, (T (j + 1)).head? = some h → chainSet (T j) ∩ chainSet (T (j + 1)) = {h}
  adjClose : ∀ h, (T 0).head? = some h → chainSet (T (N - 1)) ∩ chainSet (T 0) = {h}
  disj : ∀ j k, j + 2 ≤ k → k < N → ¬ (j = 0 ∧ k = N - 1) → Disjoint (chainSet (T j)) (chainSet (T k))

/-- The invariant of the left-to-right sweep after the junctions `0|1, …, (k-1)|k` have been fixed. -/
structure LinInv (N k : ℕ) (S T : ℕ → List (ℝ × ℝ)) : Prop where
  simple : ∀ j < N, IsSimpleChain (T j)
  sub : ∀ j < N, chainSet (T j) ⊆ chainSet (S j)
  head : ∀ j < N, (T j).head? ≠ none
  link : ∀ j, j + 1 < N → (T j).getLast? = (T (j + 1)).head?
  first : (T 0).head? = (S 0).head?
  lastN : (T (N - 1)).getLast? = (S (N - 1)).getLast?
  adj : ∀ j, j < k → j + 1 < N → ∀ h, (T (j + 1)).head? = some h →
    chainSet (T j) ∩ chainSet (T (j + 1)) = {h}

lemma LinInv.init {N : ℕ} {S : ℕ → List (ℝ × ℝ)} (hS : RawChains N S) : LinInv N 0 S S where
  simple := hS.simple
  sub := fun _ _ => subset_rfl
  head := hS.head
  link := hS.link
  first := rfl
  lastN := rfl
  adj := fun j hj => absurd hj (Nat.not_lt_zero _)

lemma LinInv.step {N k : ℕ} {S T : ℕ → List (ℝ × ℝ)} (hT : LinInv N k S T) (hk : k + 1 < N) :
    ∃ T', LinInv N (k + 1) S T' := by
  have hkN : k < N := by omega
  obtain ⟨a, ha⟩ : ∃ a, (T (k + 1)).head? = some a := by
    cases h : (T (k + 1)).head? with
    | none => exact absurd h (hT.head _ hk)
    | some a => exact ⟨a, rfl⟩
  have hLe : (T k).getLast? = some a := by rw [hT.link k hk]; exact ha
  obtain ⟨L', R', h, hL', hR', hLh, hLl, hRh, hRl, hLs, hRs, hint⟩ :=
    fix_junction (hT.simple k hkN) (hT.simple (k + 1) hk) hLe ha
  set T' : ℕ → List (ℝ × ℝ) := Function.update (Function.update T k L') (k + 1) R' with hT'
  have e1 : T' k = L' := by
    simp [hT']
  have e2 : T' (k + 1) = R' := by simp [hT']
  have e3 : ∀ j, j ≠ k → j ≠ k + 1 → T' j = T j := by
    intro j h1 h2
    simp [hT', Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨T', ?_⟩
  have hsimple : ∀ j < N, IsSimpleChain (T' j) := by
    intro j hj
    by_cases h1 : j = k
    · subst h1; rw [e1]; exact hL'
    by_cases h2 : j = k + 1
    · subst h2; rw [e2]; exact hR'
    rw [e3 j h1 h2]; exact hT.simple j hj
  have hsub : ∀ j < N, chainSet (T' j) ⊆ chainSet (S j) := by
    intro j hj
    by_cases h1 : j = k
    · subst h1; rw [e1]; exact hLs.trans (hT.sub _ hj)
    by_cases h2 : j = k + 1
    · subst h2; rw [e2]; exact hRs.trans (hT.sub _ hj)
    rw [e3 j h1 h2]; exact hT.sub j hj
  have hhead : ∀ j < N, (T' j).head? ≠ none := by
    intro j hj
    by_cases h1 : j = k
    · subst h1; rw [e1, hLh]; exact hT.head _ hj
    by_cases h2 : j = k + 1
    · subst h2; rw [e2, hRh]; simp
    rw [e3 j h1 h2]; exact hT.head j hj
  -- heads and lasts of the modified chains
  have hhd : ∀ j, j < N → (T' j).head? = (T j).head? ∨ j = k + 1 := by
    intro j hj
    by_cases h1 : j = k
    · subst h1; left; rw [e1, hLh]
    by_cases h2 : j = k + 1
    · right; exact h2
    left; rw [e3 j h1 h2]
  have hlst : ∀ j, j < N → (T' j).getLast? = (T j).getLast? ∨ j = k := by
    intro j hj
    by_cases h1 : j = k
    · right; exact h1
    by_cases h2 : j = k + 1
    · subst h2; left; rw [e2, hRl]
    left; rw [e3 j h1 h2]
  have hlink : ∀ j, j + 1 < N → (T' j).getLast? = (T' (j + 1)).head? := by
    intro j hj
    by_cases h1 : j = k
    · subst h1; rw [e1, e2, hLl, hRh]
    by_cases h2 : j = k + 1
    · subst h2
      rw [e2, hRl]
      have : (T' (k + 1 + 1)).head? = (T (k + 1 + 1)).head? := by
        rw [e3 _ (by omega) (by omega)]
      rw [this]; exact hT.link _ hj
    · have h3 : j + 1 ≠ k + 1 := fun h => h1 (by omega)
      rw [e3 j h1 h2]
      by_cases h4 : j + 1 = k
      · rw [h4, e1, hLh]
        have := hT.link j hj
        rw [h4] at this; exact this
      · rw [e3 (j + 1) h4 h3]; exact hT.link j hj
  have hfirst : (T' 0).head? = (S 0).head? := by
    by_cases h1 : (0 : ℕ) = k
    · rw [h1, e1, hLh, ← h1]; exact hT.first
    · have h2 : (0 : ℕ) ≠ k + 1 := by omega
      rw [e3 0 h1 h2]; exact hT.first
  have hlastN : (T' (N - 1)).getLast? = (S (N - 1)).getLast? := by
    by_cases h2 : N - 1 = k + 1
    · rw [h2, e2, hRl, ← h2]; exact hT.lastN
    · have h1 : N - 1 ≠ k := by omega
      rw [e3 _ h1 h2]; exact hT.lastN
  refine ⟨hsimple, hsub, hhead, hlink, hfirst, hlastN, ?_⟩
  intro j hjk hj hh hhd'
  by_cases hjk' : j = k
  · subst hjk'
    rw [e1, e2] at *
    rw [hint]
    rw [hRh] at hhd'
    have := Option.some.inj hhd'
    rw [this]
  · -- an earlier junction: the sets only shrank, and the common endpoint is still there
    have hjk2 : j < k := by omega
    have e4 : T' j = T j := e3 j (by omega) (by omega)
    have hold := hT.adj j hjk2 hj
    have hmem2 : (T' (j + 1)).head? = (T (j + 1)).head? := by
      by_cases h4 : j + 1 = k
      · rw [h4, e1, hLh]
      · rw [e3 (j + 1) h4 (by omega)]
    rw [hmem2] at hhd'
    have hsub1 : chainSet (T' j) ∩ chainSet (T' (j + 1)) ⊆ chainSet (T j) ∩ chainSet (T (j + 1)) := by
      refine inter_subset_inter (by rw [e4]) ?_
      by_cases h4 : j + 1 = k
      · rw [h4, e1]; exact hLs
      · rw [e3 (j + 1) h4 (by omega)]
    rw [hold hh hhd'] at hsub1
    apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨?_, ?_⟩, fun y hy => hsub1 hy⟩
    · rw [e4]
      have := mem_chainSet_of_head hhd'
      have hl : (T j).getLast? = some hh := by rw [hT.link j hj]; exact hhd'
      exact mem_chainSet_of_getLast hl
    · exact mem_chainSet_of_head (by rw [hmem2]; exact hhd')

lemma exists_lin {N : ℕ} {S : ℕ → List (ℝ × ℝ)} (hS : RawChains N S) :
    ∀ k, k < N → ∃ T, LinInv N k S T := by
  intro k
  induction k with
  | zero => intro h; exact ⟨S, LinInv.init hS⟩
  | succ k ih =>
    intro hk
    obtain ⟨T, hT⟩ := ih (by omega)
    exact hT.step hk

/-- **A cycle of simple chains can be trimmed so that consecutive chains meet exactly at their common
endpoint.** The new chains are sub-chains of the old ones. -/
theorem exists_cyc_of_raw {N : ℕ} (hN : 3 ≤ N) {S : ℕ → List (ℝ × ℝ)} (hS : RawChains N S) :
    ∃ T : ℕ → List (ℝ × ℝ), CycChains N T ∧ ∀ j < N, chainSet (T j) ⊆ chainSet (S j) := by
  obtain ⟨T, hT⟩ := exists_lin hS (N - 1) (by omega)
  have h0N : N - 1 ≠ 0 := by omega
  obtain ⟨a, ha⟩ : ∃ a, (T 0).head? = some a := by
    cases h : (T 0).head? with
    | none => exact absurd h (hT.head _ (by omega))
    | some a => exact ⟨a, rfl⟩
  have hLe : (T (N - 1)).getLast? = some a := by rw [hT.lastN, hS.close, ← hT.first]; exact ha
  obtain ⟨L', R', h, hL', hR', hLh, hLl, hRh, hRl, hLs, hRs, hint⟩ :=
    fix_junction (hT.simple _ (by omega)) (hT.simple 0 (by omega)) hLe ha
  set T' : ℕ → List (ℝ × ℝ) := Function.update (Function.update T (N - 1) L') 0 R' with hT'
  have e1 : T' (N - 1) = L' := by
    simp [hT', Function.update_of_ne h0N]
  have e2 : T' 0 = R' := by simp [hT']
  have e3 : ∀ j, j ≠ N - 1 → j ≠ 0 → T' j = T j := by
    intro j h1 h2
    simp [hT', Function.update_of_ne h1, Function.update_of_ne h2]
  have hheads : ∀ j, j < N → j ≠ 0 → (T' j).head? = (T j).head? := by
    intro j hj h2
    by_cases h1 : j = N - 1
    · subst h1; rw [e1, hLh]
    · rw [e3 j h1 h2]
  have hlasts : ∀ j, j < N → j ≠ N - 1 → (T' j).getLast? = (T j).getLast? := by
    intro j hj h1
    by_cases h2 : j = 0
    · subst h2; rw [e2, hRl]
    · rw [e3 j h1 h2]
  have hsub : ∀ j < N, chainSet (T' j) ⊆ chainSet (S j) := by
    intro j hj
    by_cases h1 : j = N - 1
    · subst h1; rw [e1]; exact hLs.trans (hT.sub _ hj)
    by_cases h2 : j = 0
    · subst h2; rw [e2]; exact hRs.trans (hT.sub _ hj)
    rw [e3 j h1 h2]; exact hT.sub j hj
  have hsimple : ∀ j < N, IsSimpleChain (T' j) := by
    intro j hj
    by_cases h1 : j = N - 1
    · subst h1; rw [e1]; exact hL'
    by_cases h2 : j = 0
    · subst h2; rw [e2]; exact hR'
    rw [e3 j h1 h2]; exact hT.simple j hj
  have hlink : ∀ j, j + 1 < N → (T' j).getLast? = (T' (j + 1)).head? := by
    intro j hj
    rw [hlasts j (by omega) (by omega), hheads (j + 1) hj (by omega)]
    exact hT.link j hj
  refine ⟨T', ⟨hsimple, ?_, hlink, ?_, ?_, ?_, ?_⟩, hsub⟩
  · intro j hj
    by_cases h2 : j = 0
    · subst h2; rw [e2, hRh]; simp
    · rw [hheads j hj h2]; exact hT.head j hj
  · rw [e1, e2, hLl, hRh]
  · intro j hj hh hhd
    have hhd' : (T (j + 1)).head? = some hh := by rw [← hheads (j + 1) hj (by omega)]; exact hhd
    have hold := hT.adj j (by omega) hj hh hhd'
    have hsub1 : chainSet (T' j) ∩ chainSet (T' (j + 1)) ⊆ chainSet (T j) ∩ chainSet (T (j + 1)) := by
      have hj' : j ≠ 0 → chainSet (T' j) ⊆ chainSet (T j) := by
        intro h2
        by_cases h1 : j = N - 1
        · omega
        · rw [e3 j h1 h2]
      have hj0 : chainSet (T' j) ⊆ chainSet (T j) := by
        by_cases h2 : j = 0
        · subst h2; rw [e2]; exact hRs
        · exact hj' h2
      have hj1 : chainSet (T' (j + 1)) ⊆ chainSet (T (j + 1)) := by
        by_cases h1 : j + 1 = N - 1
        · rw [h1, e1]; exact hLs
        · rw [e3 (j + 1) h1 (by omega)]
      exact inter_subset_inter hj0 hj1
    rw [hold] at hsub1
    apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨?_, mem_chainSet_of_head hhd⟩, fun y hy => hsub1 hy⟩
    have : (T' j).getLast? = some hh := by rw [hlink j hj]; exact hhd
    exact mem_chainSet_of_getLast this
  · intro hh hhd
    rw [e2, hRh] at hhd
    have := Option.some.inj hhd
    rw [e1, e2, hint, this]
  · intro j k hjk hk hne
    exact (hS.disj j k hjk hk hne).mono (hsub j (by omega)) (hsub k hk)

end Lightlike.PL.Schoenflies
