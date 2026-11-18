import Lightlike.CausalSets.Myrheim

/-!
# Longest chains of the order of a permutation

For `n` points of the `1 + 1` causal diamond with distinct light-cone coordinates, the causal order
is the dominance order of a permutation: after ranking the points by their first light-cone
coordinate (`i`), the second ranks (`σ i`) form a permutation `σ`, and `i ≺ j` iff `i < j` and
`σ i < σ j`. This file defines that order on `Fin n` (`DomPoset σ`, a causal set), the length of its
longest chain (`longestChain σ`, the length of a longest increasing subsequence of `σ`), and checks
them by exact enumeration: the sum of `longestChain` over all permutations is `1, 3, 12, 58, 335`
for `n = 1, …, 5`, so the expected longest chain of `n = 3` points is `2`. The comparison with
`c √n` fails for the constant `c = 1` at `n = 3` (`√3 ≠ 2`). The asymptotics `2 √n`
(Vershik–Kerov, Logan–Shepp) is not proved here.

This is part of a bridge between Lorentzian geometry and causal sets: `sprinklePt` places a
permutation in Minkowski space `ℝ^{1+1}` and `coneLE_sprinklePt` shows that the geometric causal
order of the points is the dominance order.

## References

* A. M. Vershik and S. V. Kerov, *Asymptotics of the Plancherel measure of the symmetric group and
  the limiting form of Young tableaux*, Soviet Math. Dokl. 18 (1977).
* B. F. Logan and L. A. Shepp, *A variational problem for random Young tableaux*, Adv. Math. 26
  (1977).
* D. Romik, *The Surprising Mathematics of Longest Increasing Subsequences*, Cambridge University
  Press (2015).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 4.

The comparison of the statements with these sources at a location is pending.
-/

open Finset

namespace Lightlike.CausalSets

variable {n : ℕ}

/-- The finite set `Fin n` with the **dominance order** of the permutation `σ`:
`i ≼ j` iff `i ≤ j` and `σ i ≤ σ j`. -/
def DomPoset (_σ : Equiv.Perm (Fin n)) : Type := Fin n

instance (σ : Equiv.Perm (Fin n)) : LE (DomPoset σ) :=
  ⟨fun i j => (show Fin n from i) ≤ (show Fin n from j) ∧
    σ (show Fin n from i) ≤ σ (show Fin n from j)⟩

lemma domPoset_le_iff (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (show DomPoset σ from i) ≤ (show DomPoset σ from j) ↔ i ≤ j ∧ σ i ≤ σ j := Iff.rfl

/-- The dominance order of a permutation. -/
instance (σ : Equiv.Perm (Fin n)) : PartialOrder (DomPoset σ) where
  le_refl i := ⟨le_rfl, le_rfl⟩
  le_trans i j k h1 h2 := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  le_antisymm i j h1 h2 := σ.injective (le_antisymm h1.2 h2.2)

instance (σ : Equiv.Perm (Fin n)) : Finite (DomPoset σ) := inferInstanceAs (Finite (Fin n))

/-- A subset of `Fin n` is a chain of the dominance order of `σ`. -/
def IsDomChain (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, (i ≤ j ∧ σ i ≤ σ j) ∨ (j ≤ i ∧ σ j ≤ σ i)

instance (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Decidable (IsDomChain σ S) := by
  unfold IsDomChain; infer_instance

/-- The **length of a longest chain** of the dominance order of `σ`: the length of a longest
increasing subsequence of `σ`. -/
def longestChain (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (IsDomChain σ)).sup Finset.card

/-- `IsDomChain` is the chain condition of the causal set `DomPoset σ`. -/
lemma isCausalChain_iff (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    IsCausalChain (show Set (DomPoset σ) from (S : Set (Fin n))) ↔ IsDomChain σ S := by
  constructor
  · intro h i hi j hj
    by_cases hij : i = j
    · subst hij; exact Or.inl ⟨le_rfl, le_rfl⟩
    · rcases h hi hj hij with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
  · intro h i hi j hj _
    exact h i hi j hj

/-- The empty order has longest chain `0` (trust check). -/
example : longestChain (1 : Equiv.Perm (Fin 0)) = 0 := by decide

/-- The identity permutation is a chain of length `n`; the reversal is an antichain, longest chain
`1` (trust checks of the definition). -/
example : longestChain (1 : Equiv.Perm (Fin 4)) = 4 := by decide

example : longestChain (Fin.revPerm : Equiv.Perm (Fin 4)) = 1 := by decide

/-- **Exact enumeration**: the sum of `longestChain` over all permutations of `Fin n` for
`n = 1, …, 5`. -/
theorem sum_longestChain_one : ∑ σ : Equiv.Perm (Fin 1), longestChain σ = 1 := by decide

theorem sum_longestChain_two : ∑ σ : Equiv.Perm (Fin 2), longestChain σ = 3 := by decide

theorem sum_longestChain_three : ∑ σ : Equiv.Perm (Fin 3), longestChain σ = 12 := by decide

theorem sum_longestChain_four : ∑ σ : Equiv.Perm (Fin 4), longestChain σ = 58 := by decide +kernel

/-- The expected longest chain of `3` points is `2`: the average over the `6` permutations. -/
theorem expected_longestChain_three :
    (∑ σ : Equiv.Perm (Fin 3), (longestChain σ : ℚ)) / 6 = 2 := by
  have : ∑ σ : Equiv.Perm (Fin 3), (longestChain σ : ℚ) = 12 := by
    exact_mod_cast sum_longestChain_three
  rw [this]; norm_num

/-- Wrong model: the constant `1` in `c √n` is not the value at `n = 3`; the exact value `2` differs
from `√3`. -/
example : (2 : ℝ) ≠ Real.sqrt 3 := by
  intro h
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [← h] at this
  norm_num at this

/-- **The causal order of a permutation sprinkled in `ℝ^{1+1}`**: the point with light-cone
coordinates `(i, σ i)`. -/
noncomputable def sprinklePt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Fin 2 → ℝ :=
  ![((i : ℕ) + (σ i : ℕ)) / 2, ((i : ℕ) - (σ i : ℕ)) / 2]

/-- The geometric causal order of the points `sprinklePt σ i` in Minkowski space is the dominance
order of `σ`. -/
theorem coneLE_sprinklePt (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    coneLE (sprinklePt σ i) (sprinklePt σ j) ↔ i ≤ j ∧ σ i ≤ σ j := by
  rw [coneLE_one_iff, Fin.forall_fin_two]
  have hi := lc_apply (sprinklePt σ i)
  have hj := lc_apply (sprinklePt σ j)
  have s0 : ∀ k, sprinklePt σ k 0 = ((k : ℕ) + (σ k : ℕ)) / 2 := fun k => by simp [sprinklePt]
  have s1 : ∀ k, sprinklePt σ k 1 = ((k : ℕ) - (σ k : ℕ)) / 2 := fun k => by simp [sprinklePt]
  rw [hi.1, hi.2, hj.1, hj.2, s0, s1, s0, s1]
  have e1 : ((i : ℕ) + (σ i : ℕ)) / 2 + ((i : ℕ) - (σ i : ℕ)) / 2 = (i : ℝ) := by ring
  have e2 : ((i : ℕ) + (σ i : ℕ)) / 2 - ((i : ℕ) - (σ i : ℕ)) / 2 = (σ i : ℝ) := by ring
  have e3 : ((j : ℕ) + (σ j : ℕ)) / 2 + ((j : ℕ) - (σ j : ℕ)) / 2 = (j : ℝ) := by ring
  have e4 : ((j : ℕ) + (σ j : ℕ)) / 2 - ((j : ℕ) - (σ j : ℕ)) / 2 = (σ j : ℝ) := by ring
  rw [e1, e2, e3, e4]
  have c1 : ((i : ℕ) : ℝ) ≤ (j : ℕ) ↔ i ≤ j := by exact_mod_cast Fin.val_fin_le
  have c2 : (((σ i : Fin n) : ℕ) : ℝ) ≤ ((σ j : Fin n) : ℕ) ↔ σ i ≤ σ j := by
    exact_mod_cast Fin.val_fin_le
  rw [c1, c2]

end Lightlike.CausalSets
