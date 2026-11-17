import Lightlike.CausalSets.Basic
import Mathlib.Tactic

/-!
# Counting labelled partial orders on a small set

A strict partial order on `Fin n` is a relation `r` (as Booleans) that is irreflexive and transitive
(`IsStrictOrder'`, so it is also asymmetric). The number of such orders is `1, 1, 3, 19, 219` for
`n = 0, …, 4` (the labelled partial orders), and the number of those of *height at most two*
(no chain `i ≺ j ≺ k`, two layers) is `1, 1, 3, 13, 87`. By the Kleitman–Rothschild theorem (1975)
almost all finite partial orders have exactly three layers, so the two-layer fraction tends to `0`;
the small values `13/19` and `87/219` only show the decrease, the theorem is not formalised.

## References

* D. J. Kleitman and B. L. Rothschild, *Asymptotic enumeration of partial orders on a finite set*,
  Trans. Amer. Math. Soc. 205 (1975) 205–220.
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 6 (the entropy of causal sets and the Kleitman–Rothschild orders).

The comparison of the statements with these sources at a location is pending.
-/

namespace Lightlike.CausalSets

/-- A Boolean relation on `Fin n` is a **strict partial order**: irreflexive and transitive. -/
def IsStrictOrder' {n : ℕ} (r : Fin n → Fin n → Bool) : Prop :=
  (∀ i, r i i = false) ∧ ∀ i j k, r i j = true → r j k = true → r i k = true

instance {n : ℕ} (r : Fin n → Fin n → Bool) : Decidable (IsStrictOrder' r) := by
  unfold IsStrictOrder'; infer_instance

/-- The relation has **height at most two**: no chain `i ≺ j ≺ k`. -/
def HeightLeTwo {n : ℕ} (r : Fin n → Fin n → Bool) : Prop :=
  ∀ i j k, r i j = true → r j k = false

instance {n : ℕ} (r : Fin n → Fin n → Bool) : Decidable (HeightLeTwo r) := by
  unfold HeightLeTwo; infer_instance

/-- The number of labelled strict partial orders on `Fin n`. -/
def countOrders (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter IsStrictOrder').card

/-- The number of labelled strict partial orders on `Fin n` of height at most two. -/
def countTwoLayer (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter
    fun r => IsStrictOrder' r ∧ HeightLeTwo r).card

theorem countOrders_values : countOrders 0 = 1 ∧ countOrders 1 = 1 ∧ countOrders 2 = 3 ∧
    countOrders 3 = 19 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem countTwoLayer_values : countTwoLayer 0 = 1 ∧ countTwoLayer 1 = 1 ∧ countTwoLayer 2 = 3 ∧
    countTwoLayer 3 = 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

set_option maxHeartbeats 1000000 in
/-- Four elements: `219` labelled orders, `87` of height at most two. -/
theorem count_four : countOrders 4 = 219 ∧ countTwoLayer 4 = 87 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- The two-layer fraction decreases: `13/19 > 87/219`, and both are below `1` once chains of
three elements exist. -/
example : (87 : ℚ) / 219 < 13 / 19 ∧ (13 : ℚ) / 19 < 1 := by norm_num

/-- Wrong model: the relation `i ≺ j` for all `i ≠ j` is not a strict order (not transitive
as it relates `0 ≺ 1 ≺ 0`), and the order `0 ≺ 1 ≺ 2` has height three. -/
example : ¬ IsStrictOrder' (fun i j : Fin 2 => decide (i ≠ j)) := by decide

example : ¬ HeightLeTwo (fun i j : Fin 3 => decide (i < j)) := by decide

end Lightlike.CausalSets
