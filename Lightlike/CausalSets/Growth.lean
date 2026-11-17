import Lightlike.CausalSets.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Transitive percolation: the simplest sequential growth of a causal set

A causal set grows by adding elements one at a time, each new element above some down-set of the
existing ones. The labels record the order of birth, so a *naturally labelled* poset on `Fin n` has
`i ≺ j ⇒ i < j` (`NatPoset n`). In **transitive percolation** (Rideout–Sorkin 2000) each new element
`j` is related to each earlier element independently with probability `p`, and the relations are
completed transitively. The past of `j` is then a down-set `D` with `m` maximal elements and has
probability `p^m q^{j - |D|}`, `q = 1 - p`: its maximal elements must be chosen, the elements outside
`D` must not be, and the other elements of `D` are free. The weight of a naturally labelled poset is
the product over `j` (`tpExpP`, `tpExpQ` give the exponents).

For `n = 1, 2, 3, 4` the numbers of naturally labelled posets are `1, 2, 7, 40`, and for `n = 2, 3`
the weights sum to `1` by exact enumeration of the exponent pairs (`q³ + 3 p q² + 2 p² q + p²` for
`n = 3`: the empty order, the three single relations, the two `V`-shaped orders and the chain). The classification of all sequential growth processes obeying Bell causality and
discrete general covariance (Rideout–Sorkin) is not formalised.

## References

* D. P. Rideout and R. D. Sorkin, *Classical sequential growth dynamics for causal sets*, Phys.
  Rev. D 61 (2000) 024002.
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 6.

The comparison of the statements with these sources at a location is pending.
-/

namespace Lightlike.CausalSets

/-- A relation on `Fin n` (as Booleans) is a **naturally labelled partial order** if
`rel i j` implies `i < j` and it is transitive. -/
def IsNatPoset {n : ℕ} (r : Fin n → Fin n → Bool) : Prop :=
  (∀ i j, r i j = true → i < j) ∧ ∀ i j k, r i j = true → r j k = true → r i k = true

instance {n : ℕ} (r : Fin n → Fin n → Bool) : Decidable (IsNatPoset r) := by
  unfold IsNatPoset; infer_instance

/-- The **naturally labelled posets** on `Fin n`. -/
def NatPoset (n : ℕ) : Type := {r : Fin n → Fin n → Bool // IsNatPoset r}

instance (n : ℕ) : Fintype (NatPoset n) := by unfold NatPoset; infer_instance

instance (n : ℕ) : DecidableEq (NatPoset n) := by unfold NatPoset; infer_instance

namespace NatPoset

variable {n : ℕ}

/-- The past of `j`: the elements below it. -/
def past (P : NatPoset n) (j : Fin n) : Finset (Fin n) := Finset.univ.filter fun i => P.1 i j = true

/-- The maximal elements of the past of `j`: those `i` below `j` with no `k` between. -/
def maxPast (P : NatPoset n) (j : Fin n) : Finset (Fin n) :=
  (P.past j).filter fun i => ∀ k ∈ P.past j, P.1 i k = false

end NatPoset

/-- The exponent of `p` in the transitive-percolation weight: the total number of maximal elements
of the pasts. -/
def tpExpP {n : ℕ} (P : NatPoset n) : ℕ := ∑ j : Fin n, (P.maxPast j).card

/-- The exponent of `q` in the transitive-percolation weight: for each `j`, the number of earlier
elements not in the past of `j`. -/
def tpExpQ {n : ℕ} (P : NatPoset n) : ℕ := ∑ j : Fin n, ((j : ℕ) - (P.past j).card)

/-- The **transitive-percolation probability** of the naturally labelled poset `P`. -/
noncomputable def tpProb (p : ℝ) {n : ℕ} (P : NatPoset n) : ℝ := p ^ tpExpP P * (1 - p) ^ tpExpQ P

/-- The numbers of naturally labelled posets on `1, 2, 3, 4` labelled elements. -/
theorem card_natPoset : Fintype.card (NatPoset 1) = 1 ∧ Fintype.card (NatPoset 2) = 2 ∧
    Fintype.card (NatPoset 3) = 7 ∧ Fintype.card (NatPoset 4) = 40 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The multiset of the exponent pairs `(a, b)` of the weights `p^a q^b`, for `n = 3`. -/
theorem exps_three : (Finset.univ : Finset (NatPoset 3)).val.map (fun P => (tpExpP P, tpExpQ P)) =
    {(0, 3), (1, 2), (1, 2), (1, 2), (2, 1), (2, 1), (2, 0)} := by
  decide +kernel

/-- **The probabilities of the seven 3-element naturally labelled posets sum to `1`.** -/
theorem sum_tpProb_three (p : ℝ) : ∑ P : NatPoset 3, tpProb p P = 1 := by
  have h : ∑ P : NatPoset 3, tpProb p P =
      (((Finset.univ : Finset (NatPoset 3)).val.map (fun P => (tpExpP P, tpExpQ P))).map
        (fun ab : ℕ × ℕ => p ^ ab.1 * (1 - p) ^ ab.2)).sum := by
    rw [Multiset.map_map]; rfl
  rw [h, exps_three]
  simp
  ring

/-- **The probabilities of the two 2-element naturally labelled posets (the chain `p`, the
antichain `1 - p`) sum to `1`.** -/
theorem sum_tpProb_two (p : ℝ) : ∑ P : NatPoset 2, tpProb p P = 1 := by
  have e : (Finset.univ : Finset (NatPoset 2)).val.map (fun P => (tpExpP P, tpExpQ P)) =
      {(1, 0), (0, 1)} := by decide +kernel
  have h : ∑ P : NatPoset 2, tpProb p P =
      (((Finset.univ : Finset (NatPoset 2)).val.map (fun P => (tpExpP P, tpExpQ P))).map
        (fun ab : ℕ × ℕ => p ^ ab.1 * (1 - p) ^ ab.2)).sum := by
    rw [Multiset.map_map]; rfl
  rw [h, e]
  simp

/-- Wrong model: the weights `p^m q^0` that forget the elements outside the past do not sum to `1`
for `n = 3` (at `p = 1/2` the sum is not `1`). -/
example : ((Finset.univ : Finset (NatPoset 3)).val.map (fun P => (1 / 2 : ℚ) ^ tpExpP P)).sum ≠ 1 := by
  have e : (Finset.univ : Finset (NatPoset 3)).val.map (fun P => tpExpP P) =
      {0, 1, 1, 1, 2, 2, 2} := by decide +kernel
  have : (Finset.univ : Finset (NatPoset 3)).val.map (fun P => (1 / 2 : ℚ) ^ tpExpP P) =
      (((Finset.univ : Finset (NatPoset 3)).val.map (fun P => tpExpP P)).map fun a => (1 / 2 : ℚ) ^ a) := by
    rw [Multiset.map_map]; rfl
  rw [this, e]
  norm_num

end Lightlike.CausalSets
