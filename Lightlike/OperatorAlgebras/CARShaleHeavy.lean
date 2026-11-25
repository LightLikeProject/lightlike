import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Only finitely many eigenvalue classes are heavy

For nonnegative weights `μ k` with a finite total, call a value `m` *heavy* if some finite set of indices with `μ = m`
has total weight above `1/2`. A heavy value is positive, its class is finite, and there are only finitely many heavy
values (their disjoint witnesses have total weight above `N/2` for `N` of them, while all finite sums are at most the
total). So the set of indices with a heavy value is finite (`finite_heavy`).
-/

namespace Lightlike.OperatorAlgebras.CARShale

variable {κ : Type*} {μ : κ → ℝ} {h : ℝ}

/-- Auxiliary lemma `sum_le_of_hasSum` for the fermionic Shale theorem. -/
lemma sum_le_of_hasSum (hμ0 : ∀ k, 0 ≤ μ k) (hsum : HasSum μ h) (G : Finset κ) : ∑ k ∈ G, μ k ≤ h :=
  sum_le_hasSum G (fun k _ => hμ0 k) hsum

/-- The class of a positive value is finite. -/
lemma finite_class (hμ0 : ∀ k, 0 ≤ μ k) (hsum : HasSum μ h) {m : ℝ} (hm : 0 < m) : {k | μ k = m}.Finite := by
  by_contra hinf
  have hinf' : {k | μ k = m}.Infinite := hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (h / m)
  obtain ⟨G, hGsub, hGcard⟩ := hinf'.exists_subset_card_eq N
  have h1 : ∑ k ∈ G, μ k = N * m := by
    rw [Finset.sum_congr rfl (fun k hk => hGsub hk)]
    simp [hGcard]
  have h2 := sum_le_of_hasSum hμ0 hsum G
  rw [h1] at h2
  have : h < N * m := by
    have := (div_lt_iff₀ hm).1 hN
    linarith
  linarith

/-- The set of heavy values is finite. -/
lemma finite_heavy_values (hμ0 : ∀ k, 0 ≤ μ k) (hsum : HasSum μ h) :
    {m : ℝ | ∃ F : Finset κ, (∀ l ∈ F, μ l = m) ∧ 1 / 2 < ∑ l ∈ F, μ l}.Finite := by
  classical
  by_contra hinf
  have hinf' : {m : ℝ | ∃ F : Finset κ, (∀ l ∈ F, μ l = m) ∧ 1 / 2 < ∑ l ∈ F, μ l}.Infinite := hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * h)
  obtain ⟨M, hMsub, hMcard⟩ := hinf'.exists_subset_card_eq N
  choose! F hF1 hF2 using fun m (hm : m ∈ M) => (hMsub hm : _)
  have hh : 0 ≤ h := hsum.nonneg hμ0
  have hMne : M.Nonempty := by
    rw [← Finset.card_pos, hMcard]
    exact_mod_cast (lt_of_le_of_lt (by linarith : (0 : ℝ) ≤ 2 * h) hN)
  have hdisj : (M : Set ℝ).PairwiseDisjoint F := by
    intro m hm m' hm' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro l hl hl'
    exact hne ((hF1 m hm l hl).symm.trans (hF1 m' hm' l hl'))
  have hsumG : ∑ k ∈ M.biUnion F, μ k = ∑ m ∈ M, ∑ k ∈ F m, μ k := Finset.sum_biUnion hdisj
  have hlt : ∑ m ∈ M, (1 / 2 : ℝ) < ∑ m ∈ M, ∑ k ∈ F m, μ k :=
    Finset.sum_lt_sum_of_nonempty hMne (fun m hm => hF2 m hm)
  have hle := sum_le_of_hasSum hμ0 hsum (M.biUnion F)
  rw [hsumG] at hle
  simp only [Finset.sum_const, hMcard, nsmul_eq_mul] at hlt
  linarith

/-- The set of indices with a heavy value is finite. -/
lemma finite_heavy (hμ0 : ∀ k, 0 ≤ μ k) (hsum : HasSum μ h) :
    {k : κ | ∃ F : Finset κ, (∀ l ∈ F, μ l = μ k) ∧ 1 / 2 < ∑ l ∈ F, μ l}.Finite := by
  have hv := finite_heavy_values hμ0 hsum
  refine (Set.Finite.biUnion (t := fun m : ℝ => {k : κ | μ k = m}) hv (fun m hm => ?_)).subset (fun k hk => ?_)
  · obtain ⟨F, hF1, hF2⟩ := hm
    have hmpos : 0 < m := by
      by_contra hneg
      have hm0 : m ≤ 0 := not_lt.1 hneg
      have : ∑ l ∈ F, μ l ≤ 0 := Finset.sum_nonpos fun l hl => by rw [hF1 l hl]; exact hm0
      linarith
    exact finite_class hμ0 hsum hmpos
  · exact Set.mem_biUnion (x := μ k) hk rfl

end Lightlike.OperatorAlgebras.CARShale
