import Mathlib
import Lightlike.TemperleyLieb.Window

/-!
# Coefficients of `e_j v` and the sorted-coordinates bound

`coeff_modelE_FT`, `coeff_modelE_TF`: the coefficient of `e_j v` at a sequence with bits `(0,1)` (resp. `(1,0)`) at
`j, j+1` in terms of `v`.  Consequently, if `e_j v = 0` then `v σ = q⁻¹ v σ'` for `σ` with bits `(1,0)` at `j, j+1`
and `σ'` the sequence with the bits swapped.
-/

namespace Lightlike.TemperleyLieb

open Finsupp
open scoped Classical

variable {k : Type*} [Field k]

/-- `e_j v` as a sum over the support. -/
lemma modelE_apply_eq_sum (q : kˣ) (j : ℕ) (v : ModelSpace k) :
    modelE q j v = v.sum (fun σ c => c • eBasis q j σ) := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [map_finsuppSum]
  simp [modelE_single]

/-- The coefficient of `eBasis σ` at `τ`. -/
lemma eBasis_apply (q : kˣ) (j : ℕ) (σ τ : ℕ → Bool) :
    eBasis q j σ τ =
      if σ j = true ∧ σ (j + 1) = false then
        (if τ = set2 σ j false true then 1 else 0) - (q : k) * (if τ = σ then 1 else 0)
      else if σ j = false ∧ σ (j + 1) = true then
        (if τ = set2 σ j true false then 1 else 0) - ((q⁻¹ : kˣ) : k) * (if τ = σ then 1 else 0)
      else 0 := by
  unfold eBasis
  rcases h0 : σ j with _ | _ <;> rcases h1 : σ (j + 1) with _ | _ <;>
    simp [Finsupp.single_apply, eq_comm]

/-- If `eBasis ρ` has a nonzero coefficient at `σ` with bits `(1,0)` at `j, j+1`, then `ρ ∈ {σ, σ'}`. -/
lemma eBasis_ne_zero_cases (q : kˣ) {j : ℕ} {ρ σ : ℕ → Bool} (h0 : σ j = true) (h1 : σ (j + 1) = false)
    (h : eBasis q j ρ σ ≠ (0 : k)) : ρ = σ ∨ ρ = set2 σ j false true := by
  rw [eBasis_apply] at h
  by_cases hρ : ρ j = true ∧ ρ (j + 1) = false
  · rw [if_pos hρ] at h
    by_cases hσ : σ = set2 ρ j false true
    · exfalso
      have : σ j = false := by rw [hσ]; simp [set2]
      rw [h0] at this; exact Bool.noConfusion this
    · by_cases hσ2 : σ = ρ
      · left; exact hσ2.symm
      · exfalso; apply h; simp [hσ, hσ2]
  · rw [if_neg hρ] at h
    by_cases hρ2 : ρ j = false ∧ ρ (j + 1) = true
    · rw [if_pos hρ2] at h
      by_cases hσ : σ = set2 ρ j true false
      · right
        rw [hσ]
        funext n
        simp only [set2, Function.update_apply]
        split_ifs with a b <;> first | (subst_vars; simp_all) | rfl | (simp_all)
      · by_cases hσ2 : σ = ρ
        · exfalso; rw [← hσ2] at hρ2; rw [h0] at hρ2; exact Bool.noConfusion hρ2.1
        · exfalso; apply h; simp [hσ, hσ2]
    · rw [if_neg hρ2] at h; exact absurd rfl h

/-- The coefficient of `e_j v` at a sequence `σ` with bits `(1,0)` at `j, j+1`. -/
lemma modelE_coeff_TF (q : kˣ) {j : ℕ} (v : ModelSpace k) {σ : ℕ → Bool} (h0 : σ j = true)
    (h1 : σ (j + 1) = false) :
    (modelE q j v) σ = v (set2 σ j false true) - (q : k) * v σ := by
  have hne : set2 σ j false true ≠ σ := by
    intro h; have := congrFun h j; simp [set2] at this; rw [h0] at this; exact Bool.noConfusion this
  rw [modelE_apply_eq_sum, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_of_support_subset v (s := v.support ∪ {σ, set2 σ j false true}) Finset.subset_union_left]
  · have hsub : ∑ x ∈ ({σ, set2 σ j false true} : Finset (ℕ → Bool)), v x * (eBasis q j x) σ =
        ∑ x ∈ v.support ∪ {σ, set2 σ j false true}, v x * (eBasis q j x) σ := by
      refine Finset.sum_subset Finset.subset_union_right ?_
      intro ρ _ hρ
      have : eBasis q j ρ σ = 0 := by
        by_contra hc
        rcases eBasis_ne_zero_cases q h0 h1 hc with h | h
        · exact hρ (by simp [h])
        · exact hρ (by simp [h])
      simp [this]
    rw [← hsub, Finset.sum_pair hne.symm]
    have e1 : eBasis q j σ σ = -(q : k) := by
      rw [eBasis_apply]; simp [h0, h1, hne.symm]
    have e2 : eBasis q j (set2 σ j false true) σ = 1 := by
      rw [eBasis_apply]
      have a0 : set2 σ j false true j = false := by simp [set2]
      have a1 : set2 σ j false true (j + 1) = true := by simp [set2]
      have a2 : set2 (set2 σ j false true) j true false = σ := by
        rw [set2_set2, ← set2_self σ j, h0, h1, set2_set2]
      simp [a0, a1, a2, hne.symm]
    rw [e1, e2]; ring
  · intro ρ _; simp

/-- If `e_j v = 0` then `v σ = q⁻¹ v σ'` for `σ` with bits `(1,0)` at `j, j+1`. -/
lemma kernel_relation (q : kˣ) {j : ℕ} {v : ModelSpace k} (hv : modelE q j v = 0) {σ : ℕ → Bool}
    (h0 : σ j = true) (h1 : σ (j + 1) = false) :
    v σ = ((q⁻¹ : kˣ) : k) * v (set2 σ j false true) := by
  have h := modelE_coeff_TF q v h0 h1
  rw [hv] at h
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination ((q⁻¹ : kˣ) : k) * h - (v σ) * hq

end Lightlike.TemperleyLieb
