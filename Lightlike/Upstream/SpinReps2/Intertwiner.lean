module

public import Lightlike.Upstream.SpinReps2.SixJOrth

/-!
# Orthonormal 4-valent intertwiners from 3j symbols

The invariant subspace of `V_{j₁} ⊗ V_{j₂} ⊗ V_{j₃} ⊗ V_{j₄}` has an orthonormal basis labelled by
an intermediate ("virtual") spin `k` coupling the pair `(j₁ j₂)`, and with it the pair `(j₃ j₄)`:

`ι^{(k)}_{m₁ m₂ m₃ m₄} = √(2k + 1) Σ_μ (-1)^{k - μ} (j₁ j₂ k; m₁ m₂ μ) (k j₃ j₄; -μ m₃ m₄)`.

Here this is `fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄`, with Physlib's 3j symbols `threeJ` and doubled
spins `jᵢ, k ∈ ℕ` and doubled projections `mᵢ, μ ∈ ℤ`: the normalisation is `√(k + 1)` and the
phase `(-1)^((k - μ)/2)`.

## Main definitions

* `PhyslibAlpha.Sl2.fourJ`: the 4-valent intertwiner with virtual spin `k`.

## Main results

* `PhyslibAlpha.Sl2.sum_fourJ_mul_fourJ`: **orthonormality**,
  `Σ_{m₁ m₂ m₃ m₄} ι^{(k)} ι^{(k')} = δ_{kk'}` for `k` admissible (`(j₁ j₂ k)` and `(k j₃ j₄)`
  admissible triads), and `0` otherwise.

All 3j symbols are real, so the Hermitian inner product of two such tensors is the plain sum of
products used here.
-/

@[expose] public section

open Finset

namespace PhyslibAlpha.Sl2

/-- The **4-valent intertwiner** `ι^{(k)}_{m₁ m₂ m₃ m₄}` of `j₁ ⊗ j₂ ⊗ j₃ ⊗ j₄` with virtual spin `k`
in the channel `(j₁ j₂)(j₃ j₄)` (doubled spins and projections):
`√(k + 1) Σ_μ (-1)^((k - μ)/2) (j₁ j₂ k; m₁ m₂ μ) (k j₃ j₄; -μ m₃ m₄)`. -/
noncomputable def fourJ (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) : ℝ :=
  Real.sqrt ((k : ℝ) + 1) * ∑ μ ∈ Icc (-(k : ℤ)) k,
    (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * threeJ j₁ j₂ k m₁ m₂ μ * threeJ k j₃ j₄ (-μ) m₃ m₄

/-- Reordering a contraction of two tensors that are each a sum over one internal index: the
internal sums move outside, and the sums over the four external indices split into two pairs. -/
lemma sum_contract_reorder {I₁ I₂ I₃ I₄ J J' : Finset ℤ} (A A' B B' : ℤ → ℤ → ℤ → ℝ) :
    ∑ m₁ ∈ I₁, ∑ m₂ ∈ I₂, ∑ m₃ ∈ I₃, ∑ m₄ ∈ I₄,
      (∑ μ ∈ J, A m₁ m₂ μ * B μ m₃ m₄) * (∑ μ ∈ J', A' m₁ m₂ μ * B' μ m₃ m₄) =
    ∑ μ ∈ J, ∑ μ' ∈ J', (∑ m₁ ∈ I₁, ∑ m₂ ∈ I₂, A m₁ m₂ μ * A' m₁ m₂ μ') *
      (∑ m₃ ∈ I₃, ∑ m₄ ∈ I₄, B μ m₃ m₄ * B' μ' m₃ m₄) := by
  simp only [sum_mul_sum]
  simp only [sum_comm (s := I₄) (t := J), sum_comm (s := I₃) (t := J), sum_comm (s := I₂) (t := J),
    sum_comm (s := I₁) (t := J), sum_comm (s := I₄) (t := J'), sum_comm (s := I₃) (t := J'),
    sum_comm (s := I₂) (t := J'), sum_comm (s := I₁) (t := J')]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun μ' _ => ?_
  refine sum_congr rfl fun m₁ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun m₂ _ => sum_congr rfl fun m₃ _ => sum_congr rfl fun m₄ _ => ?_
  ring

/-- `Σ_{μ m₃ m₄} (k j₃ j₄; -μ m₃ m₄)² = 1` for an admissible triad, `0` otherwise. -/
lemma sum_threeJ_neg_sq (k j₃ j₄ : ℕ) :
    ∑ μ ∈ Icc (-(k : ℤ)) k, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃, ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
      threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ) m₃ m₄ =
        if Triad k j₃ j₄ then 1 else 0 := by
  rw [sum_Icc_neg k, ← sum_threeJ_sq k j₃ j₄]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun m₃ _ => sum_congr rfl fun m₄ _ => ?_
  rw [neg_neg, sq]

/-- **Orthonormality of the 4-valent intertwiners**:
`Σ_{m₁ m₂ m₃ m₄} ι^{(k)}_{m} ι^{(k')}_{m} = δ_{kk'}` when `(j₁ j₂ k)` and `(k j₃ j₄)` are
admissible triads, and `0` otherwise. -/
theorem sum_fourJ_mul_fourJ (j₁ j₂ j₃ j₄ k k' : ℕ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
        fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ * fourJ j₁ j₂ j₃ j₄ k' m₁ m₂ m₃ m₄ =
      if k = k' ∧ Triad j₁ j₂ k ∧ Triad k j₃ j₄ then 1 else 0 := by
  set c : ℝ := Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k' : ℝ) + 1) with hc
  -- pull out the normalisations and reorder the sums
  have h1 : ∀ m₁ m₂ m₃ m₄ : ℤ,
      fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ * fourJ j₁ j₂ j₃ j₄ k' m₁ m₂ m₃ m₄ =
        c * ((∑ μ ∈ Icc (-(k : ℤ)) k,
          ((-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * threeJ j₁ j₂ k m₁ m₂ μ) *
            threeJ k j₃ j₄ (-μ) m₃ m₄) *
          (∑ μ' ∈ Icc (-(k' : ℤ)) k',
          ((-1 : ℝ) ^ (((k' : ℤ) - μ') / 2) * threeJ j₁ j₂ k' m₁ m₂ μ') *
            threeJ k' j₃ j₄ (-μ') m₃ m₄)) := fun _ _ _ _ => by
    unfold fourJ; rw [hc]; ring
  simp only [h1, ← mul_sum]
  rw [sum_contract_reorder]
  -- the sums over `m₁, m₂` are 3j orthogonality
  have h2 : ∀ μ μ' : ℤ, ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂,
      (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * threeJ j₁ j₂ k m₁ m₂ μ *
        ((-1 : ℝ) ^ (((k' : ℤ) - μ') / 2) * threeJ j₁ j₂ k' m₁ m₂ μ') =
      (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * (-1 : ℝ) ^ (((k' : ℤ) - μ') / 2) *
        (if k = k' ∧ μ = μ' ∧ Triad j₁ j₂ k ∧ AdmProj k μ then 1 / ((k : ℝ) + 1) else 0) := by
    intro μ μ'
    rw [← sum_threeJ_mul_threeJ, mul_sum]
    refine sum_congr rfl fun _ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun _ _ => ?_
    ring
  simp only [h2]
  by_cases hk : k = k'
  swap
  · rw [ite_eq_right (fun h => hk h.1)]
    simp [hk]
  subst hk
  -- `k = k'`: the sum over `μ'` collapses to `μ' = μ`
  have hs : ∀ μ : ℤ, (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) = 1 :=
    fun μ => by rw [← mul_zpow]; norm_num
  have h3 : ∀ μ ∈ Icc (-(k : ℤ)) k, ∑ μ' ∈ Icc (-(k : ℤ)) k,
      (-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * (-1 : ℝ) ^ (((k : ℤ) - μ') / 2) *
        (if k = k ∧ μ = μ' ∧ Triad j₁ j₂ k ∧ AdmProj k μ then 1 / ((k : ℝ) + 1) else 0) *
        (∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃, ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
          threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ') m₃ m₄) =
      (if Triad j₁ j₂ k then 1 / ((k : ℝ) + 1) else 0) *
        ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃, ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
          threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ) m₃ m₄ := by
    intro μ hμ
    rw [sum_eq_single μ (fun μ' _ hne => by rw [ite_eq_right (fun h => hne h.2.1.symm)]; ring)
      (fun h => absurd hμ h), hs, one_mul]
    by_cases hadm : AdmProj k μ
    · by_cases ht : Triad j₁ j₂ k
      · rw [ite_eq_left ⟨rfl, rfl, ht, hadm⟩, ite_eq_left ht]
      · rw [ite_eq_right (fun h => ht h.2.2.1), ite_eq_right ht]
    · -- an inadmissible `μ` kills the 3j symbols `(k j₃ j₄; -μ m₃ m₄)`
      have h0 : ∀ m₃ m₄ : ℤ, threeJ k j₃ j₄ (-μ) m₃ m₄ = 0 := fun m₃ m₄ =>
        threeJ_of_not fun h => hadm (by
          obtain ⟨-, h1, h2, -, -, -, -, h7, -⟩ := h
          exact ⟨by omega, by omega, by omega⟩)
      simp [h0]
  rw [sum_congr rfl h3, ← mul_sum, sum_threeJ_neg_sq]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcc : c = (k : ℝ) + 1 := by rw [hc, Real.mul_self_sqrt hpos.le]
  rw [hcc]
  by_cases ht : Triad j₁ j₂ k <;> by_cases ht' : Triad k j₃ j₄ <;> simp [ht, ht', hpos.ne']

end PhyslibAlpha.Sl2
