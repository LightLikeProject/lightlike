import Lightlike.Recoupling.ThreeJ
import Lightlike.PonzanoRegge.Move14

/-!
# 4-valent intertwiners from 3j symbols

The invariant subspace of `V_{j₁} ⊗ V_{j₂} ⊗ V_{j₃} ⊗ V_{j₄}` has an orthonormal basis labelled by
an intermediate ("virtual") spin `k` coupling the pair `(j₁ j₂)`, and with it the pair `(j₃ j₄)`.
In components (Martin-Dussaud, §5.4, eqs. (44)–(45)):

`ι^{(k)}_{m₁ m₂ m₃ m₄} = √(2k + 1) Σ_μ (-1)^{k - μ} (j₁ j₂ k; m₁ m₂ μ) (k j₃ j₄; -μ m₃ m₄)`,

the 4jm symbol times `√(2k + 1)`. Here this is `fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄`, with Physlib's
3j symbols `threeJ` and, as everywhere in this library, doubled spins `jᵢ, k ∈ ℕ` and doubled
projections `mᵢ, μ ∈ ℤ`: the normalisation is `√(k + 1)` and the phase `(-1)^((k - μ)/2)`.

## Main results

- `sum_fourJ_mul_fourJ`: **orthonormality**,
  `Σ_{m₁ m₂ m₃ m₄} ι^{(k)} ι^{(k')} = δ_{kk'}` for `k` admissible (`(j₁ j₂ k)` and `(k j₃ j₄)`
  admissible triads), and `0` otherwise.

All 3j symbols are real, so the Hermitian inner product of two such tensors is the plain sum of
products used here.

## References

- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.4, eqs. (44), (45), (49).
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

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
      (∑ μ ∈ J, A m₁ m₂ μ * B μ m₃ m₄) * (∑ μ' ∈ J', A' m₁ m₂ μ' * B' μ' m₃ m₄) =
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
      threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ) m₃ m₄ = if Tri k j₃ j₄ then 1 else 0 := by
  rw [sum_Icc_neg k, ← sum_threeJ_sq k j₃ j₄]
  refine sum_congr rfl fun μ _ => sum_congr rfl fun m₃ _ => sum_congr rfl fun m₄ _ => ?_
  rw [neg_neg, sq]

/-- **Orthonormality of the 4-valent intertwiners**:
`Σ_{m₁ m₂ m₃ m₄} ι^{(k)}_{m} ι^{(k')}_{m} = δ_{kk'}` when `(j₁ j₂ k)` and `(k j₃ j₄)` are
admissible triads, and `0` otherwise (Martin-Dussaud, eq. (49)). -/
theorem sum_fourJ_mul_fourJ (j₁ j₂ j₃ j₄ k k' : ℕ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
        fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ * fourJ j₁ j₂ j₃ j₄ k' m₁ m₂ m₃ m₄ =
      if k = k' ∧ Tri j₁ j₂ k ∧ Tri k j₃ j₄ then 1 else 0 := by
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
        (if k = k' ∧ μ = μ' ∧ Tri j₁ j₂ k ∧ AdmProj k μ then 1 / ((k : ℝ) + 1) else 0) := by
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
        (if k = k ∧ μ = μ' ∧ Tri j₁ j₂ k ∧ AdmProj k μ then 1 / ((k : ℝ) + 1) else 0) *
        (∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃, ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
          threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ') m₃ m₄) =
      (if Tri j₁ j₂ k then 1 / ((k : ℝ) + 1) else 0) *
        ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃, ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
          threeJ k j₃ j₄ (-μ) m₃ m₄ * threeJ k j₃ j₄ (-μ) m₃ m₄ := by
    intro μ hμ
    rw [sum_eq_single μ (fun μ' _ hne => by rw [ite_eq_right (fun h => hne h.2.1.symm)]; ring)
      (fun h => absurd hμ h), hs, one_mul]
    by_cases hadm : AdmProj k μ
    · by_cases ht : Tri j₁ j₂ k
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
  by_cases ht : Tri j₁ j₂ k <;> by_cases ht' : Tri k j₃ j₄ <;> simp [ht, ht', hpos.ne']

/-! ## Change of channel: the overlap is a 6j symbol -/

/-- Exchange of the first and last columns:
`(j₃ j₂ j₁; m₃ m₂ m₁) = (-1)^(j₁+j₂+j₃) (j₁ j₂ j₃; m₁ m₂ m₃)`. -/
lemma threeJ_swap₁₃ (j₁ j₂ j₃ : ℕ) (m₁ m₂ m₃ : ℤ) :
    threeJ j₃ j₂ j₁ m₃ m₂ m₁ = (-1) ^ ((j₁ + j₂ + j₃) / 2) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ := by
  rw [threeJ_swap j₂ j₃ j₁ m₂ m₃ m₁, threeJ_cycle, show j₂ + j₃ + j₁ = j₁ + j₂ + j₃ by ring]

/-- Sign bookkeeping for `overlap_term`: two products of the same four factors with sign factors
agree when the total exponents agree mod 2 wherever all four factors are nonzero. -/
lemma sign_mul_eq {a b E : ℤ} {P q r r' s : ℕ} {F₁ F₂ F₃ F₄ : ℝ}
    (h : F₁ ≠ 0 → F₂ ≠ 0 → F₃ ≠ 0 → F₄ ≠ 0 →
      (a + b) % 2 = ((P : ℤ) + E + q + r + r' + s) % 2) :
    (-1 : ℝ) ^ a * F₁ * F₂ * ((-1) ^ b * F₃ * F₄) =
      (-1 : ℝ) ^ P * ((-1) ^ E * (F₁ * ((-1) ^ q * F₃) * ((-1) ^ r * ((-1) ^ r' * F₄)) *
        ((-1) ^ s * F₂))) := by
  have hn : (-1 : ℝ) ≠ 0 := by norm_num
  have hL : (-1 : ℝ) ^ a * F₁ * F₂ * ((-1) ^ b * F₃ * F₄) =
      (-1 : ℝ) ^ (a + b) * (F₁ * F₂ * F₃ * F₄) := by
    rw [zpow_add₀ hn]; ring
  have hR : (-1 : ℝ) ^ P * ((-1) ^ E * (F₁ * ((-1) ^ q * F₃) * ((-1) ^ r * ((-1) ^ r' * F₄)) *
      ((-1) ^ s * F₂))) =
      (-1 : ℝ) ^ ((P : ℤ) + E + q + r + r' + s) * (F₁ * F₂ * F₃ * F₄) := by
    simp only [zpow_add₀ hn, zpow_natCast]; ring
  rw [hL, hR]
  rcases prod_four_eq_zero_or h with h0 | h0
  · rw [h0]; simp
  · rw [neg_one_zpow_congr h0]

/-- One term of the overlap of the `(12)(34)` and `(13)(24)` intertwiners is a term of the 6j sum
`sixJSym j₁ j₂ k j₄ j₃ l`, after the change of summation variables
`(m₁, m₂, μ, m₄, m₃, ν) ↦ (-m₁, -m₂, -μ, -m₄, m₃, -ν)`. -/
lemma overlap_term (j₁ j₂ j₃ j₄ k l : ℕ) (m₁ m₂ m₃ m₄ μ ν : ℤ) :
    ((-1 : ℝ) ^ (((k : ℤ) - μ) / 2) * threeJ j₁ j₂ k m₁ m₂ μ * threeJ k j₃ j₄ (-μ) m₃ m₄) *
      ((-1 : ℝ) ^ (((l : ℤ) - ν) / 2) * threeJ j₁ j₃ l m₁ m₃ ν * threeJ l j₂ j₄ (-ν) m₂ m₄) =
    (-1 : ℝ) ^ ((j₂ + j₃ + k + l) / 2) *
      sixJTerm j₁ j₂ k j₄ j₃ l ![-m₁, -m₂, -μ, -m₄, m₃, -ν] := by
  have hT : sixJTerm j₁ j₂ k j₄ j₃ l ![-m₁, -m₂, -μ, -m₄, m₃, -ν] =
      (-1 : ℝ) ^ (((j₁ : ℤ) - -m₁ + ((j₂ : ℤ) - -m₂) + ((k : ℤ) - -μ) + ((j₄ : ℤ) - -m₄) +
        ((j₃ : ℤ) - m₃) + ((l : ℤ) - -ν)) / 2) *
      (threeJ j₁ j₂ k (-(-m₁)) (-(-m₂)) (-(-μ)) * threeJ j₁ j₃ l (-m₁) (-m₃) (-ν) *
        threeJ j₄ j₂ l (-m₄) (-m₂) (-(-ν)) * threeJ j₄ j₃ k (-(-m₄)) m₃ (-μ)) := rfl
  have e3 : threeJ j₄ j₂ l (-m₄) (-m₂) ν =
      (-1) ^ ((j₄ + j₂ + l) / 2) * ((-1) ^ ((l + j₂ + j₄) / 2) * threeJ l j₂ j₄ (-ν) m₂ m₄) := by
    have h := threeJ_neg j₄ j₂ l m₄ m₂ (-ν)
    rw [neg_neg] at h
    rw [h, threeJ_swap₁₃]
  rw [hT]
  simp only [neg_neg]
  rw [threeJ_neg j₁ j₃ l, e3, threeJ_swap₁₃ k j₃ j₄ (-μ) m₃ m₄]
  refine sign_mul_eq fun h₁ h₂ h₃ h₄ => ?_
  obtain ⟨s₁, -, -, -, -, -, -, p₁, p₂, p₃, -, -, -, t₁⟩ := adm3_of_threeJ_ne_zero h₁
  obtain ⟨s₂, -, -, -, -, -, -, -, p₅, p₆, -, -, -, t₂⟩ := adm3_of_threeJ_ne_zero h₂
  obtain ⟨s₃, -, -, -, -, -, -, -, p₇, p₈, -, -, -, t₃⟩ := adm3_of_threeJ_ne_zero h₃
  obtain ⟨s₄, -, -, -, -, -, -, -, -, -, -, -, -, t₄⟩ := adm3_of_threeJ_ne_zero h₄
  omega

/-- Six nested projection sums as one sum over a product of the ranges. -/
lemma sum_six_eq_sum_product (I₁ I₂ I₃ I₄ I₅ I₆ : Finset ℤ) (G : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℝ) :
    ∑ a ∈ I₁, ∑ b ∈ I₂, ∑ c ∈ I₃, ∑ d ∈ I₄, ∑ e ∈ I₅, ∑ f ∈ I₆, G a b c d e f =
      ∑ p ∈ I₁ ×ˢ (I₂ ×ˢ (I₃ ×ˢ (I₄ ×ˢ (I₅ ×ˢ I₆)))),
        G p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 := by
  simp only [sum_product]

/-- **Change of channel.** The overlap of the `(j₁ j₂)(j₃ j₄)` intertwiner with virtual spin `k`
and the `(j₁ j₃)(j₂ j₄)` intertwiner with virtual spin `l` is a 6j symbol:
`⟨ι^{(12)k} | ι^{(13)l}⟩ = (-1)^(j₂+j₃+k+l) √((2k+1)(2l+1)) {j₁ j₂ k; j₄ j₃ l}`
(doubled units). -/
theorem sum_fourJ_mul_fourJ_swap (j₁ j₂ j₃ j₄ k l : ℕ) :
    ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄,
        fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ * fourJ j₁ j₃ j₂ j₄ l m₁ m₃ m₂ m₄ =
      (-1) ^ ((j₂ + j₃ + k + l) / 2) * Real.sqrt (((k : ℝ) + 1) * ((l : ℝ) + 1)) *
        sixJSym j₁ j₂ k j₄ j₃ l := by
  -- the six projection sums are the 6j sum, reindexed
  have H : ∑ m₁ ∈ Icc (-(j₁ : ℤ)) j₁, ∑ m₂ ∈ Icc (-(j₂ : ℤ)) j₂, ∑ m₃ ∈ Icc (-(j₃ : ℤ)) j₃,
      ∑ m₄ ∈ Icc (-(j₄ : ℤ)) j₄, ∑ μ ∈ Icc (-(k : ℤ)) k, ∑ ν ∈ Icc (-(l : ℤ)) l,
        sixJTerm j₁ j₂ k j₄ j₃ l ![-m₁, -m₂, -μ, -m₄, m₃, -ν] = sixJSym j₁ j₂ k j₄ j₃ l := by
    rw [sum_six_eq_sum_product, sixJSym]
    refine sum_nbij' (fun p => ![-p.1, -p.2.1, -p.2.2.2.2.1, -p.2.2.2.1, p.2.2.1, -p.2.2.2.2.2])
      (fun n => (-n 0, -n 1, n 4, -n 3, -n 2, -n 5)) (fun p hp => ?_) (fun n hn => ?_)
      (fun p _ => ?_) (fun n _ => ?_) (fun p _ => rfl)
    · simp only [mem_product, mem_Icc] at hp
      rw [mem_sixJBox]
      simp only [Matrix.cons_val]
      omega
    · rw [mem_sixJBox] at hn
      simp only [mem_product, mem_Icc]
      omega
    · simp
    · funext i
      fin_cases i <;> simp
  have h1 : ∀ m₁ m₂ m₃ m₄ : ℤ,
      fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ * fourJ j₁ j₃ j₂ j₄ l m₁ m₃ m₂ m₄ =
        Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((l : ℝ) + 1) * (-1 : ℝ) ^ ((j₂ + j₃ + k + l) / 2) *
          ∑ μ ∈ Icc (-(k : ℤ)) k, ∑ ν ∈ Icc (-(l : ℤ)) l,
              sixJTerm j₁ j₂ k j₄ j₃ l ![-m₁, -m₂, -μ, -m₄, m₃, -ν] := fun m₁ m₂ m₃ m₄ => by
    unfold fourJ
    rw [mul_mul_mul_comm, sum_mul_sum]
    simp only [overlap_term, mul_sum]
    refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
    ring
  simp only [h1, ← mul_sum, H]
  rw [Real.sqrt_mul (by positivity)]
  ring

/-! ## Orthogonality of the recoupling matrix -/

/-- **6j orthogonality for all spins** (doubled units):
`Σ_x (x+1)(q+1) {B A x; E F q}{B A x; E F r} = δ_{qr} [(A E q), (B q F) admissible]`.
For `B, E > 0` this is `Lightlike.Pentagon.sixJSym_orth`; the diagonal is `Lightlike.PR.sixJSym_sq_orth`; off
the diagonal a zero `B` or `E` forces `q = r` by the triangle rule. -/
theorem sixJSym_orth_all (B A E F q r : ℕ) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F r) =
      if q = r ∧ Tri A E q ∧ Tri B q F then 1 else 0 := by
  by_cases hBE : 0 < B ∧ 0 < E
  · exact sixJSym_orth hBE.1 hBE.2
  by_cases hqr : q = r
  · subst hqr
    have hq : ((q : ℝ) + 1) ≠ 0 := by positivity
    rw [show ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F q) =
        ((q : ℝ) + 1) * ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by ring, Lightlike.PR.sixJSym_sq_orth]
    by_cases ht : Tri A E q ∧ Tri B q F
    · rw [ite_eq_left ht, ite_eq_left ⟨rfl, ht⟩]; field_simp
    · rw [ite_eq_right ht, ite_eq_right (fun h => ht h.2)]; ring
  · rw [ite_eq_right (fun h => hqr h.1)]
    refine sum_eq_zero fun x _ => ?_
    by_cases h1 : sixJSym B A x E F q = 0
    · rw [h1]; ring
    by_cases h2 : sixJSym B A x E F r = 0
    · rw [h2]; ring
    exfalso
    obtain ⟨-, a2, a3, -⟩ := tri_of_sixJSym_ne_zero h1
    obtain ⟨-, b2, b3, -⟩ := tri_of_sixJSym_ne_zero h2
    unfold Tri at a2 a3 b2 b3
    omega

/-- The **recoupling coefficient** `⟨ι^{(12)k} | ι^{(13)l}⟩` between the `(j₁ j₂)(j₃ j₄)` and the
`(j₁ j₃)(j₂ j₄)` intertwiner bases: `(-1)^(j₂+j₃+k+l) √((2k+1)(2l+1)) {j₁ j₂ k; j₄ j₃ l}`
(doubled units; `sum_fourJ_mul_fourJ_swap`). -/
noncomputable def fourRecoupling (j₁ j₂ j₃ j₄ k l : ℕ) : ℝ :=
  (-1) ^ ((j₂ + j₃ + k + l) / 2) * Real.sqrt (((k : ℝ) + 1) * ((l : ℝ) + 1)) *
    sixJSym j₁ j₂ k j₄ j₃ l

/-- `{j₁ j₂ k; j₄ j₃ l} = {j₁ j₃ l; j₄ j₂ k}`: exchange of upper and lower spins in the last two
columns, from the tetrahedral symmetry. -/
lemma sixJSym_flip₂₃ (j₁ j₂ k j₄ j₃ l : ℕ) :
    sixJSym j₁ j₂ k j₄ j₃ l = sixJSym j₁ j₃ l j₄ j₂ k := by
  rw [← sj_swap13 j₁ j₂ k j₄ j₃ l, ← sj_flip12 k j₂ j₁ l j₃ j₄, ← sj_swap13 l j₃ j₁ k j₂ j₄]

/-- **Orthogonality of the recoupling matrix**:
`Σ_l ⟨ι^{(12)k} | ι^{(13)l}⟩ ⟨ι^{(12)k'} | ι^{(13)l}⟩ = δ_{kk'}` for admissible `k`, `0` otherwise.
The sum runs over `l ≤ j₁ + j₃`, beyond which `(j₁ j₃ l)` is not a triad. -/
theorem sum_fourRecoupling_mul (j₁ j₂ j₃ j₄ k k' : ℕ) :
    ∑ l ∈ range (j₁ + j₃ + 1), fourRecoupling j₁ j₂ j₃ j₄ k l * fourRecoupling j₁ j₂ j₃ j₄ k' l =
      if k = k' ∧ Tri j₁ j₂ k ∧ Tri k j₃ j₄ then 1 else 0 := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  set σ : ℝ := (-1) ^ (j₁ + j₂ + (k + k') / 2) with hσ
  have hterm : ∀ l ∈ range (j₁ + j₃ + 1),
      fourRecoupling j₁ j₂ j₃ j₄ k l * fourRecoupling j₁ j₂ j₃ j₄ k' l =
        σ * (Real.sqrt (((k : ℝ) + 1) * ((k' : ℝ) + 1)) / ((k : ℝ) + 1)) *
          (((l : ℝ) + 1) * ((k : ℝ) + 1) *
            (sixJSym j₁ j₃ l j₄ j₂ k * sixJSym j₁ j₃ l j₄ j₂ k')) := by
    intro l _
    unfold fourRecoupling
    rw [sixJSym_flip₂₃ j₁ j₂ k, sixJSym_flip₂₃ j₁ j₂ k']
    have hs : Real.sqrt (((k : ℝ) + 1) * ((l : ℝ) + 1)) *
        Real.sqrt (((k' : ℝ) + 1) * ((l : ℝ) + 1)) =
        Real.sqrt (((k : ℝ) + 1) * ((k' : ℝ) + 1)) * ((l : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by positivity),
        show ((k : ℝ) + 1) * ((l : ℝ) + 1) * (((k' : ℝ) + 1) * ((l : ℝ) + 1)) =
          ((k : ℝ) + 1) * ((k' : ℝ) + 1) * (((l : ℝ) + 1) * ((l : ℝ) + 1)) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
    by_cases h0 : sixJSym j₁ j₃ l j₄ j₂ k * sixJSym j₁ j₃ l j₄ j₂ k' = 0
    · rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
    · obtain ⟨t1, t2, -, -⟩ := tri_of_sixJSym_ne_zero (left_ne_zero_of_mul h0)
      obtain ⟨-, u2, -, -⟩ := tri_of_sixJSym_ne_zero (right_ne_zero_of_mul h0)
      unfold Tri at t1 t2 u2
      have hsign : ((-1 : ℝ) ^ ((j₂ + j₃ + k + l) / 2)) * (-1) ^ ((j₂ + j₃ + k' + l) / 2) = σ := by
        rw [hσ, ← pow_add, neg_one_pow_eq_pow_mod_two,
          neg_one_pow_eq_pow_mod_two (n := j₁ + j₂ + (k + k') / 2)]
        congr 1
        omega
      calc _ = ((-1 : ℝ) ^ ((j₂ + j₃ + k + l) / 2) * (-1) ^ ((j₂ + j₃ + k' + l) / 2)) *
            (Real.sqrt (((k : ℝ) + 1) * ((l : ℝ) + 1)) *
              Real.sqrt (((k' : ℝ) + 1) * ((l : ℝ) + 1))) *
            (sixJSym j₁ j₃ l j₄ j₂ k * sixJSym j₁ j₃ l j₄ j₂ k') := by ring
        _ = σ * (Real.sqrt (((k : ℝ) + 1) * ((k' : ℝ) + 1)) * ((l : ℝ) + 1)) *
            (sixJSym j₁ j₃ l j₄ j₂ k * sixJSym j₁ j₃ l j₄ j₂ k') := by rw [hsign, hs]
        _ = _ := by field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sixJSym_orth_all]
  by_cases hc : k = k' ∧ Tri j₁ j₂ k ∧ Tri k j₃ j₄
  · obtain ⟨rfl, h1, h2⟩ := hc
    rw [ite_eq_left ⟨rfl, by unfold Tri at *; omega, by unfold Tri at *; omega⟩,
      ite_eq_left ⟨rfl, h1, h2⟩, Real.sqrt_mul_self (by positivity), div_self hk, hσ]
    unfold Tri at h1
    rw [show j₁ + j₂ + (k + k) / 2 = 2 * ((j₁ + j₂ + k) / 2) by omega, pow_mul]
    norm_num
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, by unfold Tri at *; omega,
      by unfold Tri at *; omega⟩)]
    ring

/-! ## The change of channel as an identity of tensors -/

/-- **Parseval argument.** If the `g l` are orthogonal with squared norms `e l`, `c l e l = c l`,
`⟨f, g l⟩ = c l`, and `‖f‖² = Σ_l (c l)²`, then `f = Σ_l c l • g l` on `s`: the squared norm of
the difference is `‖f‖² - 2 Σ_l c_l² + Σ_l c_l² = 0`. -/
lemma eq_sum_of_parseval {α : Type*} (s : Finset α) (L : Finset ℕ) (f : α → ℝ) (g : ℕ → α → ℝ)
    (c e : ℕ → ℝ) (hfg : ∀ l ∈ L, ∑ a ∈ s, f a * g l a = c l)
    (hgg : ∀ l ∈ L, ∀ l' ∈ L, ∑ a ∈ s, g l a * g l' a = if l = l' then e l else 0)
    (hce : ∀ l ∈ L, c l * e l = c l)
    (hff : ∑ a ∈ s, f a * f a = ∑ l ∈ L, c l * c l) :
    ∀ a ∈ s, f a = ∑ l ∈ L, c l * g l a := by
  have hexp : ∀ a, (f a - ∑ l ∈ L, c l * g l a) ^ 2 = f a * f a -
      2 * ∑ l ∈ L, c l * (f a * g l a) + ∑ l ∈ L, ∑ l' ∈ L, c l * c l' * (g l a * g l' a) := by
    intro a
    have h1 : f a * ∑ l ∈ L, c l * g l a = ∑ l ∈ L, c l * (f a * g l a) := by
      rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    have h2 : (∑ l ∈ L, c l * g l a) * (∑ l' ∈ L, c l' * g l' a) =
        ∑ l ∈ L, ∑ l' ∈ L, c l * c l' * (g l a * g l' a) := by
      rw [sum_mul_sum]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    rw [← h1, ← h2]; ring
  have hG : ∑ a ∈ s, ∑ l ∈ L, c l * (f a * g l a) = ∑ l ∈ L, c l * c l := by
    rw [sum_comm]
    exact sum_congr rfl fun l hl => by rw [← mul_sum, hfg l hl]
  have hH : ∑ a ∈ s, ∑ l ∈ L, ∑ l' ∈ L, c l * c l' * (g l a * g l' a) =
      ∑ l ∈ L, c l * c l := by
    rw [sum_comm]
    refine sum_congr rfl fun l hl => ?_
    rw [sum_comm]
    simp only [← mul_sum]
    rw [sum_congr rfl fun l' hl' => by rw [hgg l hl l' hl']]
    rw [sum_eq_single l (fun l' _ hne => by rw [ite_eq_right (Ne.symm hne)]; ring)
      (fun h => absurd hl h), ite_eq_left rfl, mul_assoc, hce l hl]
  have key : ∑ a ∈ s, (f a - ∑ l ∈ L, c l * g l a) ^ 2 = 0 := by
    simp only [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, hG, hH, hff]
    ring
  intro a ha
  have h0 := (sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg _)).mp key a ha
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)

/-- A 4-valent intertwiner vanishes when a projection is out of range. -/
lemma fourJ_eq_zero_of_not_mem {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ}
    (h : ¬(m₁ ∈ Icc (-(j₁ : ℤ)) j₁ ∧ m₂ ∈ Icc (-(j₂ : ℤ)) j₂ ∧ m₃ ∈ Icc (-(j₃ : ℤ)) j₃ ∧
      m₄ ∈ Icc (-(j₄ : ℤ)) j₄)) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  unfold fourJ
  rw [sum_eq_zero fun μ _ => ?_, mul_zero]
  by_cases h₁ : threeJ j₁ j₂ k m₁ m₂ μ = 0
  · rw [h₁]; ring
  by_cases h₂ : threeJ k j₃ j₄ (-μ) m₃ m₄ = 0
  · rw [h₂]; ring
  exfalso
  obtain ⟨-, a1, a2, a3, a4, -⟩ := adm3_of_threeJ_ne_zero h₁
  obtain ⟨-, -, -, b3, b4, b5, b6, -⟩ := adm3_of_threeJ_ne_zero h₂
  simp only [mem_Icc] at h
  omega

/-- **Change of channel as a tensor identity**: the `(j₁ j₂)(j₃ j₄)` intertwiner is the
combination `ι^{(12)k} = Σ_l ⟨ι^{(12)k} | ι^{(13)l}⟩ ι^{(13)l}` of the `(j₁ j₃)(j₂ j₄)`
intertwiners, componentwise, for all spins and projections. -/
theorem fourJ_eq_sum_fourRecoupling (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = ∑ l ∈ range (j₁ + j₃ + 1),
      fourRecoupling j₁ j₂ j₃ j₄ k l * fourJ j₁ j₃ j₂ j₄ l m₁ m₃ m₂ m₄ := by
  by_cases hm : m₁ ∈ Icc (-(j₁ : ℤ)) j₁ ∧ m₂ ∈ Icc (-(j₂ : ℤ)) j₂ ∧ m₃ ∈ Icc (-(j₃ : ℤ)) j₃ ∧
      m₄ ∈ Icc (-(j₄ : ℤ)) j₄
  swap
  · rw [fourJ_eq_zero_of_not_mem hm]
    refine (sum_eq_zero fun l _ => ?_).symm
    rw [fourJ_eq_zero_of_not_mem (fun h => hm ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩), mul_zero]
  set I₁ := Icc (-(j₁ : ℤ)) j₁
  set I₂ := Icc (-(j₂ : ℤ)) j₂
  set I₃ := Icc (-(j₃ : ℤ)) j₃
  set I₄ := Icc (-(j₄ : ℤ)) j₄
  let f : ℤ × ℤ × ℤ × ℤ → ℝ := fun p => fourJ j₁ j₂ j₃ j₄ k p.1 p.2.1 p.2.2.1 p.2.2.2
  let g : ℕ → ℤ × ℤ × ℤ × ℤ → ℝ := fun l p => fourJ j₁ j₃ j₂ j₄ l p.1 p.2.2.1 p.2.1 p.2.2.2
  let e : ℕ → ℝ := fun l => if Tri j₁ j₃ l ∧ Tri l j₂ j₄ then 1 else 0
  have hsum : ∀ F : ℤ × ℤ × ℤ × ℤ → ℝ, ∑ p ∈ I₁ ×ˢ (I₂ ×ˢ (I₃ ×ˢ I₄)), F p =
      ∑ a ∈ I₁, ∑ b ∈ I₂, ∑ c ∈ I₃, ∑ d ∈ I₄, F (a, b, c, d) := fun F => by
    simp only [sum_product]
  have key := eq_sum_of_parseval (I₁ ×ˢ (I₂ ×ˢ (I₃ ×ˢ I₄))) (range (j₁ + j₃ + 1)) f g
    (fourRecoupling j₁ j₂ j₃ j₄ k) e
    (fun l _ => by
      rw [hsum]
      exact sum_fourJ_mul_fourJ_swap j₁ j₂ j₃ j₄ k l)
    (fun l _ l' _ => by
      rw [hsum]
      have h := sum_fourJ_mul_fourJ j₁ j₃ j₂ j₄ l l'
      rw [sum_congr rfl fun a _ => sum_comm] at h
      simp only [g, e]
      rw [h]
      by_cases hl : l = l'
      · subst hl; simp
      · simp [hl])
    (fun l _ => by
      by_cases ht : Tri j₁ j₃ l ∧ Tri l j₂ j₄
      · simp [e, ht]
      · have h0 : sixJSym j₁ j₂ k j₄ j₃ l = 0 := by
          by_contra h
          obtain ⟨-, t2, t3, -⟩ := tri_of_sixJSym_ne_zero h
          exact ht ⟨t2, by unfold Tri at *; omega⟩
        simp [fourRecoupling, h0])
    (by
      rw [hsum, sum_fourRecoupling_mul]
      exact sum_fourJ_mul_fourJ j₁ j₂ j₃ j₄ k k)
  exact key (m₁, m₂, m₃, m₄) (by simp only [mem_product]; exact hm)

end Lightlike.Recoupling
