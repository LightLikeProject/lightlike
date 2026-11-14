import Lightlike.Recoupling.FifteenJ

/-!
# Symmetries of the 4-valent intertwiners

The intertwiner `fourJ j₁ j₂ j₃ j₄ k` couples the legs `(j₁ j₂)` to the virtual spin `k`, and with
it the legs `(j₃ j₄)`. Reordering the legs within the channel `(12)(34)` changes it only by a sign
(doubled units):

* `fourJ_swap₁₂`: exchanging the first two legs gives `(-1)^((j₁ + j₂ + k)/2)`;
* `fourJ_swap₃₄`: exchanging the last two legs gives `(-1)^((k + j₃ + j₄)/2)`;
* `fourJ_swapPairs`: exchanging the two pairs gives `(-1)^k`.

They follow from the symmetries of the 3j symbols under exchange and cyclic permutation of
columns. `fourJ_eq_zero_of_parity` records that an intertwiner vanishes when a projection has the
wrong parity, which makes sign identities such as `(-1)^((j + m)/2) = (-1)^j (-1)^((j - m)/2)`
usable termwise.

## References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (Princeton, 1957), §3.7: the symmetries
  of the 3j symbols under permutations of columns.
- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §5.4: the 4-valent intertwiners.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- **Exchange of the first two legs**: `ι_{j₂ j₁ j₃ j₄}^{(k)} = (-1)^((j₁+j₂+k)/2) ι_{j₁ j₂ j₃ j₄}^{(k)}`. -/
theorem fourJ_swap₁₂ (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₂ j₁ j₃ j₄ k m₂ m₁ m₃ m₄ = (-1) ^ ((j₁ + j₂ + k) / 2) * fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ := by
  unfold fourJ
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [threeJ_swap j₁ j₂ k m₁ m₂ μ]
  ring

/-- **Exchange of the last two legs**: `ι_{j₁ j₂ j₄ j₃}^{(k)} = (-1)^((k+j₃+j₄)/2) ι_{j₁ j₂ j₃ j₄}^{(k)}`. -/
theorem fourJ_swap₃₄ (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₁ j₂ j₄ j₃ k m₁ m₂ m₄ m₃ = (-1) ^ ((k + j₃ + j₄) / 2) * fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ := by
  unfold fourJ
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [threeJ_swap₂₃ k j₃ j₄ (-μ) m₃ m₄]
  ring

/-- **Exchange of the two pairs**: `ι_{j₃ j₄ j₁ j₂}^{(k)} = (-1)^k ι_{j₁ j₂ j₃ j₄}^{(k)}`. -/
theorem fourJ_swapPairs (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₃ j₄ j₁ j₂ k m₃ m₄ m₁ m₂ = (-1) ^ k * fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ := by
  unfold fourJ
  simp only [Finset.mul_sum]
  rw [sum_Icc_neg]
  refine sum_congr rfl fun μ _ => ?_
  rw [threeJ_cycle k j₃ j₄ (-μ) m₃ m₄, ← threeJ_cycle k j₁ j₂ (- -μ) m₁ m₂, neg_neg]
  by_cases hp : ((k : ℤ) - μ) % 2 = 0
  · have h1 : ((k : ℤ) - -μ) / 2 = ((k : ℤ) - μ) / 2 + μ := by omega
    have h2 : (-1 : ℝ) ^ μ = (-1) ^ k := by
      rw [← zpow_natCast]
      exact neg_one_zpow_congr (by omega)
    rw [h1, zpow_add₀ (by norm_num), h2]
    ring
  · rw [threeJ_of_not (j₁ := j₁) (j₂ := j₂) (j₃ := k) (m₁ := m₁) (m₂ := m₂) (m₃ := μ)
      (fun h => hp (by obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h; exact h10))]
    ring

/-- An intertwiner vanishes when one of its projections has the wrong parity (or lies outside its
range): a nonzero `fourJ` has admissible projections on all four legs. -/
theorem admProj_of_fourJ_ne_zero {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ}
    (h : fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ ≠ 0) :
    AdmProj j₁ m₁ ∧ AdmProj j₂ m₂ ∧ AdmProj j₃ m₃ ∧ AdmProj j₄ m₄ := by
  unfold fourJ at h
  obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
  have hA := adm3_of_threeJ_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hμ))
  have hB := adm3_of_threeJ_ne_zero (right_ne_zero_of_mul hμ)
  unfold AdmProj
  omega

/-- The four spins of a nonzero intertwiner have even sum. -/
theorem even_of_fourJ_ne_zero {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ}
    (h : fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ ≠ 0) : (j₁ + j₂ + j₃ + j₄) % 2 = 0 := by
  unfold fourJ at h
  obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h)
  have hA := adm3_of_threeJ_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul hμ))
  have hB := adm3_of_threeJ_ne_zero (right_ne_zero_of_mul hμ)
  omega

end Lightlike.Recoupling
