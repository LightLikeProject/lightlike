import Lightlike.Recoupling.NineJ

/-!
# The 9j symbol under the exchange of two rows

`nineJSym_swapRows`: exchanging the first two rows of a 9j symbol multiplies it by
`(-1)^(Σ_columns (j₁ₖ + j₂ₖ + j₃ₖ)/2)` (doubled units), the classical symmetry of the 9j symbol
under an odd permutation of its rows (Varshalovich–Moskalev–Khersonskii, *Quantum Theory of Angular
Momentum*, §10.4.1, eq. (1) of §10.4: the sign is `(-1)^S` with `S` the sum of all nine
(undoubled) spins). The proof is the 3j form `nineJSym_eq_sum_threeJ`: the row 3j symbols are
permuted, and each column 3j symbol has its first two columns exchanged (`threeJ_swap`).
-/

open Finset PhyslibAlpha.Sl2

namespace Lightlike.Recoupling

/-- Moving a sum outward past three others. -/
lemma sum_out_three {M : Type*} [AddCommMonoid M] (A₁ A₂ A₃ B : Finset ℤ)
    (g : ℤ → ℤ → ℤ → ℤ → M) :
    ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, ∑ a₃ ∈ A₃, ∑ b ∈ B, g a₁ a₂ a₃ b =
      ∑ b ∈ B, ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, ∑ a₃ ∈ A₃, g a₁ a₂ a₃ b := by
  calc ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, ∑ a₃ ∈ A₃, ∑ b ∈ B, g a₁ a₂ a₃ b
      = ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, ∑ b ∈ B, ∑ a₃ ∈ A₃, g a₁ a₂ a₃ b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a₁ ∈ A₁, ∑ b ∈ B, ∑ a₂ ∈ A₂, ∑ a₃ ∈ A₃, g a₁ a₂ a₃ b :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- **The 9j symbol under the exchange of its first two rows.** -/
theorem nineJSym_swapRows (j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ : ℕ) :
    nineJSym j₂₁ j₂₂ j₂₃ j₁₁ j₁₂ j₁₃ j₃₁ j₃₂ j₃₃ =
      (-1) ^ ((j₁₁ + j₂₁ + j₃₁) / 2 + (j₁₂ + j₂₂ + j₃₂) / 2 + (j₁₃ + j₂₃ + j₃₃) / 2) *
        nineJSym j₁₁ j₁₂ j₁₃ j₂₁ j₂₂ j₂₃ j₃₁ j₃₂ j₃₃ := by
  rw [nineJSym_eq_sum_threeJ, nineJSym_eq_sum_threeJ]
  -- bring the sums of the second row outward on the right
  conv_rhs =>
    rw [Finset.mul_sum]
    enter [2, μ₁₁]; rw [Finset.mul_sum]
    enter [2, μ₁₂]; rw [Finset.mul_sum]
    enter [2, μ₁₃]; rw [Finset.mul_sum]
    enter [2, μ₂₁]; rw [Finset.mul_sum]
    enter [2, μ₂₂]; rw [Finset.mul_sum]
    enter [2, μ₂₃]; rw [Finset.mul_sum]
    enter [2, μ₃₁]; rw [Finset.mul_sum]
    enter [2, μ₃₂]; rw [Finset.mul_sum]
  conv_lhs => rw [sum_out_three]
  conv_lhs => enter [2, μ₁₁]; rw [sum_out_three]
  conv_lhs => enter [2, μ₁₁, 2, μ₁₂]; rw [sum_out_three]
  refine Finset.sum_congr rfl fun μ₁₁ _ => Finset.sum_congr rfl fun μ₁₂ _ =>
    Finset.sum_congr rfl fun μ₁₃ _ => Finset.sum_congr rfl fun μ₂₁ _ =>
    Finset.sum_congr rfl fun μ₂₂ _ => Finset.sum_congr rfl fun μ₂₃ _ =>
    Finset.sum_congr rfl fun μ₃₁ _ => Finset.sum_congr rfl fun μ₃₂ _ =>
    Finset.sum_congr rfl fun μ₃₃ _ => ?_
  rw [threeJ_swap j₁₁ j₂₁ j₃₁ μ₁₁ μ₂₁ μ₃₁, threeJ_swap j₁₂ j₂₂ j₃₂ μ₁₂ μ₂₂ μ₃₂,
    threeJ_swap j₁₃ j₂₃ j₃₃ μ₁₃ μ₂₃ μ₃₃, pow_add, pow_add]
  ring

end Lightlike.Recoupling
