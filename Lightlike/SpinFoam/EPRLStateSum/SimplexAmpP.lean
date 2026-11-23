import Lightlike.SpinFoam.EPRLStateSum.SimplexSwap

/-!
# The recoupled 4-simplex contraction in terms of the Ooguri vertex amplitude

`fifteenJSimplex_eq_sum_ampP` writes the 15j symbol of a 4-simplex, with the virtual spins
`i_a` in the channel `(a+1, a+2)(a+3, a+4)`, as a signed combination of the Ooguri vertex
amplitudes `ampP J K` (`Lightlike/SpinFoam/Vertex.lean`), whose virtual spins `K a = l_a` are in the channel
`(a+1, a+3)(a+2, a+4)`. The coefficients are products of five recoupling matrices and the sign
`recoupSign J K = (-1)^(K₀+…+K₄+J₁₂+J₁₄+J₃₄) * ampSign J K`.
-/

open Finset

namespace Lightlike.SpinFoam.EPRLStateSum

open Lightlike.Recoupling Lightlike.SpinFoam

/-- The sign `S(J, K)` in front of the 15j symbol in `ampP`, as one power of `-1`. -/
def ampSign (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  (-1) ^ (J 0 2 + J 0 4 + J 2 4 + K 0 + K 4 + K 2 + (J 1 3 + J 0 1 + K 1) / 2 +
    (K 2 + J 2 4 + J 1 2) / 2 + (J 2 3 + J 0 2 + K 2) / 2 + (K 3 + J 3 4 + J 1 3) / 2)

/-- `ampP J K` is `ampSign J K` times the pentagram-relabelled 15j symbol. -/
theorem ampP_eq (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    ampP J K = ampSign J K *
      fifteenJSimplex (J 0 2) (J 0 4) (J 0 1) (J 0 3) (J 2 4) (J 1 2) (J 2 3) (J 1 4) (J 3 4)
        (J 1 3) (K 0) (K 2) (K 4) (K 1) (K 3) := by
  unfold ampP ampSign
  simp only [pow_add]
  ring

/-- `ampSign` squares to one. -/
theorem ampSign_mul_self (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    ampSign J K * ampSign J K = 1 := by
  unfold ampSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- The sign in front of `ampP J K` in the expansion of the 4-simplex contraction. -/
def recoupSign (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  (-1) ^ (K 0 + K 1 + K 2 + K 3 + K 4 + J 1 2 + J 1 4 + J 3 4) * ampSign J K

/-- **The 4-simplex contraction in the Ooguri basis.** The 15j symbol with virtual spins
`i₀,…,i₄` is `Σ_l Π_a fourRecoupling(i_a, l_a) · recoupSign J l · ampP J l`. -/
theorem fifteenJSimplex_eq_sum_ampP (J : Fin 5 → Fin 5 → ℕ) (i₀ i₁ i₂ i₃ i₄ : ℕ) :
    fifteenJSimplex (J 0 1) (J 0 2) (J 0 3) (J 0 4) (J 1 2) (J 1 3) (J 1 4) (J 2 3) (J 2 4)
        (J 3 4) i₀ i₁ i₂ i₃ i₄ =
      ∑ l₀ ∈ range (J 0 1 + J 0 3 + 1), ∑ l₁ ∈ range (J 1 2 + J 1 4 + 1),
      ∑ l₂ ∈ range (J 2 3 + J 0 2 + 1), ∑ l₃ ∈ range (J 3 4 + J 1 3 + 1),
      ∑ l₄ ∈ range (J 0 4 + J 2 4 + 1),
        fourRecoupling (J 0 1) (J 0 2) (J 0 3) (J 0 4) i₀ l₀ *
          fourRecoupling (J 1 2) (J 1 3) (J 1 4) (J 0 1) i₁ l₁ *
          fourRecoupling (J 2 3) (J 2 4) (J 0 2) (J 1 2) i₂ l₂ *
          fourRecoupling (J 3 4) (J 0 3) (J 1 3) (J 2 3) i₃ l₃ *
          fourRecoupling (J 0 4) (J 1 4) (J 2 4) (J 3 4) i₄ l₄ *
        (recoupSign J ![l₀, l₁, l₂, l₃, l₄] * ampP J ![l₀, l₁, l₂, l₃, l₄]) := by
  rw [fifteenJSimplex_recouple]
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
    Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun l₃ _ =>
    Finset.sum_congr rfl fun l₄ _ => ?_
  rw [simplexGen_swapped_eq, ampP_eq]
  have key : ∀ A σ S F : ℝ, S * S = 1 → A * (σ * F) = A * (σ * S * (S * F)) :=
    fun A σ S F h => by linear_combination (-(A * σ * F)) * h
  have h := ampSign_mul_self J ![l₀, l₁, l₂, l₃, l₄]
  unfold recoupSign
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h ⊢
  exact key _ _ _ _ h

end Lightlike.SpinFoam.EPRLStateSum
