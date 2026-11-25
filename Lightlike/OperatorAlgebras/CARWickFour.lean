import Lightlike.OperatorAlgebras.CARWick

/-!
# The four-point function of the CAR fields of a Bogoliubov vacuum

The explicit `n = 4` expansion of the Wick recursion (`wick_four`) and the resulting four-point function
`⟪Ψ, x₁ x₂ x₃ x₄ Ψ⟫ = ⟪Ψ, Ψ⟫ (p₁₂ p₃₄ − p₁₃ p₂₄ + p₁₄ p₂₃)` with `pᵢⱼ = Σ uᵢ vⱼ'` (`car_wick_four`), a check of
`car_wick` at `n = 4` against the Pfaffian of the two-point functions.
-/

open scoped InnerProductSpace
open Finset Matrix

namespace Lightlike.OperatorAlgebras

/-- **The Wick recursion for four fields** is the Pfaffian expansion `p₁₂ p₃₄ − p₁₃ p₂₄ + p₁₄ p₂₃`. -/
lemma wick_four {E : Type*} [AddCommGroup E] [Module ℂ E] (pair : SplitField E → SplitField E → ℂ)
    (a b c d : SplitField E) :
    wick pair [a, b, c, d] = pair a b * pair c d - pair a c * pair b d + pair a d * pair b c := by
  rw [wick]
  simp [Fin.sum_univ_succ, wick_pair, List.eraseIdx]
  ring

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
  {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (α β : Matrix (Fin n) (Fin n) ℂ)
  (h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) {Ψ : E}
  (hΨ : ∀ j, bogAnn α β (carAnnihilation φ) (carCreation φ) j Ψ = 0)

include h h1 h2 in
/-- The pairing of two CAR fields on a nonzero vector is `Σ uᵢ vᵢ'`. -/
lemma pairOf_carField (hΨ0 : Ψ ≠ 0) (c d : (Fin n → ℂ) × (Fin n → ℂ)) :
    pairOf (carField (φ := φ) α β c) (carField (φ := φ) α β d) = ∑ i, c.1 i * d.2 i := by
  have hsp := pairOf_spec (carField_anticomm h α β h1 h2 c d)
  rw [carField_anticomm h α β h1 h2 c d] at hsp
  have := congrArg (fun T : Module.End ℂ E => T Ψ) hsp
  simp only [LinearMap.smul_apply, Module.End.one_apply] at this
  exact (smul_left_injective ℂ hΨ0 this).symm

include h h1 h2 hΨ in
/-- **The four-point function** of CAR fields in a Bogoliubov vacuum, a check of `car_wick` at `n = 4`. -/
theorem car_wick_four (hΨ0 : Ψ ≠ 0) (c₁ c₂ c₃ c₄ : (Fin n → ℂ) × (Fin n → ℂ)) :
    ⟪Ψ, (carField (φ := φ) α β c₁).φ ((carField (φ := φ) α β c₂).φ
        ((carField (φ := φ) α β c₃).φ ((carField (φ := φ) α β c₄).φ Ψ)))⟫_ℂ =
      ⟪Ψ, Ψ⟫_ℂ * ((∑ i, c₁.1 i * c₂.2 i) * (∑ i, c₃.1 i * c₄.2 i) -
        (∑ i, c₁.1 i * c₃.2 i) * (∑ i, c₂.1 i * c₄.2 i) + (∑ i, c₁.1 i * c₄.2 i) * (∑ i, c₂.1 i * c₃.2 i)) := by
  have hw := car_wick h α β h1 h2 hΨ [c₁, c₂, c₃, c₄]
  simp only [List.map_cons, List.map_nil, fieldProd, List.prod_cons, List.prod_nil, mul_one, wick_four] at hw
  simp only [pairOf_carField h α β h1 h2 hΨ0] at hw
  simpa using hw

end

end Lightlike.OperatorAlgebras
