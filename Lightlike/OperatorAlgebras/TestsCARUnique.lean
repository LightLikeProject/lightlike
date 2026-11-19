import Lightlike.OperatorAlgebras.CARUnique
/-!
# Checks of Dereziński's Theorem 10 and Corollary 2 on the Jordan-Wigner representation
-/

namespace Lightlike.OperatorAlgebras

open scoped InnerProductSpace Kronecker

/-- The Pauli matrices are a representation of the CAR over `ℝ³`, hence by operators on `ℂ²`. -/
example : IsCAROn (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (pauliFamily a)) :=
  isCARRep_pauli.isCAROn_toEuclideanCLM

/-- Theorem 10, part 1, applied to the Jordan-Wigner representation itself. -/
example (n : ℕ) :
    ∃ U : PiLp 2 (fun _ : Fin n → Fin 2 =>
        carVacuum (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a))) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → Fin 2),
      ∀ b f, U (tensorOne (jordanWigner n b) f) = Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n b) (U f) :=
  car_unitarily_equivalent_jordanWigner (isCAROn_jordanWigner n)

/-- The Jordan-Wigner vacuum space is one-dimensional. -/
example (n : ℕ) :
    Module.finrank ℂ (carVacuum (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a))) = 1 := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n → Fin 2)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace]; exact Fintype.card_pos)
  exact (isIrreducibleCAR_iff (isCAROn_jordanWigner n)).mp (isIrreducibleCAR_jordanWigner n)

/-- Corollary 2: an irreducible representation over `ℝ²ⁿ` on a nonzero space is the Jordan-Wigner one. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E] {n : ℕ}
    {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (hi : IsIrreducibleCAR φ) :
    ∃ V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n → Fin 2),
      ∀ b v, V (φ b v) = Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n b) (V v) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n → Fin 2)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace]; exact Fintype.card_pos)
  exact car_irreducible_unitarily_equivalent h (isCAROn_jordanWigner n) hi (isIrreducibleCAR_jordanWigner n)

/-- Theorem 10, part 2, for a representation over `ℝ²ⁿ⁺¹`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ} {ψ : Fin (2 * n + 1) → (E →L[ℂ] E)}
    (h : IsCAROn ψ) :
    ∃ (U : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum (fun b : Fin (2 * n) => ψ b.castSucc)) ≃ₗᵢ[ℂ] E)
      (T : carVacuum (fun b : Fin (2 * n) => ψ b.castSucc) →L[ℂ] carVacuum (fun b : Fin (2 * n) => ψ b.castSucc)),
      T * T = 1 ∧ (∀ v w, ⟪T v, w⟫_ℂ = ⟪v, T w⟫_ℂ) ∧
      (∀ b f, U (tensorOne (jordanWigner n b) f) = ψ b.castSucc (U f)) ∧
      ∀ f, U (tensorOp (jwParity n) T f) = ψ (Fin.last _) (U f) :=
  car_odd_unitarily_equivalent h

/-- The Jordan-Wigner parity of one site is `σ₃`. -/
example : jwParity 1 = (pauli3 ⊗ₖ (1 : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ)).submatrix
    (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm := rfl

end Lightlike.OperatorAlgebras
