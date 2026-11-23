import Lightlike.Rows.G2_077.Final

/-!
# G2-077: trust checks for the pure quasi-free state of `Pos(iΔ)`

* the 2-point example `Δ = !![0, 1; -1, 0]` (the Pauli–Jordan matrix of a 2-chain up to normalisation):
  `Δᵀ = -Δ`, `|Δ| = 1`, so `exists_pure_quasiFree` applies and the state has `ω(W f) = exp(-‖f‖²/4)`;
* a non-antisymmetric matrix `!![0, 1; 1, 0]` does not satisfy the hypothesis of `exists_pure_quasiFree`,
  and the theorem gives nothing for it.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Lightlike.Rows.G2_077

/-- The standard `2 × 2` antisymmetric matrix. -/
def J2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

lemma J2_antisymm : J2ᵀ = -J2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2]

lemma J2_transpose_mul : J2ᵀ * J2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `|J₂| = 1` in closed form. -/
lemma absRe_J2 : absRe J2 = 1 := by
  rw [absRe, J2_transpose_mul]; exact CFC.sqrt_one

/-- The pure quasi-free state of the 2-point example: `ω(W f) = exp(-(f₀² + f₁²)/4)`. -/
theorem J2_expectation :
    ∃ H : Type, ∃ (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
      Nonempty (PureQuasiFreeRep J2 H) := by
  obtain ⟨H, i1, i2, i3, h⟩ := exists_pure_quasiFree (ι := Fin 2) J2_antisymm
  exact ⟨H, i1, i2, i3, h⟩

/-- For `J₂` the covariance is the identity: `fᵀ|J₂|f = f₀² + f₁²`. -/
lemma J2_quadratic (f : Fin 2 → ℝ) : f ⬝ᵥ absRe J2 *ᵥ f = f 0 ^ 2 + f 1 ^ 2 := by
  rw [absRe_J2]; simp [dotProduct, Fin.sum_univ_two, sq]

/-- A non-antisymmetric matrix is rejected: `!![0,1;1,0]` fails the hypothesis `Δᵀ = -Δ`. -/
lemma not_antisymm_sym : ¬ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = -!![0, 1; 1, 0]) := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp at this
  norm_num at this

end Lightlike.Rows.G2_077
