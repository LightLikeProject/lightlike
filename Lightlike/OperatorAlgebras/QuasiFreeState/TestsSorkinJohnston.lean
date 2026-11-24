import Lightlike.OperatorAlgebras.QuasiFreeState.SorkinJohnston

/-!
# Tests for the Sorkin-Johnston purity theorem

The 2-chain `0 ≺ 1` in closed form: the causal matrix is `[[0, 1], [0, 0]]`, the Pauli-Jordan matrix is
`a [[0, 1], [-1, 0]]` (`pauliJordan_chain`), and for `a ≥ 0` its absolute value is `H = a·1` (`chain_pjData`), so the
Sorkin-Johnston two-point function `Pos(iΔ) = ½ (H + iΔ)` has real part `a/2` times the identity. Wrong input (a
relation that is not a partial order): the matrix of the symmetric relation is rejected by
`not_pjData_symmetric` in `TestsPauliJordan`.
-/

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Matrix

/-- The causal matrix of the 2-chain. -/
theorem causalMatrix_chain : causalMatrix (Fin 2) = !![0, 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [causalMatrix]

/-- **The Pauli-Jordan matrix of the 2-chain in closed form**: `a [[0, 1], [-1, 0]]`. -/
theorem pauliJordan_chain (a : ℝ) : pauliJordanMatrix (Fin 2) a = !![0, a; -a, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliJordanMatrix, causalMatrix]

/-- **The absolute value `|iΔ|` of the 2-chain is `a·1`** (the hypotheses of the purity theorem). -/
theorem chain_pjData (a : ℝ) (ha : 0 ≤ a) :
    PJData (pauliJordanMatrix (Fin 2) a) (a • (1 : Matrix (Fin 2) (Fin 2) ℝ)) where
  anti := pauliJordanMatrix_anti _ a
  psd := Matrix.PosSemidef.one.smul ha
  sq := by
    rw [pauliJordan_chain]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  comm := by
    rw [pauliJordan_chain]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Lightlike.OperatorAlgebras.QuasiFreeState
