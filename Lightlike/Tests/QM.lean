module

public import Lightlike.QM.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Tests for finite-dimensional quantum mechanics

A concrete system for the definitions of `Lightlike/QM/Basic.lean`: a qubit `ℂ²` with the Pauli
matrix `Z`.

* `pauliZ`: `Z = diag(1, −1)` is an observable (self-adjoint), so the hypotheses of the general
  theorems are satisfiable.
* `expectation_pauliZ_zero`: in the state `|0⟩` the Born rule gives the expectation value `1`
  (`Σ_μ μ · P(μ) = ⟨0|Z|0⟩ = 1`).
* `norm_evolve_pauliZ`: the evolution under `Z` keeps the norm of `|0⟩`.
* `sum_bornProb_unnormalised` (**wrong input**): for the unnormalised vector `2|0⟩` the "Born
  probabilities" add up to `4`, not `1`. The Born rule needs unit vectors (`State`).
-/

@[expose] public section

open Matrix

namespace Lightlike.QM.Test

/-- The qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The Pauli matrix `Z = diag(1, −1)`. -/
def pauliZMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

lemma pauliZMat_isHermitian : pauliZMat.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZMat]

/-- **`Z` is an observable** on the qubit. -/
noncomputable def pauliZ : Observable Qubit :=
  ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) pauliZMat, by
    show star (Matrix.toEuclideanCLM (𝕜 := ℂ) pauliZMat) = Matrix.toEuclideanCLM (𝕜 := ℂ) pauliZMat
    rw [← map_star]
    exact congrArg _ pauliZMat_isHermitian⟩

/-- The basis state `|0⟩`. -/
noncomputable def ket0 : Qubit := EuclideanSpace.single 0 1

lemma pauliZ_ket0 : (pauliZ : Qubit →L[ℂ] Qubit) ket0 = ket0 := by
  ext i
  fin_cases i <;> simp [pauliZ, ket0, pauliZMat, Matrix.mulVec, dotProduct]

/-- **The Born rule on a qubit**: in `|0⟩` the expectation value of `Z` is `1`. -/
theorem expectation_pauliZ_zero :
    ∑ μ : Outcome pauliZ, (μ : ℂ) * (bornProb pauliZ ket0 μ : ℂ) = 1 := by
  rw [← expectation_eq_sum, pauliZ_ket0, inner_self_eq_norm_sq_to_K]
  simp [ket0]

/-- The evolution under `Z` keeps the norm of `|0⟩` (non-vacuity of `norm_evolve`). -/
theorem norm_evolve_pauliZ (t : ℝ) : ‖(evolve pauliZ t : Qubit →L[ℂ] Qubit) ket0‖ = 1 := by
  rw [norm_evolve]
  simp [ket0]

/-- **Wrong input:** for the unnormalised vector `2|0⟩` the Born probabilities add up to `4`, not
`1`, so the Born rule is stated for unit vectors only. -/
theorem sum_bornProb_unnormalised :
    ∑ μ, bornProb pauliZ ((2 : ℂ) • ket0) μ = 4 := by
  rw [sum_bornProb_eq_norm_sq, norm_smul]
  simp [ket0]
  norm_num

end Lightlike.QM.Test
