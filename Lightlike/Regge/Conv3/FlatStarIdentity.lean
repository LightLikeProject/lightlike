import Lightlike.Regge.Conv3.FlatStar

/-!
# The star identity at a point with vanishing metric gradient

The sum over the 36 incidences of the Kuhn triangulation of the derivative combination
`Einc` of the squared lengths, for a Gram matrix `G` and second derivatives `dd` of the metric, equals
`Rnum G dd / det G`, that is `det R / 2`. This is an identity between rational functions of the 6
entries of `G` and the 36 independent entries of `dd`. The six face polynomials divide their
numerators exactly (`scripts/regge/gen_flat_star.py`, which also checks the identity in exact
arithmetic), so after clearing denominators it is a polynomial identity, proved by `ring1` inside
`linear_combination`.
-/

open Real Matrix
namespace Lightlike.Regge.Conv3

/-- The Gram squared lengths of the incidence `(0, 0)` with explicit edge vectors. -/
theorem lenQ_0_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 0 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 0)` with explicit edge data. -/
theorem lenR_0_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(0, 1)` with explicit edge vectors. -/
theorem lenQ_0_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 1 = ![qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 1)` with explicit edge data. -/
theorem lenR_0_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(0, 2)` with explicit edge vectors. -/
theorem lenQ_0_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 2)` with explicit edge data. -/
theorem lenR_0_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(0, 3)` with explicit edge vectors. -/
theorem lenQ_0_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 3 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 3)` with explicit edge data. -/
theorem lenR_0_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(0, 4)` with explicit edge vectors. -/
theorem lenQ_0_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 4 = ![qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 4)` with explicit edge data. -/
theorem lenR_0_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(0, 5)` with explicit edge vectors. -/
theorem lenQ_0_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 0 5 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(0, 5)` with explicit edge data. -/
theorem lenR_0_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 0 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 0)` with explicit edge vectors. -/
theorem lenQ_1_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 0 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 0)` with explicit edge data. -/
theorem lenR_1_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 1)` with explicit edge vectors. -/
theorem lenQ_1_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 1 = ![qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 1)` with explicit edge data. -/
theorem lenR_1_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 2)` with explicit edge vectors. -/
theorem lenQ_1_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 2)` with explicit edge data. -/
theorem lenR_1_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 3)` with explicit edge vectors. -/
theorem lenQ_1_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 3 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 3)` with explicit edge data. -/
theorem lenR_1_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 4)` with explicit edge vectors. -/
theorem lenQ_1_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 4 = ![qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 4)` with explicit edge data. -/
theorem lenR_1_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(1, 5)` with explicit edge vectors. -/
theorem lenQ_1_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 1 5 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(1, 5)` with explicit edge data. -/
theorem lenR_1_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 1 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 0)` with explicit edge vectors. -/
theorem lenQ_2_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 0 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 0)` with explicit edge data. -/
theorem lenR_2_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 1)` with explicit edge vectors. -/
theorem lenQ_2_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 1 = ![qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 1)` with explicit edge data. -/
theorem lenR_2_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 2)` with explicit edge vectors. -/
theorem lenQ_2_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 2)` with explicit edge data. -/
theorem lenR_2_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 3)` with explicit edge vectors. -/
theorem lenQ_2_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 3 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 3)` with explicit edge data. -/
theorem lenR_2_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 4)` with explicit edge vectors. -/
theorem lenQ_2_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 4 = ![qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 4)` with explicit edge data. -/
theorem lenR_2_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(2, 5)` with explicit edge vectors. -/
theorem lenQ_2_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 2 5 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(2, 5)` with explicit edge data. -/
theorem lenR_2_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 2 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 0)` with explicit edge vectors. -/
theorem lenQ_3_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 0 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 0)` with explicit edge data. -/
theorem lenR_3_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 1)` with explicit edge vectors. -/
theorem lenQ_3_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 1 = ![qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 1)` with explicit edge data. -/
theorem lenR_3_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 2)` with explicit edge vectors. -/
theorem lenQ_3_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 2)` with explicit edge data. -/
theorem lenR_3_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 3)` with explicit edge vectors. -/
theorem lenQ_3_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 3 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 3)` with explicit edge data. -/
theorem lenR_3_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 4)` with explicit edge vectors. -/
theorem lenQ_3_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 4 = ![qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 4)` with explicit edge data. -/
theorem lenR_3_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(3, 5)` with explicit edge vectors. -/
theorem lenQ_3_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 3 5 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(3, 5)` with explicit edge data. -/
theorem lenR_3_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 3 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 0)` with explicit edge vectors. -/
theorem lenQ_4_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 0 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 0)` with explicit edge data. -/
theorem lenR_4_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 1)` with explicit edge vectors. -/
theorem lenQ_4_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 1 = ![qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 1)` with explicit edge data. -/
theorem lenR_4_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 2)` with explicit edge vectors. -/
theorem lenQ_4_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 2)` with explicit edge data. -/
theorem lenR_4_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 3)` with explicit edge vectors. -/
theorem lenQ_4_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 3 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 3)` with explicit edge data. -/
theorem lenR_4_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 4)` with explicit edge vectors. -/
theorem lenQ_4_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 4 = ![qf G ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 4)` with explicit edge data. -/
theorem lenR_4_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(4, 5)` with explicit edge vectors. -/
theorem lenQ_4_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 4 5 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(4, 5)` with explicit edge data. -/
theorem lenR_4_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 4 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 0)` with explicit edge vectors. -/
theorem lenQ_5_0 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 0 = ![qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 0)` with explicit edge data. -/
theorem lenR_5_0 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 0 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 1)` with explicit edge vectors. -/
theorem lenQ_5_1 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 1 = ![qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 1)` with explicit edge data. -/
theorem lenR_5_1 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 1 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 2)` with explicit edge vectors. -/
theorem lenQ_5_2 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 2 = ![qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 2)` with explicit edge data. -/
theorem lenR_5_2 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 2 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (1/2 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 3)` with explicit edge vectors. -/
theorem lenQ_5_3 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 3 = ![qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 3)` with explicit edge data. -/
theorem lenR_5_3 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 3 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(1 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 4)` with explicit edge vectors. -/
theorem lenQ_5_4 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 4 = ![qf G ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 4)` with explicit edge data. -/
theorem lenR_5_4 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 4 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (0 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (1 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num

/-- The Gram squared lengths of the incidence `(5, 5)` with explicit edge vectors. -/
theorem lenQ_5_5 (G : Fin 3 → Fin 3 → ℝ) : lenQ G 5 5 = ![qf G ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], qf G ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], qf G ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenQ, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp

/-- The second-order lengths of the incidence `(5, 5)` with explicit edge data. -/
theorem lenR_5_5 (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : lenR dd 5 5 = ![rf dd ![(0 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (-1/2 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (-1 : ℝ)], rf dd ![(-1/2 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ)] ![(-1 : ℝ), (-1 : ℝ), (0 : ℝ)], rf dd ![(-1/2 : ℝ), (-1 : ℝ), (-1/2 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)]] := by
  ext i
  fin_cases i <;> simp [lenR, incVec, kpos, kv, perms, hP, hQ, hR, hS] <;> congr 1 <;> ext j <;>
    fin_cases j <;> simp <;> norm_num


-- needs about 3.9M heartbeats (measured with `#count_heartbeats`); the cap is about twice that
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The star identity at a point with vanishing metric gradient.** For a positive definite `G`
(only the nonvanishing of the six face polynomials and of `det G` is used) and symmetric second
derivatives `dd`, the sum over the 36 incidences of `Einc (lenQ G σ h) (lenR dd σ h)` equals
`Rnum G dd / det G`. -/
theorem flat_star_identity (G : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hG : ∀ i j, G i j = G j i) (hd1 : ∀ k l i j, dd k l i j = dd l k i j)
    (hd2 : ∀ k l i j, dd k l i j = dd k l j i)
    (hP1 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2) ≠ 0) (hP2 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (2 : ℝ) * (G 0 0) * (G 1 2) + (1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 0 2) + (-1 : ℝ) * (G 0 2)^2) ≠ 0) (hP3 : ((1 : ℝ) * (G 0 0) * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2 + (-2 : ℝ) * (G 0 2) * (G 1 2) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) ≠ 0) (hP4 : ((1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) ≠ 0) (hP5 : ((1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2) ≠ 0) (hP6 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 1 2) + (2 : ℝ) * (G 0 2) * (G 1 1) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) ≠ 0)
    (hdet : (Matrix.of G).det ≠ 0) :
    ∑ σ : Fin 6, ∑ h : Fin 6, Einc (lenQ G σ h) (lenR dd σ h) =
    Rnum G dd / (Matrix.of G).det := by
  have hu1 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2) * (((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2))⁻¹ = 1 := mul_inv_cancel₀ hP1
  have hu2 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (2 : ℝ) * (G 0 0) * (G 1 2) + (1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 0 2) + (-1 : ℝ) * (G 0 2)^2) * (((1 : ℝ) * (G 0 0) * (G 1 1) + (2 : ℝ) * (G 0 0) * (G 1 2) + (1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 0 2) + (-1 : ℝ) * (G 0 2)^2))⁻¹ = 1 := mul_inv_cancel₀ hP2
  have hu3 : ((1 : ℝ) * (G 0 0) * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2 + (-2 : ℝ) * (G 0 2) * (G 1 2) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) * (((1 : ℝ) * (G 0 0) * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2 + (-2 : ℝ) * (G 0 2) * (G 1 2) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2))⁻¹ = 1 := mul_inv_cancel₀ hP3
  have hu4 : ((1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) * (((1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2))⁻¹ = 1 := mul_inv_cancel₀ hP4
  have hu5 : ((1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2) * (((1 : ℝ) * (G 0 0) * (G 2 2) + (-1 : ℝ) * (G 0 2)^2))⁻¹ = 1 := mul_inv_cancel₀ hP5
  have hu6 : ((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 1 2) + (2 : ℝ) * (G 0 2) * (G 1 1) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2) * (((1 : ℝ) * (G 0 0) * (G 1 1) + (-1 : ℝ) * (G 0 1)^2 + (-2 : ℝ) * (G 0 1) * (G 1 2) + (2 : ℝ) * (G 0 2) * (G 1 1) + (1 : ℝ) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 1 2)^2))⁻¹ = 1 := mul_inv_cancel₀ hP6
  have hdetp : ((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) = (Matrix.of G).det := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply]
    rw [hG 1 0, hG 2 0, hG 2 1]
    ring
  rw [eq_div_iff hdet, ← hdetp]
  simp only [Rnum, Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.sum_univ_three]
  simp (config := { maxSteps := 100000000 }) only [Fin.sum_univ_six, lenQ_0_0, lenR_0_0, lenQ_0_1, lenR_0_1, lenQ_0_2, lenR_0_2, lenQ_0_3, lenR_0_3, lenQ_0_4, lenR_0_4, lenQ_0_5, lenR_0_5, lenQ_1_0, lenR_1_0, lenQ_1_1, lenR_1_1, lenQ_1_2, lenR_1_2, lenQ_1_3, lenR_1_3, lenQ_1_4, lenR_1_4, lenQ_1_5, lenR_1_5, lenQ_2_0, lenR_2_0, lenQ_2_1, lenR_2_1, lenQ_2_2, lenR_2_2, lenQ_2_3, lenR_2_3, lenQ_2_4, lenR_2_4, lenQ_2_5, lenR_2_5, lenQ_3_0, lenR_3_0, lenQ_3_1, lenR_3_1, lenQ_3_2, lenR_3_2, lenQ_3_3, lenR_3_3, lenQ_3_4, lenR_3_4, lenQ_3_5, lenR_3_5, lenQ_4_0, lenR_4_0, lenQ_4_1, lenR_4_1, lenQ_4_2, lenR_4_2, lenQ_4_3, lenR_4_3, lenQ_4_4, lenR_4_4, lenQ_4_5, lenR_4_5, lenQ_5_0, lenR_5_0, lenQ_5_1, lenR_5_1, lenQ_5_2, lenR_5_2, lenQ_5_3, lenR_5_3, lenQ_5_4, lenR_5_4, lenQ_5_5, lenR_5_5, Einc, NPoly, NPoly', PPoly,
    PPoly', qf, rf, ddq, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, div_eq_mul_inv]
  rw [hG 1 0, hG 2 0, hG 2 1]
  simp only [hd1 1 0, hd1 2 0, hd1 2 1, hd2 _ _ 1 0, hd2 _ _ 2 0, hd2 _ _ 2 1]
  linear_combination (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/8 : ℝ) * (G 0 0) * (dd 0 0 1 1) + (-1/4 : ℝ) * (G 0 0) * (dd 0 1 1 1) + (-5/24 : ℝ) * (G 0 0) * (dd 1 1 1 1) + (5/12 : ℝ) * (G 0 1) * (dd 0 0 0 1) + (1/12 : ℝ) * (G 0 1) * (dd 0 0 1 1) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 0 0) + (1/3 : ℝ) * (G 0 1) * (dd 0 1 0 1) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 1 1) + (1/12 : ℝ) * (G 0 1) * (dd 1 1 0 0) + (5/12 : ℝ) * (G 0 1) * (dd 1 1 0 1) + (-5/24 : ℝ) * (G 1 1) * (dd 0 0 0 0) + (-1/4 : ℝ) * (G 1 1) * (dd 0 1 0 0) + (-1/8 : ℝ) * (G 1 1) * (dd 1 1 0 0))) * hu1 + (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/4 : ℝ) * (G 0 0) * (dd 0 0 1 1) + (-1/2 : ℝ) * (G 0 0) * (dd 0 0 1 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 0 2 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 1 1 1) + (-1/2 : ℝ) * (G 0 0) * (dd 0 1 1 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 1 2 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 2 1 1) + (-1/2 : ℝ) * (G 0 0) * (dd 0 2 1 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 2 2 2) + (-5/24 : ℝ) * (G 0 0) * (dd 1 1 1 1) + (-5/12 : ℝ) * (G 0 0) * (dd 1 1 1 2) + (-5/24 : ℝ) * (G 0 0) * (dd 1 1 2 2) + (-5/12 : ℝ) * (G 0 0) * (dd 1 2 1 1) + (-5/6 : ℝ) * (G 0 0) * (dd 1 2 1 2) + (-5/12 : ℝ) * (G 0 0) * (dd 1 2 2 2) + (-5/24 : ℝ) * (G 0 0) * (dd 2 2 1 1) + (-5/12 : ℝ) * (G 0 0) * (dd 2 2 1 2) + (-5/24 : ℝ) * (G 0 0) * (dd 2 2 2 2) + (1/6 : ℝ) * (G 0 1) * (dd 0 0 0 1) + (1/6 : ℝ) * (G 0 1) * (dd 0 0 0 2) + (-1/6 : ℝ) * (G 0 1) * (dd 0 0 1 1) + (-1/3 : ℝ) * (G 0 1) * (dd 0 0 1 2) + (-1/6 : ℝ) * (G 0 1) * (dd 0 0 2 2) + (1/6 : ℝ) * (G 0 1) * (dd 0 1 0 0) + (1/3 : ℝ) * (G 0 1) * (dd 0 1 0 1) + (1/3 : ℝ) * (G 0 1) * (dd 0 1 0 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 1 1) + (-1/6 : ℝ) * (G 0 1) * (dd 0 1 1 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 2 2) + (1/6 : ℝ) * (G 0 1) * (dd 0 2 0 0) + (1/3 : ℝ) * (G 0 1) * (dd 0 2 0 1) + (1/3 : ℝ) * (G 0 1) * (dd 0 2 0 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 2 1 1) + (-1/6 : ℝ) * (G 0 1) * (dd 0 2 1 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 2 2 2) + (1/12 : ℝ) * (G 0 1) * (dd 1 1 0 0) + (5/12 : ℝ) * (G 0 1) * (dd 1 1 0 1) + (5/12 : ℝ) * (G 0 1) * (dd 1 1 0 2) + (1/6 : ℝ) * (G 0 1) * (dd 1 2 0 0) + (5/6 : ℝ) * (G 0 1) * (dd 1 2 0 1) + (5/6 : ℝ) * (G 0 1) * (dd 1 2 0 2) + (1/12 : ℝ) * (G 0 1) * (dd 2 2 0 0) + (5/12 : ℝ) * (G 0 1) * (dd 2 2 0 1) + (5/12 : ℝ) * (G 0 1) * (dd 2 2 0 2) + (1/6 : ℝ) * (G 0 2) * (dd 0 0 0 1) + (1/6 : ℝ) * (G 0 2) * (dd 0 0 0 2) + (-1/6 : ℝ) * (G 0 2) * (dd 0 0 1 1) + (-1/3 : ℝ) * (G 0 2) * (dd 0 0 1 2) + (-1/6 : ℝ) * (G 0 2) * (dd 0 0 2 2) + (1/6 : ℝ) * (G 0 2) * (dd 0 1 0 0) + (1/3 : ℝ) * (G 0 2) * (dd 0 1 0 1) + (1/3 : ℝ) * (G 0 2) * (dd 0 1 0 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 1 1 1) + (-1/6 : ℝ) * (G 0 2) * (dd 0 1 1 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 1 2 2) + (1/6 : ℝ) * (G 0 2) * (dd 0 2 0 0) + (1/3 : ℝ) * (G 0 2) * (dd 0 2 0 1) + (1/3 : ℝ) * (G 0 2) * (dd 0 2 0 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 1 1) + (-1/6 : ℝ) * (G 0 2) * (dd 0 2 1 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 2 2) + (1/12 : ℝ) * (G 0 2) * (dd 1 1 0 0) + (5/12 : ℝ) * (G 0 2) * (dd 1 1 0 1) + (5/12 : ℝ) * (G 0 2) * (dd 1 1 0 2) + (1/6 : ℝ) * (G 0 2) * (dd 1 2 0 0) + (5/6 : ℝ) * (G 0 2) * (dd 1 2 0 1) + (5/6 : ℝ) * (G 0 2) * (dd 1 2 0 2) + (1/12 : ℝ) * (G 0 2) * (dd 2 2 0 0) + (5/12 : ℝ) * (G 0 2) * (dd 2 2 0 1) + (5/12 : ℝ) * (G 0 2) * (dd 2 2 0 2) + (-1/12 : ℝ) * (G 1 1) * (dd 0 0 0 0) + (-1/8 : ℝ) * (G 1 1) * (dd 1 1 0 0) + (-1/4 : ℝ) * (G 1 1) * (dd 1 2 0 0) + (-1/8 : ℝ) * (G 1 1) * (dd 2 2 0 0) + (-1/6 : ℝ) * (G 1 2) * (dd 0 0 0 0) + (-1/4 : ℝ) * (G 1 2) * (dd 1 1 0 0) + (-1/2 : ℝ) * (G 1 2) * (dd 1 2 0 0) + (-1/4 : ℝ) * (G 1 2) * (dd 2 2 0 0) + (-1/12 : ℝ) * (G 2 2) * (dd 0 0 0 0) + (-1/8 : ℝ) * (G 2 2) * (dd 1 1 0 0) + (-1/4 : ℝ) * (G 2 2) * (dd 1 2 0 0) + (-1/8 : ℝ) * (G 2 2) * (dd 2 2 0 0))) * hu2 + (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/8 : ℝ) * (G 0 0) * (dd 0 0 2 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 1 2 2) + (-1/8 : ℝ) * (G 0 0) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 0 0) * (dd 2 2 2 2) + (-1/4 : ℝ) * (G 0 1) * (dd 0 0 2 2) + (-1/2 : ℝ) * (G 0 1) * (dd 0 1 2 2) + (-1/4 : ℝ) * (G 0 1) * (dd 1 1 2 2) + (-1/6 : ℝ) * (G 0 1) * (dd 2 2 2 2) + (5/12 : ℝ) * (G 0 2) * (dd 0 0 0 2) + (5/12 : ℝ) * (G 0 2) * (dd 0 0 1 2) + (1/12 : ℝ) * (G 0 2) * (dd 0 0 2 2) + (5/6 : ℝ) * (G 0 2) * (dd 0 1 0 2) + (5/6 : ℝ) * (G 0 2) * (dd 0 1 1 2) + (1/6 : ℝ) * (G 0 2) * (dd 0 1 2 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 0 0) + (-1/6 : ℝ) * (G 0 2) * (dd 0 2 0 1) + (1/3 : ℝ) * (G 0 2) * (dd 0 2 0 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 1 1) + (1/3 : ℝ) * (G 0 2) * (dd 0 2 1 2) + (1/6 : ℝ) * (G 0 2) * (dd 0 2 2 2) + (5/12 : ℝ) * (G 0 2) * (dd 1 1 0 2) + (5/12 : ℝ) * (G 0 2) * (dd 1 1 1 2) + (1/12 : ℝ) * (G 0 2) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 0 2) * (dd 1 2 0 0) + (-1/6 : ℝ) * (G 0 2) * (dd 1 2 0 1) + (1/3 : ℝ) * (G 0 2) * (dd 1 2 0 2) + (-1/12 : ℝ) * (G 0 2) * (dd 1 2 1 1) + (1/3 : ℝ) * (G 0 2) * (dd 1 2 1 2) + (1/6 : ℝ) * (G 0 2) * (dd 1 2 2 2) + (-1/6 : ℝ) * (G 0 2) * (dd 2 2 0 0) + (-1/3 : ℝ) * (G 0 2) * (dd 2 2 0 1) + (1/6 : ℝ) * (G 0 2) * (dd 2 2 0 2) + (-1/6 : ℝ) * (G 0 2) * (dd 2 2 1 1) + (1/6 : ℝ) * (G 0 2) * (dd 2 2 1 2) + (-1/8 : ℝ) * (G 1 1) * (dd 0 0 2 2) + (-1/4 : ℝ) * (G 1 1) * (dd 0 1 2 2) + (-1/8 : ℝ) * (G 1 1) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 1 1) * (dd 2 2 2 2) + (5/12 : ℝ) * (G 1 2) * (dd 0 0 0 2) + (5/12 : ℝ) * (G 1 2) * (dd 0 0 1 2) + (1/12 : ℝ) * (G 1 2) * (dd 0 0 2 2) + (5/6 : ℝ) * (G 1 2) * (dd 0 1 0 2) + (5/6 : ℝ) * (G 1 2) * (dd 0 1 1 2) + (1/6 : ℝ) * (G 1 2) * (dd 0 1 2 2) + (-1/12 : ℝ) * (G 1 2) * (dd 0 2 0 0) + (-1/6 : ℝ) * (G 1 2) * (dd 0 2 0 1) + (1/3 : ℝ) * (G 1 2) * (dd 0 2 0 2) + (-1/12 : ℝ) * (G 1 2) * (dd 0 2 1 1) + (1/3 : ℝ) * (G 1 2) * (dd 0 2 1 2) + (1/6 : ℝ) * (G 1 2) * (dd 0 2 2 2) + (5/12 : ℝ) * (G 1 2) * (dd 1 1 0 2) + (5/12 : ℝ) * (G 1 2) * (dd 1 1 1 2) + (1/12 : ℝ) * (G 1 2) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 0 0) + (-1/6 : ℝ) * (G 1 2) * (dd 1 2 0 1) + (1/3 : ℝ) * (G 1 2) * (dd 1 2 0 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 1 1) + (1/3 : ℝ) * (G 1 2) * (dd 1 2 1 2) + (1/6 : ℝ) * (G 1 2) * (dd 1 2 2 2) + (-1/6 : ℝ) * (G 1 2) * (dd 2 2 0 0) + (-1/3 : ℝ) * (G 1 2) * (dd 2 2 0 1) + (1/6 : ℝ) * (G 1 2) * (dd 2 2 0 2) + (-1/6 : ℝ) * (G 1 2) * (dd 2 2 1 1) + (1/6 : ℝ) * (G 1 2) * (dd 2 2 1 2) + (-5/24 : ℝ) * (G 2 2) * (dd 0 0 0 0) + (-5/12 : ℝ) * (G 2 2) * (dd 0 0 0 1) + (-5/24 : ℝ) * (G 2 2) * (dd 0 0 1 1) + (-5/12 : ℝ) * (G 2 2) * (dd 0 1 0 0) + (-5/6 : ℝ) * (G 2 2) * (dd 0 1 0 1) + (-5/12 : ℝ) * (G 2 2) * (dd 0 1 1 1) + (-1/4 : ℝ) * (G 2 2) * (dd 0 2 0 0) + (-1/2 : ℝ) * (G 2 2) * (dd 0 2 0 1) + (-1/4 : ℝ) * (G 2 2) * (dd 0 2 1 1) + (-5/24 : ℝ) * (G 2 2) * (dd 1 1 0 0) + (-5/12 : ℝ) * (G 2 2) * (dd 1 1 0 1) + (-5/24 : ℝ) * (G 2 2) * (dd 1 1 1 1) + (-1/4 : ℝ) * (G 2 2) * (dd 1 2 0 0) + (-1/2 : ℝ) * (G 2 2) * (dd 1 2 0 1) + (-1/4 : ℝ) * (G 2 2) * (dd 1 2 1 1) + (-1/4 : ℝ) * (G 2 2) * (dd 2 2 0 0) + (-1/2 : ℝ) * (G 2 2) * (dd 2 2 0 1) + (-1/4 : ℝ) * (G 2 2) * (dd 2 2 1 1))) * hu3 + (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/8 : ℝ) * (G 1 1) * (dd 1 1 2 2) + (-1/4 : ℝ) * (G 1 1) * (dd 1 2 2 2) + (-5/24 : ℝ) * (G 1 1) * (dd 2 2 2 2) + (5/12 : ℝ) * (G 1 2) * (dd 1 1 1 2) + (1/12 : ℝ) * (G 1 2) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 1 1) + (1/3 : ℝ) * (G 1 2) * (dd 1 2 1 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 2 2) + (1/12 : ℝ) * (G 1 2) * (dd 2 2 1 1) + (5/12 : ℝ) * (G 1 2) * (dd 2 2 1 2) + (-5/24 : ℝ) * (G 2 2) * (dd 1 1 1 1) + (-1/4 : ℝ) * (G 2 2) * (dd 1 2 1 1) + (-1/8 : ℝ) * (G 2 2) * (dd 2 2 1 1))) * hu4 + (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/8 : ℝ) * (G 0 0) * (dd 0 0 2 2) + (-1/4 : ℝ) * (G 0 0) * (dd 0 2 2 2) + (-5/24 : ℝ) * (G 0 0) * (dd 2 2 2 2) + (5/12 : ℝ) * (G 0 2) * (dd 0 0 0 2) + (1/12 : ℝ) * (G 0 2) * (dd 0 0 2 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 0 0) + (1/3 : ℝ) * (G 0 2) * (dd 0 2 0 2) + (-1/12 : ℝ) * (G 0 2) * (dd 0 2 2 2) + (1/12 : ℝ) * (G 0 2) * (dd 2 2 0 0) + (5/12 : ℝ) * (G 0 2) * (dd 2 2 0 2) + (-5/24 : ℝ) * (G 2 2) * (dd 0 0 0 0) + (-1/4 : ℝ) * (G 2 2) * (dd 0 2 0 0) + (-1/8 : ℝ) * (G 2 2) * (dd 2 2 0 0))) * hu5 + (((1 : ℝ) * (G 0 0) * (G 1 1) * (G 2 2) + (-1 : ℝ) * (G 0 0) * (G 1 2)^2 + (-1 : ℝ) * (G 0 1)^2 * (G 2 2) + (2 : ℝ) * (G 0 1) * (G 0 2) * (G 1 2) + (-1 : ℝ) * (G 0 2)^2 * (G 1 1)) * ((-1/8 : ℝ) * (G 0 0) * (dd 0 0 1 1) + (-1/4 : ℝ) * (G 0 0) * (dd 0 2 1 1) + (-1/12 : ℝ) * (G 0 0) * (dd 1 1 1 1) + (-1/8 : ℝ) * (G 0 0) * (dd 2 2 1 1) + (5/12 : ℝ) * (G 0 1) * (dd 0 0 0 1) + (1/12 : ℝ) * (G 0 1) * (dd 0 0 1 1) + (5/12 : ℝ) * (G 0 1) * (dd 0 0 1 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 0 0) + (1/3 : ℝ) * (G 0 1) * (dd 0 1 0 1) + (-1/6 : ℝ) * (G 0 1) * (dd 0 1 0 2) + (1/6 : ℝ) * (G 0 1) * (dd 0 1 1 1) + (1/3 : ℝ) * (G 0 1) * (dd 0 1 1 2) + (-1/12 : ℝ) * (G 0 1) * (dd 0 1 2 2) + (5/6 : ℝ) * (G 0 1) * (dd 0 2 0 1) + (1/6 : ℝ) * (G 0 1) * (dd 0 2 1 1) + (5/6 : ℝ) * (G 0 1) * (dd 0 2 1 2) + (-1/6 : ℝ) * (G 0 1) * (dd 1 1 0 0) + (1/6 : ℝ) * (G 0 1) * (dd 1 1 0 1) + (-1/3 : ℝ) * (G 0 1) * (dd 1 1 0 2) + (1/6 : ℝ) * (G 0 1) * (dd 1 1 1 2) + (-1/6 : ℝ) * (G 0 1) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 0 1) * (dd 1 2 0 0) + (1/3 : ℝ) * (G 0 1) * (dd 1 2 0 1) + (-1/6 : ℝ) * (G 0 1) * (dd 1 2 0 2) + (1/6 : ℝ) * (G 0 1) * (dd 1 2 1 1) + (1/3 : ℝ) * (G 0 1) * (dd 1 2 1 2) + (-1/12 : ℝ) * (G 0 1) * (dd 1 2 2 2) + (5/12 : ℝ) * (G 0 1) * (dd 2 2 0 1) + (1/12 : ℝ) * (G 0 1) * (dd 2 2 1 1) + (5/12 : ℝ) * (G 0 1) * (dd 2 2 1 2) + (-1/4 : ℝ) * (G 0 2) * (dd 0 0 1 1) + (-1/2 : ℝ) * (G 0 2) * (dd 0 2 1 1) + (-1/6 : ℝ) * (G 0 2) * (dd 1 1 1 1) + (-1/4 : ℝ) * (G 0 2) * (dd 2 2 1 1) + (-5/24 : ℝ) * (G 1 1) * (dd 0 0 0 0) + (-5/12 : ℝ) * (G 1 1) * (dd 0 0 0 2) + (-5/24 : ℝ) * (G 1 1) * (dd 0 0 2 2) + (-1/4 : ℝ) * (G 1 1) * (dd 0 1 0 0) + (-1/2 : ℝ) * (G 1 1) * (dd 0 1 0 2) + (-1/4 : ℝ) * (G 1 1) * (dd 0 1 2 2) + (-5/12 : ℝ) * (G 1 1) * (dd 0 2 0 0) + (-5/6 : ℝ) * (G 1 1) * (dd 0 2 0 2) + (-5/12 : ℝ) * (G 1 1) * (dd 0 2 2 2) + (-1/4 : ℝ) * (G 1 1) * (dd 1 1 0 0) + (-1/2 : ℝ) * (G 1 1) * (dd 1 1 0 2) + (-1/4 : ℝ) * (G 1 1) * (dd 1 1 2 2) + (-1/4 : ℝ) * (G 1 1) * (dd 1 2 0 0) + (-1/2 : ℝ) * (G 1 1) * (dd 1 2 0 2) + (-1/4 : ℝ) * (G 1 1) * (dd 1 2 2 2) + (-5/24 : ℝ) * (G 1 1) * (dd 2 2 0 0) + (-5/12 : ℝ) * (G 1 1) * (dd 2 2 0 2) + (-5/24 : ℝ) * (G 1 1) * (dd 2 2 2 2) + (5/12 : ℝ) * (G 1 2) * (dd 0 0 0 1) + (1/12 : ℝ) * (G 1 2) * (dd 0 0 1 1) + (5/12 : ℝ) * (G 1 2) * (dd 0 0 1 2) + (-1/12 : ℝ) * (G 1 2) * (dd 0 1 0 0) + (1/3 : ℝ) * (G 1 2) * (dd 0 1 0 1) + (-1/6 : ℝ) * (G 1 2) * (dd 0 1 0 2) + (1/6 : ℝ) * (G 1 2) * (dd 0 1 1 1) + (1/3 : ℝ) * (G 1 2) * (dd 0 1 1 2) + (-1/12 : ℝ) * (G 1 2) * (dd 0 1 2 2) + (5/6 : ℝ) * (G 1 2) * (dd 0 2 0 1) + (1/6 : ℝ) * (G 1 2) * (dd 0 2 1 1) + (5/6 : ℝ) * (G 1 2) * (dd 0 2 1 2) + (-1/6 : ℝ) * (G 1 2) * (dd 1 1 0 0) + (1/6 : ℝ) * (G 1 2) * (dd 1 1 0 1) + (-1/3 : ℝ) * (G 1 2) * (dd 1 1 0 2) + (1/6 : ℝ) * (G 1 2) * (dd 1 1 1 2) + (-1/6 : ℝ) * (G 1 2) * (dd 1 1 2 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 0 0) + (1/3 : ℝ) * (G 1 2) * (dd 1 2 0 1) + (-1/6 : ℝ) * (G 1 2) * (dd 1 2 0 2) + (1/6 : ℝ) * (G 1 2) * (dd 1 2 1 1) + (1/3 : ℝ) * (G 1 2) * (dd 1 2 1 2) + (-1/12 : ℝ) * (G 1 2) * (dd 1 2 2 2) + (5/12 : ℝ) * (G 1 2) * (dd 2 2 0 1) + (1/12 : ℝ) * (G 1 2) * (dd 2 2 1 1) + (5/12 : ℝ) * (G 1 2) * (dd 2 2 1 2) + (-1/8 : ℝ) * (G 2 2) * (dd 0 0 1 1) + (-1/4 : ℝ) * (G 2 2) * (dd 0 2 1 1) + (-1/12 : ℝ) * (G 2 2) * (dd 1 1 1 1) + (-1/8 : ℝ) * (G 2 2) * (dd 2 2 1 1))) * hu6

end Lightlike.Regge.Conv3
