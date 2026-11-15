import Lightlike.Regge.Conv3.KuhnCore

/-!
# The algebraic core on the curvature tensor of `H² × ℝ`

The product of the hyperbolic plane with a line has the Ricci tensor `-(1 - n nᵀ)` in an
orthonormal frame whose unit vector `n` is tangent to the line, and scalar curvature `-2`.
In three dimensions the Ricci tensor fixes the curvature tensor, so `Rm ric` is the curvature of
`H² × ℝ`. With `n = (1,1,1)/√3` (the line along the body diagonal of the cube) the Ricci tensor
has rational entries, diagonal `-2/3` and off-diagonal `1/3`, and every edge class contributes.

`kuhn_regge_core` gives `-R/2 = 1` for it. Both wrong hinge weights give a different value
(`√3` and `1/√3`), so, unlike the axis-aligned `H² × ℝ` (where the three weights agree), this
example tells the correct weight `|e|` apart from `|e|²` and from `1`.
-/

open Real
namespace Lightlike.Regge.Conv3

/-- The Ricci tensor of `H² × ℝ` in a frame whose line direction is `(1,1,1)/√3`:
`-(1 - n nᵀ)`, diagonal `-2/3` and off-diagonal `1/3`. -/
noncomputable def ricH2R : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then -2 / 3 else 1 / 3

theorem ricH2R_symm (i j : Fin 3) : ricH2R i j = ricH2R j i := by
  fin_cases i <;> fin_cases j <;> simp [ricH2R]

/-- The scalar curvature of `H² × ℝ` is `-2`. -/
theorem ricH2R_scal : scal ricH2R = -2 := by
  simp only [scal, ricH2R, Fin.sum_univ_three]
  norm_num

/-- **The algebraic core for `H² × ℝ`:** the weighted sum of angle variations is `1 = -R/2`. -/
theorem h2r_core :
    ∑ σ : Fin 6, ∑ h : Fin 6, √(hbase h 0) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ricH2R σ h 0) (kds ricH2R σ h 1) (kds ricH2R σ h 2) (kds ricH2R σ h 3)
        (kds ricH2R σ h 4) (kds ricH2R σ h 5) = 1 := by
  rw [kuhn_regge_core ricH2R ricH2R_symm, ricH2R_scal]
  norm_num

/-- **Wrong-weight control (squared length) on `H² × ℝ`:** the value is `√3`, not `1`. -/
theorem h2r_wrong_weight_sq :
    ∑ σ : Fin 6, ∑ h : Fin 6, (√(hbase h 0)) ^ 2 *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ricH2R σ h 0) (kds ricH2R σ h 1) (kds ricH2R σ h 2) (kds ricH2R σ h 3)
        (kds ricH2R σ h 4) (kds ricH2R σ h 5) = √3 := by
  rw [weighted_sum (fun l => l ^ 2) ricH2R ricH2R_symm]
  have : (√3 : ℝ) ≠ 0 := by positivity
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  simp [Fin.sum_univ_six, Th, hbase, ricH2R]
  field_simp
  norm_num
  ring

/-- **Wrong-weight control (unit weight) on `H² × ℝ`:** the value is `1/√3`, not `1`. -/
theorem h2r_wrong_weight_one :
    ∑ σ : Fin 6, ∑ h : Fin 6, (1 : ℝ) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ricH2R σ h 0) (kds ricH2R σ h 1) (kds ricH2R σ h 2) (kds ricH2R σ h 3)
        (kds ricH2R σ h 4) (kds ricH2R σ h 5) = 1 / √3 := by
  rw [weighted_sum (fun _ => 1) ricH2R ricH2R_symm]
  have : (√3 : ℝ) ≠ 0 := by positivity
  simp [Fin.sum_univ_six, Th, hbase, ricH2R]
  field_simp
  norm_num
  ring

/-- Both wrong weights miss `-R/2 = 1`. -/
theorem h2r_wrong_weights_differ : (√3 : ℝ) ≠ -(scal ricH2R) / 2 ∧ (1 / √3 : ℝ) ≠ -(scal ricH2R) / 2 := by
  rw [ricH2R_scal]
  have h3 : (√3 : ℝ) ^ 2 = 3 := sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  constructor
  · intro h; nlinarith
  · intro h
    have : 1 / √3 = 1 := by linarith
    field_simp at this
    nlinarith

end Lightlike.Regge.Conv3
