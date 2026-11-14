module

public import Lightlike.SU2.Differential

/-!
# The differential preserves brackets

Stage C, part 3, of group-level completeness (`Completeness.lean`). The basis
`Z = diag(i, -i)`, `Y = [[0,-1],[1,0]]`, `X = [[0,i],[i,0]]` of `su(2)` has
`[Z,Y] = -2X`, `[Z,X] = 2Y`, `[Y,X] = -2Z`.

For a continuous `ρ`, `brackets` proves the same relations for `dρ Z, dρ Y, dρ X`.

* `dρ_bracket_of_Ad`: if `exp(sB) C exp(-sB) = cos(2s) C + sin(2s) D` for all `s`, then
  `[dρ B, dρ C] = 2 dρ D`. Conjugation commutes with `exp` on both sides, `dρ` is linear, and
  differentiating at `s = 0` gives the bracket.
* `Ad_Z_Y`, `Ad_Z_X`, `Ad_Y_X`: the three explicit adjoint formulas (checked in SymPy first).

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 3 (Lie algebras; su(2) and its basis).
-/

@[expose] public section

open Matrix Real Filter Topology

namespace Lightlike.SU2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `suZ = iσ_z`, a basis element of `su(2)` (with `suY`, `suX`). -/
def suZ : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]
/-- `suY = -iσ_y`, a basis element of `su(2)`. -/
def suY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]
/-- `suX = iσ_x`, a basis element of `su(2)`. -/
def suX : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]

lemma isSu2_Z : IsSu2 suZ :=
  ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [suZ, conjTranspose_apply],
    by simp [suZ, trace, Fin.sum_univ_two]⟩
lemma isSu2_Y : IsSu2 suY :=
  ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [suY, conjTranspose_apply],
    by simp [suY, trace, Fin.sum_univ_two]⟩
lemma isSu2_X : IsSu2 suX :=
  ⟨by ext i j; fin_cases i <;> fin_cases j <;> simp [suX, conjTranspose_apply],
    by simp [suX, trace, Fin.sum_univ_two]⟩

lemma sqNorm_Z : sqNorm suZ = 1 := by simp [sqNorm, suZ, det_fin_two]
lemma sqNorm_Y : sqNorm suY = 1 := by simp [sqNorm, suY, det_fin_two]
lemma sqNorm_X : sqNorm suX = 1 := by simp [sqNorm, suX, det_fin_two]

/-- For `B ∈ su(2)` with `det B = 1`: `exp(tB) = cos t + (sin t) B`. -/
lemma Γ_coe_unit {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : IsSu2 B) (hB1 : sqNorm B = 1) (t : ℝ) :
    (Γ B hB t : Matrix (Fin 2) (Fin 2) ℂ) = cos t • (1 : Matrix (Fin 2) (Fin 2) ℂ) + sin t • B := by
  rw [Γ_coe, exp_smul_of_pos hB (by rw [hB1]; norm_num), hB1, Real.sqrt_one, mul_one, div_one]

lemma Γ_mul_neg {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : IsSu2 B) (s : ℝ) :
    (Γ B hB s : Matrix (Fin 2) (Fin 2) ℂ) * (Γ B hB (-s) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [← Submonoid.coe_mul, ← Γ_add, add_neg_cancel, Γ_zero]; rfl

variable {d : ℕ} [NeZero d] {ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ}

omit [NeZero d] in
lemma rho_Γ_mul_neg (hρ : Continuous ρ) {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : IsSu2 B) (s : ℝ) :
    NormedSpace.exp (s • dρ ρ B) * NormedSpace.exp ((-s) • dρ ρ B) = 1 := by
  rw [← rho_Γ hρ hB, ← rho_Γ hρ hB, ← map_mul, ← Γ_add, add_neg_cancel, Γ_zero, map_one]

/-- **Brackets from the adjoint action.** -/
theorem dρ_bracket_of_Ad (hρ : Continuous ρ) {B C D : Matrix (Fin 2) (Fin 2) ℂ} (hB : IsSu2 B)
    (hC : IsSu2 C) (hD : IsSu2 D)
    (hAd : ∀ s : ℝ, (Γ B hB s : Matrix (Fin 2) (Fin 2) ℂ) * C * (Γ B hB (-s)) =
      cos (2 * s) • C + sin (2 * s) • D) :
    dρ ρ B * dρ ρ C - dρ ρ C * dρ ρ B = (2 : ℝ) • dρ ρ D := by
  -- `dρ` of the conjugated element, computed two ways
  have hK : ∀ s : ℝ, IsSu2 (cos (2 * s) • C + sin (2 * s) • D) :=
    fun s => (hC.smul _).add (hD.smul _)
  have hconj : ∀ s : ℝ, NormedSpace.exp (s • dρ ρ B) * dρ ρ C * NormedSpace.exp ((-s) • dρ ρ B) =
      cos (2 * s) • dρ ρ C + sin (2 * s) • dρ ρ D := by
    intro s
    rw [← dρ_smul hρ hC, ← dρ_smul hρ hD, ← dρ_add hρ (hC.smul _) (hD.smul _)]
    apply exp_smul_injective
    intro t
    -- in SU(2): `Γ_K(t) = Γ_B(s) Γ_C(t) Γ_B(-s)`
    have hU : (Γ B hB s : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = Γ B hB (-s) :=
      Matrix.inv_eq_right_inv (Γ_mul_neg hB s)
    have hgrp : Γ (cos (2 * s) • C + sin (2 * s) • D) (hK s) t =
        Γ B hB s * Γ C hC t * Γ B hB (-s) := by
      apply Subtype.ext
      set U := (Γ B hB s : Matrix (Fin 2) (Fin 2) ℂ) with hUdef
      rw [Γ_coe, ← hAd s, Submonoid.coe_mul, Submonoid.coe_mul, Γ_coe hC, ← hU, ← hUdef,
        show t • (U * C * U⁻¹) = U * (t • C) * U⁻¹ by rw [Matrix.mul_smul, Matrix.smul_mul]]
      exact Matrix.exp_conj _ _ ⟨⟨_, _, Γ_mul_neg hB s, mul_eq_one_comm.mp (Γ_mul_neg hB s)⟩, rfl⟩
    have hV : (NormedSpace.exp (s • dρ ρ B))⁻¹ = NormedSpace.exp ((-s) • dρ ρ B) :=
      Matrix.inv_eq_right_inv (rho_Γ_mul_neg hρ hB s)
    rw [← rho_Γ hρ (hK s), hgrp, map_mul, map_mul, rho_Γ hρ hB, rho_Γ hρ hC, rho_Γ hρ hB, ← hV,
      show t • (NormedSpace.exp (s • dρ ρ B) * dρ ρ C * (NormedSpace.exp (s • dρ ρ B))⁻¹) =
        NormedSpace.exp (s • dρ ρ B) * (t • dρ ρ C) * (NormedSpace.exp (s • dρ ρ B))⁻¹ by
          rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact Matrix.exp_conj _ _ ⟨⟨_, _, rho_Γ_mul_neg hρ hB s,
      mul_eq_one_comm.mp (rho_Γ_mul_neg hρ hB s)⟩, rfl⟩
  -- differentiate at `s = 0`
  have hL : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • dρ ρ B) * dρ ρ C *
      NormedSpace.exp ((-s) • dρ ρ B)) (dρ ρ B * dρ ρ C - dρ ρ C * dρ ρ B) 0 := by
    have e1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (dρ ρ B) 0
    have e2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • dρ ρ B))
        (NormedSpace.exp ((-0 : ℝ) • dρ ρ B) * (-dρ ρ B)) 0 := by
      have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-dρ ρ B) 0
      simp only [smul_neg, neg_smul] at this ⊢
      exact this
    convert (e1.mul_const (dρ ρ C)).mul e2 using 1
    all_goals first
      | rfl
      | (simp only [zero_smul, neg_zero, NormedSpace.exp_zero, mul_one, one_mul]; noncomm_ring)
  have hR : HasDerivAt (fun s : ℝ => cos (2 * s) • dρ ρ C + sin (2 * s) • dρ ρ D)
      ((2 : ℝ) • dρ ρ D) 0 := by
    have c1 : HasDerivAt (fun s : ℝ => cos (2 * s)) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).cos
    have c2 : HasDerivAt (fun s : ℝ => sin (2 * s)) 2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).sin
    convert (c1.smul_const (dρ ρ C)).add (c2.smul_const (dρ ρ D)) using 1
    all_goals first
      | rfl
      | simp
  rw [show (fun s : ℝ => NormedSpace.exp (s • dρ ρ B) * dρ ρ C * NormedSpace.exp ((-s) • dρ ρ B)) =
    fun s => cos (2 * s) • dρ ρ C + sin (2 * s) • dρ ρ D from funext hconj] at hL
  exact hL.unique hR

/-! ## The three adjoint formulas -/

lemma I_cube : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring

lemma Ad_Z_Y (s : ℝ) : (Γ suZ isSu2_Z s : Matrix (Fin 2) (Fin 2) ℂ) * suY * (Γ suZ isSu2_Z (-s)) =
    cos (2 * s) • suY + sin (2 * s) • (-suX) := by
  rw [Γ_coe_unit isSu2_Z sqNorm_Z, Γ_coe_unit isSu2_Z sqNorm_Z, cos_neg, sin_neg, cos_two_mul,
    sin_two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    (try simp only [Complex.I_sq]) <;>
    first
      | linear_combination (Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination -(Complex.sin_sq_add_cos_sq (s : ℂ))

lemma Ad_Z_X (s : ℝ) : (Γ suZ isSu2_Z s : Matrix (Fin 2) (Fin 2) ℂ) * suX * (Γ suZ isSu2_Z (-s)) =
    cos (2 * s) • suX + sin (2 * s) • suY := by
  rw [Γ_coe_unit isSu2_Z sqNorm_Z, Γ_coe_unit isSu2_Z sqNorm_Z, cos_neg, sin_neg, cos_two_mul,
    sin_two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    (try simp only [Complex.I_sq, I_cube]) <;>
    first
      | linear_combination (Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination -(Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination Complex.I * (Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination -Complex.I * (Complex.sin_sq_add_cos_sq (s : ℂ))

lemma Ad_Y_X (s : ℝ) : (Γ suY isSu2_Y s : Matrix (Fin 2) (Fin 2) ℂ) * suX * (Γ suY isSu2_Y (-s)) =
    cos (2 * s) • suX + sin (2 * s) • (-suZ) := by
  rw [Γ_coe_unit isSu2_Y sqNorm_Y, Γ_coe_unit isSu2_Y sqNorm_Y, cos_neg, sin_neg, cos_two_mul,
    sin_two_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    first
      | linear_combination (Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination -(Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination Complex.I * (Complex.sin_sq_add_cos_sq (s : ℂ))
      | linear_combination -Complex.I * (Complex.sin_sq_add_cos_sq (s : ℂ))

lemma isSu2_neg {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : IsSu2 B) : IsSu2 (-B) := by
  simpa using hB.smul (-1)

/-- **The su(2) brackets for `dρ`**: `[Z,Y] = -2X`, `[Z,X] = 2Y`, `[Y,X] = -2Z`. -/
theorem brackets (hρ : Continuous ρ) :
    dρ ρ suZ * dρ ρ suY - dρ ρ suY * dρ ρ suZ = -(2 : ℝ) • dρ ρ suX ∧
    dρ ρ suZ * dρ ρ suX - dρ ρ suX * dρ ρ suZ = (2 : ℝ) • dρ ρ suY ∧
    dρ ρ suY * dρ ρ suX - dρ ρ suX * dρ ρ suY = -(2 : ℝ) • dρ ρ suZ := by
  have hnegX : dρ ρ (-suX) = -dρ ρ suX := by
    rw [show -suX = (-1 : ℝ) • suX by simp, dρ_smul hρ isSu2_X]; simp
  have hnegZ : dρ ρ (-suZ) = -dρ ρ suZ := by
    rw [show -suZ = (-1 : ℝ) • suZ by simp, dρ_smul hρ isSu2_Z]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [dρ_bracket_of_Ad hρ isSu2_Z isSu2_Y (isSu2_neg isSu2_X) Ad_Z_Y, hnegX, smul_neg, neg_smul]
  · exact dρ_bracket_of_Ad hρ isSu2_Z isSu2_X isSu2_Y Ad_Z_X
  · rw [dρ_bracket_of_Ad hρ isSu2_Y isSu2_X (isSu2_neg isSu2_Z) Ad_Y_X, hnegZ, smul_neg, neg_smul]

end Lightlike.SU2
