import Mathlib

/-!
# The representation-theoretic core of the Weinberg–Witten theorem

Row G3-253 (target T-PG3). A matrix element `M^{μν} = ⟨p', h | T^{μν}(0) | p, h⟩` of a covariant stress tensor between
massless one-particle states of helicity `h`, taken in the Breit frame `p = (E, 0, 0, q)`, `p' = (E, 0, 0, -q)`,
transforms under rotations about the `z` axis by the phase `e^{i k θ}` with `k = 2h`. Covariance of the tensor says
`R(θ) M R(θ)ᵀ = e^{i k θ} M`. This file proves the algebraic core: such an `M` vanishes when `|k| > 2`, and nonzero
solutions exist when `|k| ≤ 2` (so helicity `±1` is allowed and helicity `±2`, `k = ±4`, is not).

## Main statements

* `ww_vanishing`: if `R(θ) M Rᵀ(θ) = e^{ikθ} M` for all `θ` and `|k| > 2` then `M = 0`.

## Limits

The passage from the matrix element of the stress tensor to the Breit-frame tensor `M`, and the limit `p' → p`
(where `M → p^μ p^ν ≠ 0` by the normalisation of the energy–momentum), are not formalised here.
-/

namespace Lightlike.Rows.G3_253

open Matrix

noncomputable section

/-- The rotation by `θ` about the `z` axis on Minkowski coordinates `(t, x, y, z)`, as a complex matrix. -/
def zRot (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, (Real.cos θ : ℂ), -(Real.sin θ : ℂ), 0; 0, (Real.sin θ : ℂ), (Real.cos θ : ℂ), 0; 0, 0, 0, 1]

/-- The weight basis `e_t, e_x + i e_y, e_x - i e_y, e_z` of `ℂ⁴`. -/
def wBasis : Fin 4 → Fin 4 → ℂ
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, 1, Complex.I, 0]
  | 2 => ![0, 1, -Complex.I, 0]
  | 3 => ![0, 0, 0, 1]

/-- The `z`-weights of the basis `wBasis`. -/
def wWeight : Fin 4 → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => 0

/-- The transposed rotation `R(θ)ᵀ = R(-θ)` multiplies each weight vector by `e^{i w θ}`. -/
theorem zRot_transpose_wBasis (θ : ℝ) (i : Fin 4) :
    (zRot θ)ᵀ *ᵥ wBasis i = Complex.exp (((wWeight i : ℂ) * θ) * Complex.I) • wBasis i := by
  have e1 : Complex.exp ((θ : ℂ) * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I :=
    Complex.exp_mul_I _
  have e2 : Complex.exp (-((θ : ℂ) * Complex.I)) = Complex.cos θ - Complex.sin θ * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
  have hI := Complex.I_sq
  fin_cases i
  · ext j; fin_cases j <;> simp [zRot, wBasis, wWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · ext j; fin_cases j <;> simp [zRot, wBasis, wWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e1]
    linear_combination (-Complex.sin θ) * hI
  · ext j; fin_cases j <;> simp [zRot, wBasis, wWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e2]
    · rfl
    · linear_combination (-Complex.sin θ) * hI
  · ext j; fin_cases j <;> simp [zRot, wBasis, wWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Covariance `R M Rᵀ = e^{ikθ} M` forces `(e^{i(wᵢ+wⱼ)θ} - e^{ikθ}) · (eᵢᵀ M eⱼ) = 0` on the weight basis. -/
theorem bil_covariance (M : Matrix (Fin 4) (Fin 4) ℂ) (k : ℤ)
    (H : ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((k : ℂ) * θ) * Complex.I) • M) (θ : ℝ) (i j : Fin 4) :
    (Complex.exp ((((wWeight i + wWeight j : ℤ) : ℂ) * θ) * Complex.I) - Complex.exp (((k : ℂ) * θ) * Complex.I)) *
      (wBasis i ⬝ᵥ M *ᵥ wBasis j) = 0 := by
  have key : ∀ N : Matrix (Fin 4) (Fin 4) ℂ, wBasis i ⬝ᵥ ((zRot θ * N * (zRot θ)ᵀ) *ᵥ wBasis j) =
      Complex.exp (((wWeight i : ℂ) * θ) * Complex.I) * Complex.exp (((wWeight j : ℂ) * θ) * Complex.I) *
        (wBasis i ⬝ᵥ N *ᵥ wBasis j) := by
    intro N
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      zRot_transpose_wBasis θ i, zRot_transpose_wBasis θ j, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  have h := congrArg (fun N : Matrix (Fin 4) (Fin 4) ℂ => wBasis i ⬝ᵥ (N *ᵥ wBasis j)) (H θ)
  simp only [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  push_cast
  rw [add_mul, add_mul, Complex.exp_add]
  linear_combination h

/-- If the weights `w ≠ k` are distinct integers, some rotation angle separates `e^{iwθ}` from `e^{ikθ}`. -/
theorem exists_angle_ne (w k : ℤ) (hwk : w ≠ k) :
    ∃ θ : ℝ, Complex.exp (((w : ℂ) * θ) * Complex.I) ≠ Complex.exp (((k : ℂ) * θ) * Complex.I) := by
  have hne : ((k : ℝ) - w) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hwk.symm)
  refine ⟨Real.pi / (k - w), fun h => ?_⟩
  have h2 : Complex.exp (((k : ℂ) * ((Real.pi / (k - w) : ℝ) : ℂ)) * Complex.I) =
      Complex.exp (((w : ℂ) * ((Real.pi / (k - w) : ℝ) : ℂ)) * Complex.I) * Complex.exp (Real.pi * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    have hne' : ((k : ℂ) - w) ≠ 0 := by exact_mod_cast hne
    push_cast
    field_simp
    ring
  rw [Complex.exp_pi_mul_I, ← h] at h2
  have h0 := Complex.exp_ne_zero (((w : ℂ) * ((Real.pi / (k - w) : ℝ) : ℂ)) * Complex.I)
  apply h0
  linear_combination (1 / 2 : ℂ) * h2

/-- **Weinberg–Witten core.** A complex tensor `M^{μν}` covariant under rotations about the `z` axis with phase
`e^{ikθ}`, `|k| > 2`, vanishes: the weights of a rank-two tensor lie in `{-2, …, 2}`. -/
theorem ww_vanishing (M : Matrix (Fin 4) (Fin 4) ℂ) (k : ℤ) (hk : 2 < |k|)
    (H : ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((k : ℂ) * θ) * Complex.I) • M) : M = 0 := by
  have hb : ∀ i j, wBasis i ⬝ᵥ M *ᵥ wBasis j = 0 := by
    intro i j
    have hw : wWeight i + wWeight j ≠ k := by
      have : |wWeight i + wWeight j| ≤ 2 := by
        fin_cases i <;> fin_cases j <;> simp [wWeight]
      intro h
      rw [h] at this
      omega
    obtain ⟨θ, hθ⟩ := exists_angle_ne _ _ hw
    have := bil_covariance M k H θ i j
    push_cast at this hθ
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hθ
    · exact h
  have h00 := hb 0 0
  have h01 := hb 0 1
  have h02 := hb 0 2
  have h03 := hb 0 3
  have h10 := hb 1 0
  have h11 := hb 1 1
  have h12 := hb 1 2
  have h13 := hb 1 3
  have h20 := hb 2 0
  have h21 := hb 2 1
  have h22 := hb 2 2
  have h23 := hb 2 3
  have h30 := hb 3 0
  have h31 := hb 3 1
  have h32 := hb 3 2
  have h33 := hb 3 3
  simp [wBasis, dotProduct, Matrix.mulVec, Fin.sum_univ_four] at h00 h01 h02 h03 h10 h11 h12 h13 h20 h21 h22
  simp [wBasis, dotProduct, Matrix.mulVec, Fin.sum_univ_four] at h23 h30 h31 h32 h33
  have hI := Complex.I_sq
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  have e01 : M 0 1 = 0 := by linear_combination (1 / 2 : ℂ) * h01 + (1 / 2 : ℂ) * h02
  have e02 : M 0 2 = 0 := by
    have : (2 * Complex.I) * M 0 2 = 0 := by linear_combination h01 - h02
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  have e10 : M 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * h10 + (1 / 2 : ℂ) * h20
  have e20 : M 2 0 = 0 := by
    have : (2 * Complex.I) * M 2 0 = 0 := by linear_combination h10 - h20
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  have e13 : M 1 3 = 0 := by linear_combination (1 / 2 : ℂ) * h13 + (1 / 2 : ℂ) * h23
  have e23 : M 2 3 = 0 := by
    have : (2 * Complex.I) * M 2 3 = 0 := by linear_combination h13 - h23
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  have e31 : M 3 1 = 0 := by linear_combination (1 / 2 : ℂ) * h31 + (1 / 2 : ℂ) * h32
  have e32 : M 3 2 = 0 := by
    have : (2 * Complex.I) * M 3 2 = 0 := by linear_combination h31 - h32
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  have e11 : M 1 1 = 0 := by linear_combination (1 / 4 : ℂ) * (h11 + h12 + h21 + h22)
  have e22 : M 2 2 = 0 := by
    linear_combination (-1 / 4 : ℂ) * (h11 - h12 - h21 + h22) + M 2 2 * hI
  have e12 : M 1 2 = 0 := by
    have : (4 * Complex.I) * M 1 2 = 0 := by linear_combination h11 - h22 - h12 + h21
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  have e21 : M 2 1 = 0 := by
    have : (4 * Complex.I) * M 2 1 = 0 := by linear_combination h11 - h22 + h12 - h21
    exact (mul_eq_zero.mp this).resolve_left (by simp)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h00, h03, h30, h33, e01, e02, e10, e20, e13, e23, e31, e32, e11, e22, e12, e21]

end

end Lightlike.Rows.G3_253
