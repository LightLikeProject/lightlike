import Mathlib

/-!
# An isometry of anti-de Sitter space moves the null directions: the factor, the angle and the sphere

The first layer of the action of the isometry group `SO(2,3)` of anti-de Sitter space on its conformal boundary (GE7).
Anti-de Sitter space `AdS₄` is the quadric `-X₀² - X₁² + X₂² + X₃² + X₄² = -1` in `ℝ^{2,3}`, and its conformal boundary is
the projectivised null cone, which is the circle times the sphere: a boundary point is a null direction
`X = (cos τ, sin τ, ω)` with an angle `τ` and a unit vector `ω`. A matrix `Λ` with `Λᵀ η' Λ = η'`,
`η' = diag(-1, -1, 1, 1, 1)`, sends such a vector to `ρ X'` with `ρ > 0` and `X'` again of the same form:

* `adsEta`, `adsSq`, `adsSq_mulVec`: the form `η'` and its square, preserved by `Λ`;
* `adsNullVec`, `adsSq_adsNullVec`: the vector `(cos τ, sin τ, ω)` is null when `|ω| = 1`;
* `adsFactor`, `adsFactor_pos`: `ρ = √((ΛX)₀² + (ΛX)₁²)` is positive;
* `adsAngle`, `adsDir`: `τ'` and `ω'` with `Λ X = ρ X'` (`mulVec_adsNullVec_eq`) and `|ω'| = 1` (`sum_sq_adsDir`).

This is the boundary of `AdS₄` as the circle times the sphere (no universal cover: the angle is taken modulo `2π`).
The action on pairs, its group law and the conformality are the next layers.

Check on a concrete matrix (`adsBoost`, the boost in the `(X₀, X₂)` plane with `cosh = 5/4`, `sinh = 3/4`): it satisfies
`Λᵀ η' Λ = η'` (`adsBoost_lorentz`) and its factor on `τ = 0`, `ω = e₁` is `2` (`adsFactor_adsBoost_zero`).
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The form `η' = diag(-1, -1, 1, 1, 1)` of `ℝ^{2,3}`. -/
def adsEta : Matrix (Fin 5) (Fin 5) ℝ := diagonal ![-1, -1, 1, 1, 1]

lemma adsEta_mul_adsEta : adsEta * adsEta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adsEta, diagonal_apply, Matrix.mul_apply]

/-- The square `-w₀² - w₁² + w₂² + w₃² + w₄²` of `ℝ^{2,3}`. -/
def adsSq (w : Fin 5 → ℝ) : ℝ := -(w 0) ^ 2 - (w 1) ^ 2 + (w 2) ^ 2 + (w 3) ^ 2 + (w 4) ^ 2

lemma adsSq_eq_dot (w : Fin 5 → ℝ) : adsSq w = w ⬝ᵥ (adsEta *ᵥ w) := by
  simp [adsSq, adsEta, mulVec_diagonal, dotProduct, Fin.sum_univ_succ]
  ring

/-- A matrix with `Λᵀ η' Λ = η'` preserves the square. -/
theorem adsSq_mulVec {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (v : Fin 5 → ℝ) :
    adsSq (Λ *ᵥ v) = adsSq v := by
  have h : Λ *ᵥ v ⬝ᵥ adsEta *ᵥ (Λ *ᵥ v) = v ⬝ᵥ (Λᵀ * adsEta * Λ) *ᵥ v := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [adsSq_eq_dot, adsSq_eq_dot, h, hΛ]

/-- The vector `(cos τ, sin τ, ω)`: a point of the projectivised null cone. -/
def adsNullVec (τ : ℝ) (ω : Fin 3 → ℝ) : Fin 5 → ℝ := ![Real.cos τ, Real.sin τ, ω 0, ω 1, ω 2]

/-- The vector `(cos τ, sin τ, ω)` is null for a unit vector `ω`. -/
theorem adsSq_adsNullVec (τ : ℝ) {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) : adsSq (adsNullVec τ ω) = 0 := by
  have h := Real.sin_sq_add_cos_sq τ
  simp only [Fin.sum_univ_three] at hω
  simp [adsSq, adsNullVec]
  nlinarith [h, hω]

/-- A matrix with `Λᵀ η' Λ = η'` is injective. -/
theorem mulVec_eq_zero {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) {v : Fin 5 → ℝ}
    (h : Λ *ᵥ v = 0) : v = 0 := by
  have h1 : (adsEta * Λᵀ * adsEta) * Λ = 1 := by
    calc (adsEta * Λᵀ * adsEta) * Λ = adsEta * (Λᵀ * adsEta * Λ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hΛ, adsEta_mul_adsEta]
  calc v = ((adsEta * Λᵀ * adsEta) * Λ) *ᵥ v := by rw [h1, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h, mulVec_zero]

/-- The factor `ρ`: the length of the first two components of `Λ X`. -/
def adsFactor (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) : ℝ :=
  Real.sqrt ((Λ *ᵥ adsNullVec τ ω) 0 ^ 2 + (Λ *ᵥ adsNullVec τ ω) 1 ^ 2)

/-- The factor `ρ` is positive. -/
theorem adsFactor_pos {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) : 0 < adsFactor Λ τ ω := by
  unfold adsFactor
  apply Real.sqrt_pos.mpr
  by_contra hle
  push Not at hle
  set w := Λ *ᵥ adsNullVec τ ω with hw
  have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have hn : adsSq w = 0 := by rw [hw, adsSq_mulVec hΛ]; exact adsSq_adsNullVec τ hω
  simp only [adsSq, h0, h1] at hn
  have h2 : w 2 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 3), sq_nonneg (w 4)]
  have h3 : w 3 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 3), sq_nonneg (w 4)]
  have h4 : w 4 = 0 := by nlinarith [sq_nonneg (w 2), sq_nonneg (w 3), sq_nonneg (w 4)]
  have hz : w = 0 := by
    ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]
  have hX := mulVec_eq_zero hΛ hz
  have := congrFun hX 0
  have := congrFun hX 1
  simp [adsNullVec] at *
  nlinarith [Real.sin_sq_add_cos_sq τ]

/-- The angle `τ'` of the image: the argument of `(ΛX)₀ + i (ΛX)₁`. -/
def adsAngle (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) : ℝ :=
  Complex.arg ⟨(Λ *ᵥ adsNullVec τ ω) 0, (Λ *ᵥ adsNullVec τ ω) 1⟩

/-- The direction `ω'` of the image: the last three components of `Λ X` over `ρ`. -/
def adsDir (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (Λ *ᵥ adsNullVec τ ω) i.succ.succ / adsFactor Λ τ ω

theorem adsFactor_eq_norm (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) :
    ‖(⟨(Λ *ᵥ adsNullVec τ ω) 0, (Λ *ᵥ adsNullVec τ ω) 1⟩ : ℂ)‖ = adsFactor Λ τ ω := by
  rw [Complex.norm_def, Complex.normSq_apply, adsFactor]
  congr 1
  ring

/-- `cos τ' = (ΛX)₀ / ρ`. -/
theorem cos_adsAngle {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    Real.cos (adsAngle Λ τ ω) = (Λ *ᵥ adsNullVec τ ω) 0 / adsFactor Λ τ ω := by
  have hρ := adsFactor_pos hΛ τ hω
  have hne : (⟨(Λ *ᵥ adsNullVec τ ω) 0, (Λ *ᵥ adsNullVec τ ω) 1⟩ : ℂ) ≠ 0 := by
    intro h
    rw [← norm_eq_zero, adsFactor_eq_norm] at h
    exact hρ.ne' h
  rw [adsAngle, Complex.cos_arg hne, adsFactor_eq_norm]

/-- `sin τ' = (ΛX)₁ / ρ`. -/
theorem sin_adsAngle {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    Real.sin (adsAngle Λ τ ω) = (Λ *ᵥ adsNullVec τ ω) 1 / adsFactor Λ τ ω := by
  have hρ := adsFactor_pos hΛ τ hω
  have hne : (⟨(Λ *ᵥ adsNullVec τ ω) 0, (Λ *ᵥ adsNullVec τ ω) 1⟩ : ℂ) ≠ 0 := by
    intro h
    rw [← norm_eq_zero, adsFactor_eq_norm] at h
    exact hρ.ne' h
  rw [adsAngle, Complex.sin_arg, adsFactor_eq_norm]

/-- `Λ (cos τ, sin τ, ω) = ρ (cos τ', sin τ', ω')`. -/
theorem mulVec_adsNullVec_eq {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    Λ *ᵥ adsNullVec τ ω = adsFactor Λ τ ω • adsNullVec (adsAngle Λ τ ω) (adsDir Λ τ ω) := by
  have hρ := (adsFactor_pos hΛ τ hω).ne'
  ext j
  fin_cases j
  · simp [adsNullVec, cos_adsAngle hΛ τ hω]; field_simp
  · simp [adsNullVec, sin_adsAngle hΛ τ hω]; field_simp
  all_goals simp [adsNullVec, adsDir]; field_simp

/-- `ω'` is again a unit vector. -/
theorem sum_sq_adsDir {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) : ∑ i, adsDir Λ τ ω i ^ 2 = 1 := by
  have hρ := adsFactor_pos hΛ τ hω
  have hn : adsSq (Λ *ᵥ adsNullVec τ ω) = 0 := by rw [adsSq_mulVec hΛ]; exact adsSq_adsNullVec τ hω
  set w := Λ *ᵥ adsNullVec τ ω with hw
  have hρ2 : adsFactor Λ τ ω ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    unfold adsFactor
    rw [← hw, Real.sq_sqrt (by positivity)]
  simp only [adsDir, div_pow, Fin.sum_univ_three, Fin.reduceSucc, ← hw]
  rw [← add_div, ← add_div, div_eq_one_iff_eq (pow_pos hρ 2).ne', hρ2]
  simp only [adsSq] at hn
  linarith

theorem adsFactor_one (τ : ℝ) (ω : Fin 3 → ℝ) : adsFactor 1 τ ω = 1 := by
  simp [adsFactor, adsNullVec]

/-- A boost in the `(X₀, X₂)` plane with `cosh = 5/4`, `sinh = 3/4`. -/
def adsBoost : Matrix (Fin 5) (Fin 5) ℝ :=
  !![5 / 4, 0, 3 / 4, 0, 0; 0, 1, 0, 0, 0; 3 / 4, 0, 5 / 4, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem adsBoost_lorentz : adsBoost ᵀ * adsEta * adsBoost = adsEta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adsBoost, adsEta, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ] <;> norm_num

/-- Non-vacuity: the boost sends `(1, 0, e₁)` to a vector with factor `2`. -/
theorem adsFactor_adsBoost_zero : adsFactor adsBoost 0 ![1, 0, 0] = 2 := by
  have : (adsBoost *ᵥ adsNullVec 0 ![1, 0, 0]) 0 = 2 := by
    simp [adsBoost, adsNullVec, mulVec, dotProduct, Fin.sum_univ_succ]
    norm_num
  have h1 : (adsBoost *ᵥ adsNullVec 0 ![1, 0, 0]) 1 = 0 := by
    simp [adsBoost, adsNullVec, mulVec, dotProduct, Fin.sum_univ_succ]
  rw [adsFactor, this, h1]
  rw [show ((2 : ℝ)) ^ 2 + 0 ^ 2 = 2 ^ 2 by ring]
  exact Real.sqrt_sq (by norm_num)

end Lightlike
