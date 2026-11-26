import Lightlike.Spacetime.Lorentzian

/-!
# A Lorentz transformation moves the future null directions: the factor and the action on the sphere

The first layer of the action of the Poincaré group on future null infinity (GE7). A point of future null infinity of
Minkowski space is a retarded time `u` and a direction `n` on the unit sphere, the future null direction `(1, n)`. A
Lorentz matrix `Λ` with `Λᵀ η Λ = η` and `Λ 0 0 > 0` sends the null vector `(1, n)` to a future null vector
`K (1, n')` with `K > 0` and `n'` again a unit vector:

* `minkSq`, `minkSq_mulVec`: the Minkowski square `-w₀² + |w⃗|²` is preserved by `Λ`;
* `nullVec`, `minkSq_nullVec`: the vector `(1, n)` is null when `|n| = 1`;
* `lorentz_row`: `Λ η Λᵀ = η`, so the row `(Λ 0 0, Λ 0 j)` has the same Minkowski square as the column;
* `nullDirFactor_pos`: the time component `K = (Λ (1, n))₀` is positive (Cauchy–Schwarz on the first row);
* `nullDirMap`, `nullDirFactor`: `n' = (Λ (1, n))⃗ / K` and `K`, with `mulVec_nullVec_eq`
  (`Λ (1, n) = K (1, n')`) and `sum_sq_nullDirMap` (`|n'| = 1`).

The action on the retarded time and the conformal factor on the sphere are the next layers.

Check on a concrete boost (`boostX`, rapidity with `cosh = 5/4`, `sinh = 3/4`, velocity `3/5`): it is a Lorentz matrix
(`boostX_lorentz`) and sends `(1, e₁)` to `2 (1, e₁)` and `(1, -e₁)` to `(1/2) (1, -e₁)` (`nullDirFactor_boostX_pos`,
`nullDirFactor_boostX_neg`), the Doppler factors `γ (1 ± v)`.
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The future null vector `(1, n)` of Minkowski space for a direction `n`. -/
def nullVec (n : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons 1 n

/-- The Minkowski square `-w₀² + w₁² + w₂² + w₃²`. -/
def minkSq (w : Fin 4 → ℝ) : ℝ := -(w 0) ^ 2 + ∑ i : Fin 3, (w i.succ) ^ 2

lemma minkSq_eq_dot (w : Fin 4 → ℝ) : minkSq w = w ⬝ᵥ (eta 4 *ᵥ w) := by
  simp [minkSq, eta, mulVec_diagonal, dotProduct, Fin.sum_univ_succ, etaDiag]
  ring

/-- A Lorentz matrix preserves the Minkowski square. -/
theorem minkSq_mulVec {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4) (v : Fin 4 → ℝ) :
    minkSq (Λ *ᵥ v) = minkSq v := by
  have h : Λ *ᵥ v ⬝ᵥ eta 4 *ᵥ (Λ *ᵥ v) = v ⬝ᵥ (Λᵀ * eta 4 * Λ) *ᵥ v := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [minkSq_eq_dot, minkSq_eq_dot, h, hΛ]

/-- The vector `(1, n)` is null for a unit vector `n`. -/
theorem minkSq_nullVec {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) : minkSq (nullVec n) = 0 := by
  simp [minkSq, nullVec, hn]

/-- A Lorentz matrix also satisfies `Λ η Λᵀ = η`. -/
theorem lorentz_row {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4) :
    Λ * eta 4 * Λᵀ = eta 4 := by
  have h1 : (eta 4 * Λᵀ * eta 4) * Λ = 1 := by
    calc (eta 4 * Λᵀ * eta 4) * Λ = eta 4 * (Λᵀ * eta 4 * Λ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hΛ, eta_mul_eta 4]
  have h2 : Λ * (eta 4 * Λᵀ * eta 4) = 1 := mul_eq_one_comm.mp h1
  calc Λ * eta 4 * Λᵀ = Λ * (eta 4 * Λᵀ * eta 4) * eta 4 := by
        simp only [Matrix.mul_assoc, eta_mul_eta 4, Matrix.mul_one]
    _ = eta 4 := by rw [h2, Matrix.one_mul]

/-- The first row of a Lorentz matrix: `Σ_j Λ₀ⱼ² = Λ₀₀² - 1`. -/
theorem lorentz_row_zero {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4) :
    ∑ i : Fin 3, Λ 0 i.succ ^ 2 = Λ 0 0 ^ 2 - 1 := by
  have h := congrFun (congrFun (lorentz_row hΛ) 0) 0
  simp [Matrix.mul_apply, eta, Fin.sum_univ_succ, etaDiag, Matrix.diagonal_apply] at h
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Finset.univ_eq_empty]
  simp
  nlinarith [h]

/-- The time component of `Λ (1, n)` is positive when `Λ₀₀ > 0` and `n` is a unit vector. -/
theorem mulVec_nullVec_zero_pos {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4)
    (h0 : 0 < Λ 0 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) : 0 < (Λ *ᵥ nullVec n) 0 := by
  have hexp : (Λ *ᵥ nullVec n) 0 = Λ 0 0 + ∑ i : Fin 3, Λ 0 i.succ * n i := by
    simp [mulVec, dotProduct, Fin.sum_univ_succ, nullVec]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 3 => Λ 0 i.succ) n
  rw [lorentz_row_zero hΛ, hn, mul_one] at hcs
  have hlt : (∑ i : Fin 3, Λ 0 i.succ * n i) ^ 2 < Λ 0 0 ^ 2 := by linarith
  have habs := abs_lt_of_sq_lt_sq hlt h0.le
  rw [hexp]
  linarith [(abs_lt.mp habs).1]

/-- The factor `K` with `Λ (1, n) = K (1, n')`: the time component of `Λ (1, n)`. -/
def nullDirFactor (Λ : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 3 → ℝ) : ℝ := (Λ *ᵥ nullVec n) 0

/-- The direction `n'` with `Λ (1, n) = K (1, n')`: the spatial part of `Λ (1, n)` over `K`. -/
def nullDirMap (Λ : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (Λ *ᵥ nullVec n) i.succ / nullDirFactor Λ n

/-- The factor `K` is positive. -/
theorem nullDirFactor_pos {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4)
    (h0 : 0 < Λ 0 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) : 0 < nullDirFactor Λ n :=
  mulVec_nullVec_zero_pos hΛ h0 hn

/-- `Λ (1, n) = K (1, n')`. -/
theorem mulVec_nullVec_eq {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4)
    (h0 : 0 < Λ 0 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    Λ *ᵥ nullVec n = nullDirFactor Λ n • nullVec (nullDirMap Λ n) := by
  have hK := (nullDirFactor_pos hΛ h0 hn).ne'
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [nullVec, nullDirFactor]
  · simp [nullVec, nullDirMap]
    field_simp

/-- `n'` is again a unit vector. -/
theorem sum_sq_nullDirMap {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4)
    (h0 : 0 < Λ 0 0) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    ∑ i, nullDirMap Λ n i ^ 2 = 1 := by
  have hK := nullDirFactor_pos hΛ h0 hn
  have hnull := minkSq_mulVec hΛ (nullVec n)
  rw [minkSq_nullVec hn] at hnull
  have h0' : (Λ *ᵥ nullVec n) 0 = nullDirFactor Λ n := rfl
  simp only [minkSq, h0'] at hnull
  simp only [nullDirMap, div_pow, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (pow_pos hK 2).ne']
  linarith

/-- A boost along the first axis with `cosh = 5/4`, `sinh = 3/4`. -/
def boostX : Matrix (Fin 4) (Fin 4) ℝ :=
  !![5 / 4, 3 / 4, 0, 0; 3 / 4, 5 / 4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem boostX_lorentz : boostX ᵀ * eta 4 * boostX = eta 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostX, eta, etaDiag, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ] <;> norm_num

/-- Non-vacuity: the boost sends `(1, e₁)` to `2 (1, e₁)`. -/
theorem nullDirFactor_boostX_pos : nullDirFactor boostX ![1, 0, 0] = 2 := by
  simp [nullDirFactor, nullVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
  norm_num

/-- Non-vacuity: the boost sends `(1, -e₁)` to `(1/2) (1, -e₁)`. -/
theorem nullDirFactor_boostX_neg : nullDirFactor boostX ![-1, 0, 0] = 1 / 2 := by
  simp [nullDirFactor, nullVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
  norm_num

end Lightlike
