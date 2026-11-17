import Mathlib
import Lightlike.Canonical.DensityDeriv

/-!
# Covariance of the kinetic term: a matrix identity

At a point, write `Lξ = Σ_k ξ^k H_k + X H + H Xᵀ` (the Lie derivative of the metric) and
`Lπ = Σ_k ξ^k P_k − Xᵀ P − P X + tr X · P` (the Lie derivative of the momentum density, of weight one),
with `X i k = ∂_i ξ^k`. Then the derivative of the kinetic term along `(Lξ, Lπ)` is
`Σ_k ξ^k dkinJ(H_k, P_k) + tr X · kinJ` (`dkinJ_lie`): the kinetic term is a scalar density.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- `dkinJ c H P` is linear in the direction `(L, p)`. -/
def dkinLin (c : ℝ) (H P : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) →ₗ[ℝ] ℝ where
  toFun v := dkinJ c H P v.1 v.2
  map_add' v w := by
    simp only [dkinJ, Prod.fst_add, Prod.snd_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    ring
  map_smul' a v := by
    simp only [dkinJ, Prod.smul_fst, Prod.smul_snd, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
      Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring

lemma dkinLin_apply (c : ℝ) (H P L p : Matrix (Fin d) (Fin d) ℝ) :
    dkinLin c H P (L, p) = dkinJ c H P L p := rfl

lemma trace_cyc3 (A X : Matrix (Fin d) (Fin d) ℝ) : (A * (X * A)).trace = (A * (A * X)).trace := by
  rw [Matrix.trace_mul_comm A (X * A), ← Matrix.mul_assoc, Matrix.mul_assoc X A A,
    Matrix.trace_mul_comm X (A * A), Matrix.mul_assoc]

/-- The part of the Lie derivative of `(h, π)` that comes from `∂ξ`: it changes the kinetic term by
`tr X` times itself. -/
lemma dkinJ_Xpart (c : ℝ) (H P X : Matrix (Fin d) (Fin d) ℝ) (hH : 0 < H.det) :
    dkinJ c H P (X * H + H * Xᵀ) (-(Xᵀ * P) - P * X + X.trace • P) = X.trace * kinJ c H P := by
  set A := H * P with hA
  have hHu : IsUnit H.det := hH.ne'.isUnit
  have hA' : (X * H + H * Xᵀ) * P + H * (-(Xᵀ * P) - P * X + X.trace • P) =
      X * A - A * X + X.trace • A := by
    simp only [hA, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.mul_assoc]
    abel
  have htrL : (H⁻¹ * (X * H + H * Xᵀ)).trace = 2 * X.trace := by
    rw [Matrix.mul_add, Matrix.trace_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHu, Matrix.one_mul]
    have : (H⁻¹ * H * Xᵀ).trace = X.trace := by
      rw [Matrix.nonsing_inv_mul _ hHu, Matrix.one_mul, Matrix.trace_transpose]
    rw [this]; ring
  have htr1 : (A * (X * A - A * X + X.trace • A)).trace = X.trace * (A * A).trace := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul]
    rw [trace_cyc3 A X]; ring
  have htr2 : (X * A - A * X + X.trace • A).trace = X.trace * A.trace := by
    simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm X A]
    ring
  have hs : Real.sqrt H.det ^ 2 = H.det := Real.sq_sqrt hH.le
  have hs0 : Real.sqrt H.det ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
  have hAA : H * P * H * P = A * A := by simp [hA, Matrix.mul_assoc]
  unfold dkinJ kinJ
  rw [hA', htrL, htr1, htr2, hAA, ← hA]
  field_simp
  rw [hs]
  ring

/-- **The kinetic term is a scalar density**: the derivative along the Lie derivatives of `h` (with `π` fixed) plus
the derivative along the Lie derivative of `π` (with `h` fixed) is `Σ_k ξ^k ∂_k K + tr X · K`. -/
theorem dkinJ_lie (c : ℝ) (H P X : Matrix (Fin d) (Fin d) ℝ) (Hk Pk : Fin d → Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin d → ℝ) (hH : 0 < H.det) :
    dkinJ c H P ((∑ k, ξ k • Hk k) + X * H + H * Xᵀ) 0 +
        dkinJ c H P 0 ((∑ k, ξ k • Pk k) + (-(Xᵀ * P) - P * X + X.trace • P)) =
      ∑ k, ξ k * dkinJ c H P (Hk k) (Pk k) + X.trace * kinJ c H P := by
  have e1 : dkinJ c H P ((∑ k, ξ k • Hk k) + X * H + H * Xᵀ) 0 +
      dkinJ c H P 0 ((∑ k, ξ k • Pk k) + (-(Xᵀ * P) - P * X + X.trace • P)) =
      dkinLin c H P (((∑ k, ξ k • Hk k) + X * H + H * Xᵀ), ((∑ k, ξ k • Pk k) +
        (-(Xᵀ * P) - P * X + X.trace • P))) := by
    have : ((∑ k, ξ k • Hk k) + X * H + H * Xᵀ, (∑ k, ξ k • Pk k) + (-(Xᵀ * P) - P * X + X.trace • P)) =
        (((∑ k, ξ k • Hk k) + X * H + H * Xᵀ, 0) :
          Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) +
        (0, (∑ k, ξ k • Pk k) + (-(Xᵀ * P) - P * X + X.trace • P)) := by
      ext1 <;> simp
    rw [this, map_add]
    rfl
  have e2 : (((∑ k, ξ k • Hk k) + X * H + H * Xᵀ), ((∑ k, ξ k • Pk k) +
        (-(Xᵀ * P) - P * X + X.trace • P))) =
      (∑ k, ξ k • (Hk k, Pk k)) + (X * H + H * Xᵀ, -(Xᵀ * P) - P * X + X.trace • P) := by
    ext1
    · simp [Prod.fst_sum, add_assoc]
    · simp [Prod.snd_sum]
  rw [e1, e2, map_add, map_sum]
  simp only [map_smul, dkinLin_apply, smul_eq_mul]
  rw [dkinJ_Xpart c H P X hH]

/-- The derivative of `√det` along `Lξ = Σ_k ξ^k H_k + X H + H Xᵀ`: `Σ_k ξ^k ∂_k √det + tr X √det`. -/
lemma sqrt_det_lie (H X : Matrix (Fin d) (Fin d) ℝ) (Hk : Fin d → Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ)
    (hH : 0 < H.det) :
    H.det * (H⁻¹ * ((∑ k, ξ k • Hk k) + X * H + H * Xᵀ)).trace / (2 * Real.sqrt H.det) =
      ∑ k, ξ k * (H.det * (H⁻¹ * Hk k).trace / (2 * Real.sqrt H.det)) + X.trace * Real.sqrt H.det := by
  have hHu : IsUnit H.det := hH.ne'.isUnit
  have htr : (H⁻¹ * ((∑ k, ξ k • Hk k) + X * H + H * Xᵀ)).trace =
      ∑ k, ξ k * (H⁻¹ * Hk k).trace + 2 * X.trace := by
    have h1 : (H⁻¹ * (X * H)).trace = X.trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHu,
        Matrix.one_mul]
    have h2 : (H⁻¹ * (H * Xᵀ)).trace = X.trace := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHu, Matrix.one_mul, Matrix.trace_transpose]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, h1, h2, Matrix.mul_sum,
      Matrix.trace_sum]
    simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    ring
  have hs : Real.sqrt H.det ^ 2 = H.det := Real.sq_sqrt hH.le
  have hs0 : Real.sqrt H.det ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
  have key : ∑ k, ξ k * (H.det * (H⁻¹ * Hk k).trace / (2 * Real.sqrt H.det)) =
      H.det * (∑ k, ξ k * (H⁻¹ * Hk k).trace) / (2 * Real.sqrt H.det) := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [htr, key]
  set S := ∑ k, ξ k * (H⁻¹ * Hk k).trace
  have hd : H.det = Real.sqrt H.det ^ 2 := hs.symm
  set s := Real.sqrt H.det
  rw [hd]
  field_simp

end Lightlike.Canonical

end
