import Lightlike.Spacetime.PenroseSingularity.JacobiMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# Focusing in terms of a Gram matrix (G1-012, step D3b, algebra)

For a positive definite matrix `Q` and `B` with `Q B` symmetric (`B` is self-adjoint for the inner
product `Q`), `tr B² ≥ (tr B)² / m`.
-/

open Matrix
open scoped MatrixOrder

noncomputable section

namespace Lightlike.Penrose

variable {m : ℕ}

theorem trace_sq_ge_of_gram (hm : 0 < m) {Q B : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef)
    (hQB : (Q * B)ᵀ = Q * B) : (trace B) ^ 2 / m ≤ trace (B * B) := by
  have hQs : Q.PosSemidef := hQ.posSemidef
  set X : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt Q with hX
  have hXX : X * X = Q := by
    have := CFC.sqrt_mul_sqrt_self Q hQs.nonneg
    simpa [hX] using this
  have hXh : Xᵀ = X := by
    have := (CFC.sqrt_nonneg Q).posSemidef.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hdetX : (X).det ≠ 0 := by
    have h1 : X.det * X.det = Q.det := by rw [← Matrix.det_mul, hXX]
    have h2 : Q.det ≠ 0 := hQ.det_pos.ne'
    intro h0; rw [h0] at h1; simp at h1; exact h2 h1.symm
  have hXu : IsUnit X.det := isUnit_iff_ne_zero.2 hdetX
  have hXi : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hXu
  have hiX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ hXu
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ.det_pos.ne'
  have hQi : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQu
  -- S = X B X⁻¹ is symmetric
  set S : Matrix (Fin m) (Fin m) ℝ := X * B * X⁻¹ with hS
  have hQt : Qᵀ = Q := by
    have := hQ.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hBt : Bᵀ * Q = Q * B := by
    have := hQB
    rw [Matrix.transpose_mul, hQt] at this
    exact this
  have hXiT : (X⁻¹)ᵀ = X⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hXh]
  have hSsym : Sᵀ = S := by
    have h1 : Sᵀ = X⁻¹ * Bᵀ * X := by
      rw [hS, Matrix.transpose_mul, Matrix.transpose_mul, hXiT, hXh]
      simp only [Matrix.mul_assoc]
    rw [h1, hS]
    -- X B X⁻¹ = X⁻¹ Bᵀ X  ⇔  Q B = Bᵀ Q
    have h2 : X * (X * B * X⁻¹) * X = X * (X⁻¹ * Bᵀ * X) * X := by
      calc X * (X * B * X⁻¹) * X = (X * X) * B * (X⁻¹ * X) := by simp only [Matrix.mul_assoc]
        _ = Q * B := by rw [hiX, hXX, Matrix.mul_one]
        _ = Bᵀ * Q := hBt.symm
        _ = X * (X⁻¹ * Bᵀ * X) * X := by
          calc Bᵀ * Q = (X * X⁻¹) * Bᵀ * (X * X) := by rw [hXi, hXX, Matrix.one_mul]
            _ = X * (X⁻¹ * Bᵀ * X) * X := by simp only [Matrix.mul_assoc]
    have hXinj : ∀ A C : Matrix (Fin m) (Fin m) ℝ, X * A * X = X * C * X → A = C := by
      intro A C h
      have key : ∀ W : Matrix (Fin m) (Fin m) ℝ, X⁻¹ * (X * W * X) * X⁻¹ = W := by
        intro W
        calc X⁻¹ * (X * W * X) * X⁻¹ = (X⁻¹ * X) * W * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
          _ = W := by rw [hiX, hXi, Matrix.one_mul, Matrix.mul_one]
      rw [← key A, ← key C, h]
    exact (hXinj _ _ h2).symm
  have htr : trace S = trace B := by
    rw [hS, Matrix.trace_mul_comm (X * B) X⁻¹, ← Matrix.mul_assoc, hiX, Matrix.one_mul]
  have htr2 : trace (S * S) = trace (B * B) := by
    have : S * S = X * (B * B) * X⁻¹ := by
      calc S * S = X * B * (X⁻¹ * X) * B * X⁻¹ := by simp only [hS, Matrix.mul_assoc]
        _ = X * (B * B) * X⁻¹ := by rw [hiX]; simp [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm (X * (B * B)) X⁻¹, ← Matrix.mul_assoc, hiX, Matrix.one_mul]
  rw [← htr, ← htr2]
  exact trace_sq_ge hm hSsym

end Lightlike.Penrose
