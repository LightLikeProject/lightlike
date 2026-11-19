import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Expansion, shear and rotation (G1-009)

Kar and SenGupta (gr-qc/0611123), eq. (1): `∇_b vₐ = σₐᵦ + ωₐᵦ + h_ab Θ/(n-1)` with `σ` the symmetric traceless part (the
shear), `ω` the antisymmetric part (the rotation) and `Θ = ∇ₐvᵃ`, `h = g + v ⊗ v`. For a matrix `M` (`Mᵃ_b = ∇_b vᵃ`) with
`M v = 0` (the geodesic equation) at a point where `g(v, v) = -1`, the lowered `L = G M`, its symmetric part `S`, its
antisymmetric part `W` (the rotation), and `σ = S - (Θ/(n-1)) h`:
**`tr(M²) = Θ²/(n-1) + |σ|² - |ω|²`** (`trace_sq_split`), with `|X|² = tr(G⁻¹ X G⁻¹ Xᵀ)` (indices raised with `G⁻¹`).
-/

open Matrix

namespace Lightlike.Raychaudhuri

variable {n : ℕ}

/-- `|X|² = Xₐᵦ X^{ab}`, indices raised with `G⁻¹`. -/
noncomputable def normSqG (G X : Matrix (Fin n) (Fin n) ℝ) : ℝ := trace (G⁻¹ * X * G⁻¹ * Xᵀ)

theorem trace_sq_split (G M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (hG : Gᵀ = G) (hGu : IsUnit G.det)
    (hMu : M *ᵥ u = 0) (hnorm : u ⬝ᵥ (G *ᵥ u) = -1) (hn : 1 < n) :
    trace (M * M) = (trace M) ^ 2 / (n - 1) +
      normSqG G ((1 / 2 : ℝ) • (G * M + (G * M)ᵀ) - (trace M / (n - 1)) • (G + vecMulVec (G *ᵥ u) (G *ᵥ u))) -
      normSqG G ((1 / 2 : ℝ) • (G * M - (G * M)ᵀ)) := by
  set Gi := G⁻¹ with hGi
  have hGiG : Gi * G = 1 := nonsing_inv_mul G hGu
  have hGGi : G * Gi = 1 := mul_nonsing_inv G hGu
  have hGiT : Giᵀ = Gi := by rw [hGi, transpose_nonsing_inv, hG]
  set L := G * M with hL
  set θ := trace M with hθ
  -- `t(X, Y) = tr(G⁻¹ X G⁻¹ Y)`
  have tLL : trace (Gi * L * Gi * L) = trace (M * M) := by
    rw [hL, show Gi * (G * M) * Gi * (G * M) = (Gi * G) * M * (Gi * G) * M by simp only [Matrix.mul_assoc],
      hGiG, Matrix.one_mul, Matrix.mul_one]
  have tTT : trace (Gi * Lᵀ * Gi * Lᵀ) = trace (Gi * L * Gi * L) := by
    rw [← trace_transpose]
    simp only [transpose_mul, transpose_transpose, hGiT, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  -- the rotation and the symmetric part
  have e1 : normSqG G ((1 / 2 : ℝ) • (L + Lᵀ)) - normSqG G ((1 / 2 : ℝ) • (L - Lᵀ)) = trace (M * M) := by
    unfold normSqG
    simp only [transpose_smul, transpose_add, transpose_sub, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, trace_smul, trace_add, trace_sub, smul_eq_mul]
    rw [← tLL, ← tTT]
    ring
  -- the projector `h = G + u' u'ᵀ`
  set u' := G *ᵥ u with hu'
  set P := vecMulVec u u' with hP
  set S := (1 / 2 : ℝ) • (L + Lᵀ) with hS
  set h := G + vecMulVec u' u' with hh
  have hSt : Sᵀ = S := by simp only [hS, transpose_smul, transpose_add, transpose_transpose, add_comm]
  have hht : hᵀ = h := by simp only [hh, transpose_add, hG, transpose_vecMulVec]
  have hGih : Gi * h = 1 + P := by
    rw [hh, Matrix.mul_add, hGiG, mul_vecMulVec, hu', Matrix.mulVec_mulVec, hGiG, Matrix.one_mulVec]
  have huu : u ⬝ᵥ u' = -1 := hnorm
  have htrP : trace P = -1 := by rw [hP, trace_vecMulVec]; exact huu
  have hPP : P * P = -P := by
    rw [hP, vecMulVec_mul_vecMulVec, dotProduct_comm, huu, neg_one_smul]
    ext i j; simp [vecMulVec_apply]
  have thh : trace (Gi * h * Gi * h) = n - 1 := by
    rw [Matrix.mul_assoc Gi h, ← Matrix.mul_assoc, show Gi * h * Gi * h = (Gi * h) * (Gi * h) by
      simp only [Matrix.mul_assoc]]
    rw [hGih]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPP, trace_add, trace_neg, trace_one,
      htrP, Fintype.card_fin]
    ring
  have tGiL : trace (Gi * L) = θ := by rw [hL, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  have tGiLt : trace (Gi * Lᵀ) = θ := by
    rw [← trace_transpose, transpose_mul, transpose_transpose, hGiT, trace_mul_comm, hL, ← Matrix.mul_assoc, hGiG,
      Matrix.one_mul]
  have hLu : L *ᵥ u = 0 := by rw [hL, ← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_zero]
  have tGiSP : trace (Gi * S * P) = 0 := by
    rw [hP, mul_vecMulVec, trace_vecMulVec, hu', dotProduct_mulVec, ← Matrix.mulVec_transpose, hG,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hGGi, Matrix.one_mul, hS, Matrix.smul_mulVec,
      Matrix.add_mulVec, hLu, zero_add, smul_dotProduct, Matrix.mulVec_transpose, ← dotProduct_mulVec, hLu,
      dotProduct_zero, smul_zero]
  have tSh : trace (Gi * S * Gi * h) = θ := by
    rw [Matrix.mul_assoc (Gi * S), hGih, Matrix.mul_add, Matrix.mul_one, trace_add, tGiSP, add_zero, hS,
      Matrix.mul_smul, trace_smul, Matrix.mul_add, trace_add, tGiL, tGiLt, smul_eq_mul]
    ring
  have thS : trace (Gi * h * Gi * S) = θ := by
    rw [show Gi * h * Gi * S = (Gi * h) * (Gi * S) by simp only [Matrix.mul_assoc], trace_mul_comm,
      show Gi * S * (Gi * h) = Gi * S * Gi * h by simp only [Matrix.mul_assoc], tSh]
  have e2 : ∀ c : ℝ, normSqG G (S - c • h) = normSqG G S - 2 * c * θ + c ^ 2 * (n - 1) := by
    intro c
    have hT : (S - c • h)ᵀ = S - c • h := by rw [transpose_sub, transpose_smul c h, hSt, hht]
    unfold normSqG
    rw [← hGi, hT, hSt]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, trace_sub, trace_smul, smul_eq_mul]
    rw [show Gi * S * Gi * h = Gi * S * Gi * h from rfl, tSh, thS, thh]
    ring
  rw [e2, ← e1]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  field_simp
  ring

end Lightlike.Raychaudhuri
