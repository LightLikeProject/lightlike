import Lightlike.Spacetime.PenroseSingularity.JacobiGram
import Mathlib.Analysis.Matrix.Order

/-!
# Orthonormalising a Gram matrix (G1-012, step D3b wiring)

A positive definite Gram matrix `Q` has a matrix `A` with `A Q Aᵀ = 1` (the coefficients of an orthonormal
frame in the given basis), and then `tr (Q⁻¹ Cᵀ) = Σ_a Σ_ij A_ai A_aj C_ij`: the trace of the bilinear form
`C` over an orthonormal frame.
-/

open Matrix
open scoped Matrix MatrixOrder

noncomputable section

namespace Lightlike.Penrose

variable {m : ℕ}

/-- A positive definite matrix has an orthonormalising matrix. -/
theorem exists_orthonormalizing {Q : Matrix (Fin m) (Fin m) ℝ} (hQ : Q.PosDef) :
    ∃ A : Matrix (Fin m) (Fin m) ℝ, A * Q * Aᵀ = 1 := by
  set X : Matrix (Fin m) (Fin m) ℝ := CFC.sqrt Q with hX
  have hXX : X * X = Q := by
    have := CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg
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
  refine ⟨X⁻¹, ?_⟩
  rw [Matrix.transpose_nonsing_inv, hXh, ← hXX, Matrix.mul_assoc, Matrix.mul_assoc, hXi,
    Matrix.mul_one, hiX]

/-- The trace of a bilinear form over an orthonormal frame. -/
theorem trace_inv_mul_transpose_eq {Q C A : Matrix (Fin m) (Fin m) ℝ} (hA : A * Q * Aᵀ = 1) :
    trace (Q⁻¹ * Cᵀ) = ∑ a, ∑ i, ∑ j, A a i * A a j * C i j := by
  have h1 : A * (Q * Aᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact hA
  have h2 : (Q * Aᵀ) * A = 1 := mul_eq_one_comm.1 h1
  have h3 : Q * (Aᵀ * A) = 1 := by rw [← Matrix.mul_assoc]; exact h2
  have h4 : Q⁻¹ = Aᵀ * A := Matrix.inv_eq_right_inv h3
  rw [h4]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  calc ∑ y, ∑ x, ∑ j, A j x * A j y * C x y
      = ∑ y, ∑ j, ∑ x, A j x * A j y * C x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ y, ∑ x, A j x * A j y * C x y := Finset.sum_comm
    _ = ∑ j, ∑ x, ∑ y, A j x * A j y * C x y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **An orthonormal frame in the span of a family**: for a positive definite form `G` on a subspace `K`
containing a linearly independent family `u`, there is a `G`-orthonormal family in `K` over which the trace
of another bilinear form `B` is `tr (Q⁻¹ Cᵀ)`, with `Q = G(u_i, u_j)` and `C = B(u_i, u_j)`. -/
theorem exists_frame_trace {V : Type*} [AddCommGroup V] [Module ℝ V] (G Bf : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsymm : ∀ v w, G v w = G w v) (K : Submodule ℝ V) (u : Fin m → V) (hu : LinearIndependent ℝ u)
    (huK : ∀ i, u i ∈ K) (hpos : ∀ v ∈ K, v ≠ 0 → 0 < G v v) :
    (Matrix.of fun i j => G (u i) (u j)).PosDef ∧
      ∃ e : Fin m → V, (∀ a, e a ∈ K) ∧ (∀ a b, G (e a) (e b) = if a = b then 1 else 0) ∧
        ∑ a, Bf (e a) (e a) =
          trace ((Matrix.of fun i j => G (u i) (u j))⁻¹ * (Matrix.of fun i j => Bf (u i) (u j))ᵀ) := by
  classical
  have hQ : (Matrix.of fun i j => G (u i) (u j)).PosDef := by
    refine ⟨?_, fun c hc => ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, hsymm (u j) (u i)]
    · set v : V := ∑ i, c i • u i with hv
      have hvK : v ∈ K := K.sum_mem fun i _ => K.smul_mem _ (huK i)
      have hv0 : v ≠ 0 := by
        intro h0
        exact hc (Finsupp.ext fun i => (Fintype.linearIndependent_iff.1 hu c h0) i)
      have hGv : G v v = c.sum fun i xi => c.sum fun j xj =>
          star xi * (Matrix.of fun i j => G (u i) (u j)) i j * xj := by
        have e : (c.sum fun i xi => c.sum fun j xj =>
            star xi * (Matrix.of fun i j => G (u i) (u j)) i j * xj) =
            ∑ i, ∑ j, c i * G (u i) (u j) * c j := by
          rw [Finsupp.sum_fintype _ _ (by intro i; simp [Finsupp.sum])]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
          simp
        rw [e]
        simp only [hv, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [← hGv]; exact hpos v hvK hv0
  refine ⟨hQ, ?_⟩
  obtain ⟨A, hA⟩ := exists_orthonormalizing hQ
  refine ⟨fun a => ∑ i, A a i • u i, fun a => K.sum_mem fun i _ => K.smul_mem _ (huK i), fun a b => ?_, ?_⟩
  · have := congrFun (congrFun hA a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] at this
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [trace_inv_mul_transpose_eq hA]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end Lightlike.Penrose
