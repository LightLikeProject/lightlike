import Lightlike.Spacetime.RaychaudhuriSplit
import Mathlib.Analysis.Matrix.PosDef
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# The shear term is nonnegative (G1-009)

In Raychaudhuri's equation `dΘ/dλ = -Θ²/(n-1) - σ² + ω² - R(v, v)` (Kar and SenGupta, gr-qc/0611123, (12)) the shear
enters through `σ² = σ_ab σ^ab`, which is nonnegative because `σ` is spatial: `σ v = 0` and the orthogonal complement of
the timelike `v` is spacelike. Here, for matrices: `normSqG_nonneg` (`|X|² ≥ 0` for a symmetric `X` with `X u = 0` when
`y ↦ g(y, y) + 2 g(u, y)²` is nonnegative, via `|X|² = tr(K X K X)` with `K = g⁻¹ + 2 u uᵀ` positive semidefinite and
`trace_mul_nonneg`), `spacelike_complement` (that condition from `g(u, u) = -1` and a spacelike complement) and
`orthogonal_nonneg_of_lorentzian` (the complement of a timelike vector of a Lorentzian form is spacelike).
-/

open Matrix

namespace Lightlike.Raychaudhuri

variable {n : ℕ}

/-- The trace of a product of two positive semidefinite real matrices is nonnegative. -/
theorem trace_mul_nonneg {K A : Matrix (Fin n) (Fin n) ℝ} (hK : K.PosSemidef) (hA : A.PosSemidef) :
    0 ≤ trace (K * A) := by
  classical
  set U : Matrix (Fin n) (Fin n) ℝ := (hK.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hs : K = U * diagonal (RCLike.ofReal ∘ hK.1.eigenvalues) * star U := by
    conv_lhs => rw [hK.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [hs, show U * diagonal (RCLike.ofReal ∘ hK.1.eigenvalues) * star U * A =
      U * (diagonal (RCLike.ofReal ∘ hK.1.eigenvalues) * (star U * A)) by simp only [Matrix.mul_assoc],
    trace_mul_comm, Matrix.mul_assoc, trace_mul_comm, show star U * A * U = star U * (A * U) from Matrix.mul_assoc _ _ _]
  have hB : (star U * A * U).PosSemidef := by
    have := hA.conjTranspose_mul_mul_same U
    simpa [Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using this
  rw [← Matrix.mul_assoc (star U)]
  simp only [trace, diag, mul_diagonal, Function.comp_apply]
  exact Finset.sum_nonneg fun i _ => mul_nonneg hB.diag_nonneg (by simpa using hK.eigenvalues_nonneg i)

/-- **The square of a spatial symmetric tensor is nonnegative**: for a symmetric `X` with `X u = 0`, `|X|² ≥ 0` whenever
`y ↦ g(y, y) + 2 g(u, y)²` is nonnegative (for `g(u, u) = -1` this says the `g`-orthogonal complement of `u` is
spacelike, `spacelike_complement`). The proof: `|X|² = tr(K X K X)` with `K = g⁻¹ + 2 u uᵀ` positive semidefinite. -/
theorem normSqG_nonneg (G X : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (hG : Gᵀ = G) (hGu : IsUnit G.det)
    (hX : Xᵀ = X) (hXu : X *ᵥ u = 0) (hsp : ∀ y, 0 ≤ y ⬝ᵥ (G *ᵥ y) + 2 * (u ⬝ᵥ (G *ᵥ y)) ^ 2) :
    0 ≤ normSqG G X := by
  set Gi := G⁻¹ with hGi
  have hGGi : G * Gi = 1 := mul_nonsing_inv G hGu
  have hGiT : Giᵀ = Gi := by rw [hGi, transpose_nonsing_inv, hG]
  set K := Gi + (2 : ℝ) • vecMulVec u u with hKdef
  have huX : u ᵥ* X = 0 := by rw [← mulVec_transpose, hX, hXu]
  have hKX : K * X = Gi * X := by
    rw [hKdef, Matrix.add_mul, Matrix.smul_mul, vecMulVec_mul, huX]
    ext i j; simp
  have hK : K.PosSemidef := by
    rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hKdef, transpose_add, transpose_smul, hGiT,
        transpose_vecMulVec]
    · have hx : x = G *ᵥ (Gi *ᵥ x) := by rw [mulVec_mulVec, hGGi, one_mulVec]
      have h1 : x ⬝ᵥ (Gi *ᵥ x) = (Gi *ᵥ x) ⬝ᵥ (G *ᵥ (Gi *ᵥ x)) := by
        rw [dotProduct_comm, ← hx]
      have h2 : u ⬝ᵥ x = u ⬝ᵥ (G *ᵥ (Gi *ᵥ x)) := by rw [← hx]
      have h3 : x ⬝ᵥ (vecMulVec u u *ᵥ x) = (u ⬝ᵥ x) ^ 2 := by
        rw [vecMulVec_mulVec]
        simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_smul]
        rw [dotProduct_comm x u]; ring
      simp only [star_trivial, hKdef, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, h3, h1]
      rw [h2]
      exact hsp _
  have hXKX : (X * K * X).PosSemidef := by
    have := hK.conjTranspose_mul_mul_same X
    rwa [conjTranspose_eq_transpose_of_trivial, hX] at this
  have := trace_mul_nonneg hK hXKX
  unfold normSqG
  rw [← hGi, hX, show Gi * X * Gi * X = (Gi * X) * (Gi * X) by simp only [Matrix.mul_assoc], ← hKX,
    show K * X * (K * X) = K * (X * K * X) by simp only [Matrix.mul_assoc]]
  exact this

/-- For `g(u, u) = -1` and a `g`-orthogonal complement of `u` that is spacelike (`g(w, w) ≥ 0` when `g(u, w) = 0`),
`g(y, y) + 2 g(u, y)² ≥ 0` for every `y`: write `y = -g(u, y) u + w`. -/
theorem spacelike_complement (G : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (hG : Gᵀ = G)
    (hu : u ⬝ᵥ (G *ᵥ u) = -1) (hW : ∀ w, u ⬝ᵥ (G *ᵥ w) = 0 → 0 ≤ w ⬝ᵥ (G *ᵥ w)) (y : Fin n → ℝ) :
    0 ≤ y ⬝ᵥ (G *ᵥ y) + 2 * (u ⬝ᵥ (G *ᵥ y)) ^ 2 := by
  set a := u ⬝ᵥ (G *ᵥ y)
  have hsym : ∀ p q : Fin n → ℝ, p ⬝ᵥ (G *ᵥ q) = q ⬝ᵥ (G *ᵥ p) := fun p q => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]
  set w := y + a • u
  have hw : u ⬝ᵥ (G *ᵥ w) = 0 := by
    simp only [w, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hu]; ring
  have hww : w ⬝ᵥ (G *ᵥ w) = y ⬝ᵥ (G *ᵥ y) + a ^ 2 := by
    simp only [w, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hu]
    rw [hsym y u]; ring
  have := hW w hw
  nlinarith [sq_nonneg a]

/-- For a Lorentzian form `B(x, y) = x ⬝ᵥ (G *ᵥ y)` and a timelike `u`, the `B`-orthogonal complement of `u` is spacelike
(from `IsLorentzianForm.eq_zero_of_orthogonal_timelike`). -/
theorem orthogonal_nonneg_of_lorentzian {G : Matrix (Fin n) (Fin n) ℝ} {u : Fin n → ℝ}
    {B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hL : IsLorentzianForm n B) (hB : ∀ x y, B x y = x ⬝ᵥ (G *ᵥ y))
    (hu : u ⬝ᵥ (G *ᵥ u) < 0) (w : Fin n → ℝ) (hw : u ⬝ᵥ (G *ᵥ w) = 0) : 0 ≤ w ⬝ᵥ (G *ᵥ w) := by
  by_contra h
  have h0 := hL.eq_zero_of_orthogonal_timelike (X := u) (w := w) (by rw [hB]; exact hu)
    (by rw [hL.symm, hB]; exact hw) (by rw [hB]; linarith)
  subst h0
  simp at h

end Lightlike.Raychaudhuri
