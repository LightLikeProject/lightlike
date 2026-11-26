import Mathlib
import Lightlike.Asymptotics.MorseLemma

/-!
# The Morse index is the number of negative eigenvalues of the Hessian

`morse_diagonal` (`MorseLemma.lean`) gives the number of negative signs of the diagonal normal form as
`sigNeg` of the Hessian, the largest dimension of a subspace on which the Hessian is negative definite.
On a finite-dimensional real inner product space the Hessian is a symmetric operator `A` with
`B x y = ⟪x, A y⟫`, and this file proves the eigenvalue form: `sigNeg` is the number of negative
eigenvalues of `A`, counted with multiplicity (`sigNeg_hessQuad_eq_card_neg_eigenvalues`).
-/

namespace Lightlike.Morse

open Filter Topology
open scoped InnerProductSpace ContDiff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Morse index is the number of negative eigenvalues of the Hessian.** If `A` is a symmetric
operator representing the bilinear form `B` (`B x y = ⟪x, A y⟫`), the largest dimension `sigNeg` of a
subspace on which `½ B x x` is negative definite is the number of negative eigenvalues of `A`, counted
with multiplicity. -/
theorem sigNeg_hessQuad_eq_card_neg_eigenvalues (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (hB : ∀ x y, B x y = ⟪x, A y⟫_ℝ) :
    sigNeg (hessQuad B) =
      {i | hA.eigenvalues (n := Module.finrank ℝ E) rfl i < 0}.ncard := by
  set b := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl with hb
  set μ := hA.eigenvalues (n := Module.finrank ℝ E) rfl with hμ
  have hAb : ∀ i, A (b i) = (μ i : ℝ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ))
  have key : ∀ x : E, hessQuad B x =
      QuadraticMap.weightedSumSquares ℝ (fun i => μ i / 2) (e x) := by
    intro x
    rw [hessQuad_apply, hB]
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have hAx : A x = ∑ i, (b.repr x i * μ i) • b i := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul, hAb, smul_smul]
    rw [hAx, QuadraticMap.weightedSumSquares_apply]
    conv_lhs => rw [hx]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, b.inner_eq_ite]
    simp [Finset.sum_ite_eq', Finset.mul_sum, e]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hE : QuadraticMap.Equivalent (hessQuad B)
      (QuadraticMap.weightedSumSquares ℝ (fun i => μ i / 2)) :=
    ⟨{ toLinearEquiv := e, map_app' := fun m => (key m).symm }⟩
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hE]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- **A symmetric bilinear form on an inner product space is represented by a symmetric operator**:
`B x y = ⟪x, A y⟫` (Riesz). -/
theorem exists_symmetric_operator (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) :
    ∃ A : E →ₗ[ℝ] E, A.IsSymmetric ∧ ∀ x y, B x y = ⟪x, A y⟫_ℝ := by
  let A : E →ₗ[ℝ] E :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm (B.flip y)
      map_add' := fun y z => by simp
      map_smul' := fun c y => by simp }
  have hA : ∀ x y, B x y = ⟪x, A y⟫_ℝ := by
    intro x y
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := x) (y := B.flip y)
    show B x y = ⟪x, (InnerProductSpace.toDual ℝ E).symm (B.flip y)⟫_ℝ
    rw [real_inner_comm]
    exact h.symm
  refine ⟨A, fun x y => ?_, hA⟩
  rw [real_inner_comm, ← hA y x, hB, hA]

/-- **The Morse index in the Morse lemma is the number of negative eigenvalues of the Hessian.** Under
the hypotheses of `morse_diagonal` on a finite-dimensional real inner product space `E`, the number
of negative signs in the diagonal normal form is the number of negative eigenvalues, counted with
multiplicity, of the symmetric operator `A` of the Hessian `∂ₓ² f (0, λ₀)`. -/
theorem morse_diagonal_eigenvalues {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E × F → ℝ} (hf : ContDiff ℝ ∞ f) {l₀ : F}
    (hcrit : ∀ᶠ l in nhds l₀, partialE f (0, l) = 0)
    (hnd : ∀ v, (∀ w, partialE2 f (0, l₀) v w = 0) → v = 0) :
    ∃ (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (w : Fin (Module.finrank ℝ E) → ℝ),
      (∀ x y, partialE2 f (0, l₀) x y = ⟪x, A y⟫_ℝ) ∧ (∀ i, w i = -1 ∨ w i = 1) ∧
      {i | w i < 0}.ncard = {i | hA.eigenvalues (n := Module.finrank ℝ E) rfl i < 0}.ncard ∧
      HasDiagonalMorseChart f l₀ w := by
  obtain ⟨w, hw, hsig, hchart⟩ := morse_diagonal hf hcrit hnd
  obtain ⟨A, hA, hrep⟩ := exists_symmetric_operator (partialE2 f (0, l₀))
    (fun x y => partialE2_symm hf _ x y)
  exact ⟨A, hA, w, hrep, hw, hsig.symm.trans (sigNeg_hessQuad_eq_card_neg_eigenvalues _ A hA hrep),
    hchart⟩

end Lightlike.Morse
