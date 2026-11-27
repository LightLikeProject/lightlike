import Mathlib
import Lightlike.OperatorAlgebras.KernelSpectral

/-!
# Mercer's theorem for integral operators with continuous kernels

Let `X` be a compact space with a finite Borel measure `μ` that is positive on non-empty open sets,
`K` a continuous Hermitian kernel whose integral operator `T_K` is positive, and `(b_i, λ_i)` an
eigenbasis of `T_K`. This file builds the continuous eigenfunctions and the pointwise expansion of
`T_K` used for Mercer's theorem:

* the eigenvalues are non-negative (`eigen_nonneg`);
* `φ_i = λ_i⁻¹ (x ↦ ⟪k_x, b_i⟫)` is continuous and `x ↦ ⟪k_x, b_i⟫ = λ_i φ_i` (`kernelToC_eigen`),
  also when `λ_i = 0`, because a continuous function vanishing almost everywhere vanishes;
* `(T_K f)(x) = Σ_i λ_i φ_i(x) ⟪b_i, f⟫` for every `x` (`hasSum_kernelToC`), by Parseval's identity
  for `⟪k_x, f⟫`.

## References

* A. Gheondea, *Mercer's theorem* (arXiv:2512.06475), Theorem 4.16, p. 36, and Corollary 4.17,
  p. 37 (there for `supp ν ⊇ supp K`; here `μ` is positive on open sets, which holds for the
  Riemannian volume).
* J. Mercer, *Functions of positive and negative type, and their connection with the theory of
  integral equations*, Phil. Trans. R. Soc. Lond. A 209 (1909), 415–446 (the interval case).
-/

open MeasureTheory Filter Topology

namespace Lightlike.OperatorAlgebras

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The operator `T_K` is positive: `0 ≤ re ⟪T_K f, f⟫` for all `f`. -/
def IsPositiveKernel (K : C(X × X, ℂ)) : Prop :=
  ∀ f : Lp ℂ 2 μ, 0 ≤ RCLike.re (inner ℂ (kernelOp μ K f) f)

/-- **The eigenvalues of a positive operator are non-negative.** -/
lemma eigen_nonneg {K : C(X × X, ℂ)} (hpos : IsPositiveKernel μ K) {b : Lp ℂ 2 μ} {lam : ℝ}
    (hb : kernelOp μ K b = (lam : ℂ) • b) (hb1 : ‖b‖ = 1) : 0 ≤ lam := by
  have h := hpos b
  rw [hb, inner_smul_left, inner_self_eq_norm_sq_to_K, hb1] at h
  simpa using h

omit [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- A continuous function vanishing almost everywhere for a measure positive on open sets vanishes. -/
lemma eq_zero_of_ae_eq_zero [μ.IsOpenPosMeasure] {g : C(X, ℂ)} (hg : (g : X → ℂ) =ᵐ[μ] 0) :
    g = 0 := by
  ext x
  exact congrFun ((g.continuous.ae_eq_iff_eq μ continuous_const).1 hg) x

/-- The continuous eigenfunction `φ = λ⁻¹ (x ↦ ⟪k_x, b⟫)`. -/
def eigenFun (K : C(X × X, ℂ)) (b : Lp ℂ 2 μ) (lam : ℝ) : C(X, ℂ) :=
  ((lam : ℂ))⁻¹ • kernelToC μ K b

/-- **`x ↦ ⟪k_x, b⟫ = λ φ`** for an eigenvector `T_K b = λ b`, including `λ = 0`. -/
lemma kernelToC_eigen [μ.IsOpenPosMeasure] (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℝ}
    (hb : kernelOp μ K b = (lam : ℂ) • b) :
    kernelToC μ K b = (lam : ℂ) • eigenFun μ K b lam := by
  by_cases hl : lam = 0
  · subst hl
    have hz : kernelOp μ K b = 0 := by rw [hb]; simp
    have hae : (kernelToC μ K b : X → ℂ) =ᵐ[μ] 0 := by
      have h1 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelToC μ K b)
      have e : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kernelToC μ K b) = 0 := hz
      rw [e] at h1
      filter_upwards [h1, Lp.coeFn_zero ℂ 2 μ] with x hx1 hx2
      rw [← hx1, hx2]
    rw [eq_zero_of_ae_eq_zero μ hae]
    simp
  · have hl' : ((lam : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
    rw [eigenFun, smul_smul, mul_inv_cancel₀ hl', one_smul]

/-- `φ` represents `b` when `λ ≠ 0`. -/
lemma ae_eq_eigenFun (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℝ} (hl : lam ≠ 0)
    (hb : kernelOp μ K b = (lam : ℂ) • b) :
    (b : X → ℂ) =ᵐ[μ] eigenFun μ K b lam := by
  have h := ae_eq_continuous_of_eigen μ K (lam := (lam : ℂ)) (by exact_mod_cast hl) hb
  filter_upwards [h] with x hx
  rw [hx, eigenFun]
  simp

/-- **The pointwise expansion**: `⟪k_x, f⟫ = Σ_i λ_i φ_i(x) ⟪b_i, f⟫` for every `x`. -/
theorem hasSum_kernelToC [μ.IsOpenPosMeasure] (K : C(X × X, ℂ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ)
    (hb : ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) (f : Lp ℂ 2 μ) (x : X) :
    HasSum (fun i => (lam i : ℂ) * eigenFun μ K (b i) (lam i) x * inner ℂ (b i) f)
      (kernelToC μ K f x) := by
  have h := b.hasSum_inner_mul_inner (kernelVecOf μ K x) f
  rw [← kernelToC_apply] at h
  refine h.congr_fun fun i => ?_
  rw [← kernelToC_apply, kernelToC_eigen μ K (hb i)]
  simp [mul_assoc]

end

end Lightlike.OperatorAlgebras
