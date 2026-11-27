import Mathlib
import Lightlike.OperatorAlgebras.KernelMercer
import Lightlike.Spacetime.NondegMetric
import Lightlike.Spacetime.VolumeMeasureFinite

/-!
# Integral operators on a compact Riemannian manifold

Let `M` be a compact Riemannian manifold (a smooth Riemannian metric of Mathlib,
`Bundle.ContMDiffRiemannianMetric`, as a nondegenerate metric through `NondegMetric.ofRiemannian`)
with its Riemannian volume `vol_g` (`NondegMetric.volumeMeasure`). For a continuous Hermitian kernel
`K(y, x) = conj K(x, y)` on `M × M`, the integral operator
`(T_K ψ)(x) = ∫_M K(x, y) ψ(y) dvol_g(y)` on `L²(M)` (`riemannian_integralOperator`)

* is Hilbert–Schmidt, `Σ_i ‖T_K b_i‖² = ∫∫ |K(x, y)|²` for every Hilbert basis `(b_i)`,
* is compact and self-adjoint,
* has a Hilbert basis of eigenvectors with real eigenvalues, every eigenvector with a non-zero
  eigenvalue having a continuous representative, and
* if it is positive, its trace is `Σ_i ⟪T_K e_i, e_i⟫ = ∫_M K(x, x) dvol_g(x)` in every Hilbert basis
  `(e_i)` (Mercer).

The general statements are in `Lightlike/OperatorAlgebras/KernelOperator.lean`,
`KernelHilbertSchmidt.lean`, `KernelSpectral.lean` and `KernelMercer.lean`, for a compact second
countable space with a finite Borel measure positive on non-empty open sets. The Riemannian volume
of a compact manifold is finite and positive on open sets
(`NondegMetric.isFiniteMeasure_volumeMeasure`, `NondegMetric.isOpenPosMeasure_volumeMeasure`).

## Main results

* `riemannian_integralOperator`

## References

* A. Gheondea, *Mercer's theorem* (arXiv:2512.06475), Proposition 4.1, pp. 25–26, Theorem 4.16
  and Corollary 4.17, pp. 36–37.
* P. Garrett, *Compact operators* (notes 09b, 2020), §§2–3.
-/

open MeasureTheory Manifold
open scoped ContDiff

universe u v w

namespace Lightlike.OperatorAlgebras

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (hR : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ)
    (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))

attribute [local instance] NondegMetric.isFiniteMeasure_volumeMeasure
  NondegMetric.isOpenPosMeasure_volumeMeasure

/-- **Integral operators with continuous Hermitian kernels on a compact Riemannian manifold** are
the integral operators `ψ ↦ ∫ K(·, y) ψ(y) dvol_g(y)` on `L²(M, vol_g)`; they are Hilbert–Schmidt,
compact and self-adjoint, have an orthonormal eigenbasis (continuous for non-zero eigenvalues), and the trace of a positive one is
`∫_M K(x, x) dvol_g(x)` (Mercer). -/
theorem riemannian_integralOperator (K : C(M × M, ℂ))
    (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) :
    let μ := (NondegMetric.ofRiemannian hR).volumeMeasure
    (∀ ψ : Lp ℂ 2 μ, (kernelOp μ K ψ : M → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * ψ y ∂μ) ∧
    (∀ {ι : Type v} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)),
      HasSum (fun i => ‖kernelOp μ K (b i)‖ ^ 2) (∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂μ ∂μ)) ∧
    IsCompactOperator (kernelOp μ K) ∧
    IsSelfAdjoint (kernelOp μ K) ∧
    (∃ (ι : Type u) (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ),
      ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i) ∧
    (∀ (b : Lp ℂ 2 μ) (lam : ℂ), lam ≠ 0 → kernelOp μ K b = lam • b →
      ∃ φ : C(M, ℂ), (b : M → ℂ) =ᵐ[μ] φ) ∧
    ((kernelOp μ K).IsPositive → ∀ {κ : Type w} (e : HilbertBasis κ ℂ (Lp ℂ 2 μ)),
      HasSum (fun i => inner ℂ (kernelOp μ K (e i)) (e i)) (∫ x, K (x, x) ∂μ)) := by
  intro μ
  have hS := isSymmetric_kernelOp μ K hK
  refine ⟨kernelOp_ae_eq μ K, fun b => hasSum_norm_sq_kernelOp μ K b,
    isCompactOperator_kernelOp μ K, hS.isSelfAdjoint,
    exists_hilbertBasis_eigenvectors_kernelOp μ K hK, fun b lam hl hb => ?_, fun hP {κ} e => ?_⟩
  · refine ⟨lam⁻¹ • kernelToC μ K b, ?_⟩
    filter_upwards [ae_eq_continuous_of_eigen μ K hl hb] with x hx
    rw [hx, ContinuousMap.smul_apply, smul_eq_mul]
  have hpos : IsPositiveKernel μ K := fun f => by
    have := hP.2 f
    rwa [ContinuousLinearMap.reApplyInnerSelf_apply] at this
  exact hasSum_inner_basis_eq_integral_diag μ K hK hpos e

end

end Lightlike.OperatorAlgebras
