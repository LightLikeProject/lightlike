import Lightlike.HarmonicAnalysis.InvariantRep
import Lightlike.HarmonicAnalysis.ApproxIdentity

/-!
# Matrix coefficients separate the points of a compact group

Let `g ≠ h`. For a symmetric `φ`, the convolution operator `K_φ` is compact and self-adjoint; its eigenspaces
for nonzero eigenvalues are finite-dimensional, left-invariant, and consist of continuous functions, so by
`inv_mem_matrixCoeffSpan` the functions `x ↦ v(x⁻¹)` of eigenvectors lie in the span of the matrix
coefficients. If that span did not separate `g` and `h`, then `(K_φ χ)(g⁻¹) = (K_φ χ)(h⁻¹)` for all `χ ∈ L²`
(the eigenspaces span a dense subspace), hence `ψ(g⁻¹) = ψ(h⁻¹)` for all continuous `ψ` by the approximate
identity, contradicting Urysohn.

Supporting lemma for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- If the span of the matrix coefficients does not separate `g` and `h`, then every `K_φ χ` takes the
same value at `g⁻¹` and `h⁻¹`. -/
theorem convToC_eq_of_not_separated {g h : G}
    (hsep : ∀ f ∈ matrixCoeffSpan G, f g = f h) {φ : C(G, ℂ)}
    (hφ : ∀ z, φ z⁻¹ = starRingEnd ℂ (φ z)) (χ : Lp ℂ 2 μ) :
    convToC μ φ χ g⁻¹ = convToC μ φ χ h⁻¹ := by
  have hcpt : IsCompactOperator (convOp μ φ) := isCompactOperator_convOp μ φ
  have hsa : (convOp μ φ).IsSymmetric := (isSelfAdjoint_convOp μ hφ).isSymmetric
  -- the functional
  let Λ : Lp ℂ 2 μ →L[ℂ] ℂ :=
    ((ContinuousMap.evalCLM ℂ g⁻¹ - ContinuousMap.evalCLM ℂ h⁻¹ : C(G, ℂ) →L[ℂ] ℂ)).comp (convToC μ φ)
  have hΛ : ∀ v, Λ v = convToC μ φ v g⁻¹ - convToC μ φ v h⁻¹ := fun v => rfl
  -- it vanishes on every eigenspace
  have hvan : ∀ l : ℂ, ∀ v ∈ Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l, Λ v = 0 := by
    intro l v hv
    by_cases hl : l = 0
    · subst hl
      have h0 : convOp μ φ v = 0 := by
        simpa using Module.End.mem_eigenspace_iff.1 hv
      have h1 : convToC μ φ v = 0 := toLp_injective' μ (by simpa [convOp] using h0)
      rw [hΛ, h1]; simp
    · haveI : FiniteDimensional ℂ (Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) :=
        ContinuousLinearMap.finite_dimensional_eigenspace hcpt l hl
      set V := Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l with hV
      have hinv : ∀ s : G, ∀ w ∈ V, leftTr μ s w ∈ V := fun s w hw => leftTr_mem_eigenspace μ φ s l hw
      have hcont : ∀ w ∈ V, ∃ c : C(G, ℂ), w = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c :=
        fun w hw => ⟨_, eigen_eq_toLp μ φ hl hw⟩
      have hmem := inv_mem_matrixCoeffSpan μ V hinv (stdOrthonormalBasis ℂ V) hcont
        (l⁻¹ • convToC μ φ v) (by rw [← eigen_eq_toLp μ φ hl hv]; exact hv)
      have := hsep _ hmem
      have hv' : convToC μ φ v = l • (l⁻¹ • convToC μ φ v) := by
        rw [smul_smul, mul_inv_cancel₀ hl, one_smul]
      rw [hΛ, hv']
      simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sub]
      have h2 : (l⁻¹ • convToC μ φ v) g⁻¹ = (l⁻¹ • convToC μ φ v) h⁻¹ := this
      simp only [ContinuousMap.smul_apply, smul_eq_mul] at h2
      rw [mul_sub, h2]; simp
  -- eigenspaces span a dense subspace
  have hdense : (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcpt hsa
  have hker : (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) ≤ LinearMap.ker Λ.toLinearMap :=
    iSup_le fun l v hv => hvan l v hv
  have htop : (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.2 hdense
  have hclosed : IsClosed ((LinearMap.ker Λ.toLinearMap : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
    Λ.isClosed_ker
  have hχ : χ ∈ (LinearMap.ker Λ.toLinearMap : Submodule ℂ (Lp ℂ 2 μ)) := by
    have : χ ∈ (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l).topologicalClosure := by
      rw [htop]; trivial
    exact (Submodule.topologicalClosure_minimal _ hker hclosed) this
  have := hχ
  simp only [LinearMap.mem_ker] at this
  have h3 : Λ χ = 0 := this
  rw [hΛ] at h3
  exact sub_eq_zero.1 h3

/-- **Matrix coefficients separate points.** -/
theorem exists_matrixCoeff_ne {g h : G} (hgh : g ≠ h) : ∃ f ∈ matrixCoeffSpan G, f g ≠ f h := by
  let μ : Measure G := MeasureTheory.Measure.haar
  haveI : μ.IsHaarMeasure := inferInstance
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_continuousMap_ne (inv_injective.ne hgh)
  have hε : 0 < ‖a g⁻¹ - a h⁻¹‖ / 3 := by
    have : a g⁻¹ - a h⁻¹ ≠ 0 := sub_ne_zero.2 ha
    positivity
  obtain ⟨φ, hφ, happ⟩ := exists_approx_identity μ a hε
  have hK := convToC_eq_of_not_separated μ hcon hφ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a)
  have h1 := happ g⁻¹
  have h2 := happ h⁻¹
  rw [hK] at h1
  have e1 : ‖a g⁻¹ - convToC μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a) h⁻¹‖ ≤ ‖a g⁻¹ - a h⁻¹‖ / 3 := by
    rw [norm_sub_rev]; exact h1
  have e2 := norm_sub_le_norm_sub_add_norm_sub (a g⁻¹) (convToC μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a) h⁻¹)
    (a h⁻¹)
  have e3 := h2
  have hpos : 0 < ‖a g⁻¹ - a h⁻¹‖ := by
    have : a g⁻¹ - a h⁻¹ ≠ 0 := sub_ne_zero.2 ha
    positivity
  linarith

end

end Lightlike.HarmonicAnalysis
