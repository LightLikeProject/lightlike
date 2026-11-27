import Mathlib
import Lightlike.OperatorAlgebras.KernelHilbertSchmidt

/-!
# An orthonormal eigenbasis of a compact self-adjoint operator

A compact symmetric operator `T` on a complex Hilbert space has a Hilbert basis of eigenvectors with
real eigenvalues (`exists_hilbertBasis_eigenvectors`): the eigenspaces are closed, mutually
orthogonal and, by Mathlib's `orthogonalComplement_iSup_eigenspaces_eq_bot`, span a dense subspace,
so the union of Hilbert bases of the eigenspaces is a Hilbert basis. For an integral operator with a
Hermitian continuous kernel this gives an eigenbasis of `L²(X, μ)`
(`exists_hilbertBasis_eigenvectors_kernelOp`), and every eigenvector with a non-zero eigenvalue has
the continuous representative `λ⁻¹ (x ↦ ∫ K(x, y) b(y) dμ(y))` (`ae_eq_continuous_of_eigen`).

## Main results

* `exists_hilbertBasis_eigenvectors`, `exists_hilbertBasis_eigenvectors_kernelOp`,
  `ae_eq_continuous_of_eigen`

## References

* P. Garrett, *Compact operators* (notes 09b, 2020), §3, Theorem [3.1], pp. 5–7.
-/

open MeasureTheory Module

universe u

namespace Lightlike.OperatorAlgebras

noncomputable section

section Spectral

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma isClosed_eigenspace (T : E →L[ℂ] E) (μ : ℂ) :
    IsClosed ((End.eigenspace (T : E →ₗ[ℂ] E) μ : Submodule ℂ E) : Set E) := by
  have h := (T - μ • ContinuousLinearMap.id ℂ E).isClosed_ker
  convert h using 1
  ext v
  simp [sub_eq_zero]

/-- **A compact self-adjoint operator has an orthonormal eigenbasis with real eigenvalues.** -/
theorem exists_hilbertBasis_eigenvectors {T : E →L[ℂ] E} (hT : IsCompactOperator T)
    (hS : (T : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ E) (lam : ι → ℝ), ∀ i, T (b i) = (lam i : ℂ) • b i := by
  classical
  set V : ℂ → Submodule ℂ E := fun μ => End.eigenspace (T : E →ₗ[ℂ] E) μ with hV
  have hcomplete : ∀ μ, CompleteSpace (V μ) := fun μ => (isClosed_eigenspace T μ).completeSpace_coe
  have hex : ∀ μ, ∃ (w : Set (V μ)) (b : HilbertBasis w ℂ (V μ)), ⇑b = ((↑) : w → V μ) :=
    fun μ => by have := hcomplete μ; exact exists_hilbertBasis ℂ (V μ)
  choose w b hb using hex
  set v : (Σ μ, w μ) → E := fun a => ((b a.1 a.2 : V a.1) : E) with hvdef
  have hon : Orthonormal ℂ v :=
    hS.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hperp : ∀ μ, ∀ y ∈ V μ, inner ℂ y x = 0 := by
      intro μ y hy
      -- the closed set of `z ∈ V μ` orthogonal to `x` contains the basis, hence everything
      have hcl : IsClosed {z : V μ | inner ℂ (z : E) x = 0} :=
        isClosed_eq ((continuous_subtype_val).inner continuous_const) continuous_const
      have hbase : ∀ j, inner ℂ ((b μ j : V μ) : E) x = 0 := fun j =>
        Submodule.inner_right_of_mem_orthogonal (K := Submodule.span ℂ (Set.range v))
          (Submodule.subset_span (Set.mem_range_self (f := v) ⟨μ, j⟩)) hx
      have hspan : (Submodule.span ℂ (Set.range (b μ)) : Set (V μ)) ⊆
          {z : V μ | inner ℂ (z : E) x = 0} := by
        intro z hz
        refine Submodule.span_induction (R := ℂ) (M := V μ) (s := Set.range (b μ))
          (p := fun z _ => inner ℂ ((z : V μ) : E) x = 0) ?_ ?_ ?_ ?_ hz
        · rintro _ ⟨j, rfl⟩; exact hbase j
        · simp
        · intro u v _ _ hu hv; simp [hu, hv]
        · intro c u _ hu; simp [hu]
      have hall : closure (Submodule.span ℂ (Set.range (b μ)) : Set (V μ)) ⊆
          {z : V μ | inner ℂ (z : E) x = 0} := closure_minimal hspan hcl
      rw [← Submodule.topologicalClosure_coe, (b μ).dense_span, Submodule.top_coe] at hall
      exact hall (Set.mem_univ (⟨y, hy⟩ : V μ))
    have hle : (⨆ μ, V μ) ≤ (ℂ ∙ x)ᗮ := iSup_le fun μ y hy =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.2 (hperp μ y hy)
    have hmem : x ∈ (⨆ μ, V μ)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hy)
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hS] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  set B := HilbertBasis.mkOfOrthogonalEqBot hon hsp with hB
  have hBv : ⇑B = v := HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp
  refine ⟨Σ μ, w μ, B, fun a => a.1.re, fun a => ?_⟩
  have hmemV : v a ∈ V a.1 := (b a.1 a.2).2
  have heig : T (v a) = a.1 • v a := End.mem_eigenspace_iff.1 hmemV
  have hne : v a ≠ 0 := by
    intro h0
    have := hon.1 a
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hreal : (starRingEnd ℂ) a.1 = a.1 :=
    hS.conj_eigenvalue_eq_self (End.hasEigenvalue_of_hasEigenvector ⟨hmemV, hne⟩)
  have hre : ((a.1.re : ℝ) : ℂ) = a.1 := Complex.conj_eq_iff_re.1 hreal
  rw [hBv, hre]
  exact heig

end Spectral

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- **An eigenbasis of an integral operator with a Hermitian continuous kernel.** -/
theorem exists_hilbertBasis_eigenvectors_kernelOp [SecondCountableTopology X] (K : C(X × X, ℂ))
    (hK : ∀ x y, K (y, x) = starRingEnd ℂ (K (x, y))) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (lam : ι → ℝ),
      ∀ i, kernelOp μ K (b i) = (lam i : ℂ) • b i :=
  exists_hilbertBasis_eigenvectors (isCompactOperator_kernelOp μ K) (isSymmetric_kernelOp μ K hK)

/-- **Eigenvectors with non-zero eigenvalue are continuous**: if `T_K b = λ b` with `λ ≠ 0`, then `b`
agrees almost everywhere with the continuous function `λ⁻¹ (x ↦ ∫ K(x, y) b(y) dμ(y))`. -/
theorem ae_eq_continuous_of_eigen (K : C(X × X, ℂ)) {b : Lp ℂ 2 μ} {lam : ℂ} (hlam : lam ≠ 0)
    (hb : kernelOp μ K b = lam • b) :
    (b : X → ℂ) =ᵐ[μ] fun x => lam⁻¹ * kernelToC μ K b x := by
  have h1 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelToC μ K b)
  have h2 := Lp.coeFn_smul lam b
  have e : (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (kernelToC μ K b)) = lam • b := hb
  rw [e] at h1
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx2, Pi.smul_apply, smul_eq_mul] at hx1
  rw [← hx1, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

end

end Lightlike.OperatorAlgebras
