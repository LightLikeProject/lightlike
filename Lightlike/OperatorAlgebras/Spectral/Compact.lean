import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The spectral theorem for compact self-adjoint operators

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.2, Theorem 6.6, p. 136: if `K` is self-adjoint and
compact, the spectrum of `K` consists of an at most countable number of eigenvalues which can only cluster at `0`, the
eigenspace to each nonzero eigenvalue is finite dimensional, and `K = ∑_{λ ∈ σ(K)} λ P_K({λ})` (6.5).

## Main results

For a compact symmetric operator `T` on a complex or real Hilbert space `E`:

* `exists_hilbertBasis_eigenvectors`: `E` has a Hilbert basis of eigenvectors of `T` with real eigenvalues.
* `hasSum_eigen`: `T x = ∑ᵢ μᵢ ⟪bᵢ, x⟫ bᵢ` in such a basis, the expansion (6.5).
* `finite_eigenvalues_ge`: for `ε > 0` only finitely many eigenvalues have `‖μ‖ ≥ ε`, so they can only cluster at `0`.
* `countable_eigenvalues`: the set of eigenvalues is countable.
* `hasEigenvalue_of_mem_spectrum`: every nonzero point of the spectrum is an eigenvalue (Mathlib's Fredholm alternative).
* `finiteDimensional_eigenspace`: the eigenspace to a nonzero eigenvalue is finite dimensional (Mathlib).

Mathlib already proves that the eigenspaces of `T` span a dense subspace
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`), and this file collects their Hilbert bases.
-/

open scoped InnerProductSpace
open Module End

namespace Lightlike.OperatorAlgebras.CompactSpectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An eigenspace of a bounded operator is closed. -/
lemma isClosed_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : Module.End 𝕜 E) μ : Set E) := by
  have : (eigenspace (T : Module.End 𝕜 E) μ : Set E) = (T - μ • ContinuousLinearMap.id 𝕜 E) ⁻¹' {0} := by
    ext v; simp [sub_eq_zero]
  rw [this]
  exact isClosed_singleton.preimage (map_continuous _)

variable [CompleteSpace E]

/-- An eigenspace of a bounded operator on a Hilbert space is complete. -/
instance completeSpace_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    CompleteSpace (eigenspace (T : Module.End 𝕜 E) μ) :=
  (isClosed_eigenspace T μ).completeSpace_coe

omit [CompleteSpace E] in
/-- An eigenvalue of a symmetric operator is real. -/
lemma exists_real_of_hasEigenvalue {T : E →L[𝕜] E} (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) {μ : 𝕜}
    (hμ : HasEigenvalue (T : Module.End 𝕜 E) μ) : ((RCLike.re μ : ℝ) : 𝕜) = μ :=
  RCLike.conj_eq_iff_re.mp (hT'.conj_eigenvalue_eq_self hμ)

/-- **A compact symmetric operator on a Hilbert space has a Hilbert basis of eigenvectors, with real eigenvalues**
(Teschl, Theorem 6.6, p. 136). The basis is a set `s` of unit vectors. -/
theorem exists_hilbertBasis_eigenvectors {T : E →L[𝕜] E} (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (s : Set E) (b : HilbertBasis s 𝕜 E) (μ : s → ℝ), ⇑b = (↑) ∧ ∀ i, T (b i) = (μ i : 𝕜) • b i := by
  classical
  have hortho : OrthogonalFamily 𝕜 (fun μ => eigenspace (T : Module.End 𝕜 E) μ)
      fun μ => (eigenspace (T : Module.End 𝕜 E) μ).subtypeₗᵢ := hT'.orthogonalFamily_eigenspaces
  have hb : ∀ μ, ∃ (w : Set (eigenspace (T : Module.End 𝕜 E) μ))
      (b : HilbertBasis w 𝕜 (eigenspace (T : Module.End 𝕜 E) μ)), ⇑b = (↑) :=
    fun μ => exists_hilbertBasis 𝕜 _
  choose w b _ using hb
  let v : (Σ μ, w μ) → E := fun a => (eigenspace (T : Module.End 𝕜 E) a.1).subtypeₗᵢ (b a.1 a.2)
  have hv : Orthonormal 𝕜 v := hortho.orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal
  have hvmem : ∀ a, v a ∈ eigenspace (T : Module.End 𝕜 E) a.1 := fun a => (b a.1 a.2).2
  -- every eigenspace lies in the closed span of `v`
  have hF : ∀ μ, eigenspace (T : Module.End 𝕜 E) μ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure := by
    intro μ x hx
    have hmem : (⟨x, hx⟩ : eigenspace (T : Module.End 𝕜 E) μ) ∈
        closure (Submodule.span 𝕜 (Set.range (b μ)) : Set (eigenspace (T : Module.End 𝕜 E) μ)) := by
      rw [← Submodule.topologicalClosure_coe, (b μ).dense_span]; trivial
    have hmaps : Set.MapsTo ((↑) : eigenspace (T : Module.End 𝕜 E) μ → E)
        (Submodule.span 𝕜 (Set.range (b μ))) (Submodule.span 𝕜 (Set.range v)) := by
      intro y hy
      have hle : Submodule.map (eigenspace (T : Module.End 𝕜 E) μ).subtype
          (Submodule.span 𝕜 (Set.range (b μ))) ≤ Submodule.span 𝕜 (Set.range v) := by
        rw [Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
      exact hle (Submodule.mem_map_of_mem hy)
    have := map_mem_closure continuous_subtype_val hmem hmaps
    rwa [← Submodule.topologicalClosure_coe] at this
  have hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure := by
    have hcl : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ).topologicalClosure = ⊤ := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure,
        ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT', Submodule.bot_orthogonal_eq_top]
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ (iSup_le hF) (Submodule.isClosed_topologicalClosure _)
  -- re-index by the range of `v`
  have hinj : Function.Injective v := hv.linearIndependent.injective
  have hv' : Orthonormal 𝕜 ((↑) : Set.range v → E) := (orthonormal_subtype_range hinj).mpr hv
  have hsp' : ⊤ ≤ (Submodule.span 𝕜 (Set.range ((↑) : Set.range v → E))).topologicalClosure := by
    rwa [Subtype.range_coe]
  have hreal : ∀ x : Set.range v, ∃ r : ℝ, T x = (r : 𝕜) • (x : E) := by
    rintro ⟨_, a, rfl⟩
    have hne : v a ≠ 0 := hv.ne_zero a
    have hev : HasEigenvalue (T : Module.End 𝕜 E) a.1 :=
      hasEigenvalue_of_hasEigenvector ⟨by simpa using hvmem a, hne⟩
    refine ⟨RCLike.re a.1, ?_⟩
    rw [exists_real_of_hasEigenvalue hT' hev]
    exact mem_eigenspace_iff.mp (hvmem a)
  choose μ hμ using hreal
  refine ⟨Set.range v, HilbertBasis.mk hv' hsp', μ, HilbertBasis.coe_mk hv' hsp', fun i => ?_⟩
  rw [HilbertBasis.coe_mk]
  exact hμ i

omit [CompleteSpace E] in
/-- **The expansion (6.5)** (Teschl, Theorem 6.6, p. 136): in a Hilbert basis of eigenvectors,
`T x = ∑ᵢ μᵢ ⟪bᵢ, x⟫ bᵢ`. -/
theorem hasSum_eigen {ι : Type*} {T : E →L[𝕜] E} (b : HilbertBasis ι 𝕜 E) (μ : ι → 𝕜)
    (hμ : ∀ i, T (b i) = μ i • b i) (x : E) :
    HasSum (fun i => (μ i * ⟪b i, x⟫_𝕜) • b i) (T x) := by
  have h := (b.hasSum_repr x).mapL T
  simp only [map_smul, hμ, smul_smul, HilbertBasis.repr_apply_apply] at h
  convert h using 2 with i
  ring

omit [CompleteSpace E] in
/-- **Only finitely many eigenvalues have `‖μ‖ ≥ ε`** (Teschl, Theorem 6.6, p. 136: the eigenvalues can only cluster at
`0`). Unit eigenvectors to distinct eigenvalues are orthonormal, so their images under `T` are at least `ε` apart, while
the image of the unit ball is relatively compact. -/
theorem finite_eigenvalues_ge {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric)
    {ε : ℝ} (hε : 0 < ε) :
    {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ ε ≤ ‖μ‖}.Finite := by
  by_contra hinf
  let f := (Set.not_finite.mp hinf |>.natEmbedding)
  let m : ℕ → 𝕜 := fun n => (f n : 𝕜)
  have hm : ∀ n, HasEigenvalue (T : Module.End 𝕜 E) (m n) ∧ ε ≤ ‖m n‖ := fun n => (f n).2
  have hminj : Function.Injective m := fun i j h => f.injective (Subtype.ext h)
  -- unit eigenvectors
  have hvec : ∀ n, ∃ v : E, T v = m n • v ∧ ‖v‖ = 1 := by
    intro n
    obtain ⟨v, hv, hv0⟩ := (hm n).1.exists_hasEigenvector
    refine ⟨(‖v‖⁻¹ : 𝕜) • v, ?_, ?_⟩
    · rw [map_smul, show T v = m n • v from mem_eigenspace_iff.mp (by simpa using hv), smul_comm]
    · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  choose v hTv hv1 using hvec
  have horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_𝕜 = 0 := by
    intro i j hij
    have hi : v i ∈ eigenspace (T : Module.End 𝕜 E) (m i) := mem_eigenspace_iff.mpr (by simpa using hTv i)
    have hj : v j ∈ eigenspace (T : Module.End 𝕜 E) (m j) := mem_eigenspace_iff.mpr (by simpa using hTv j)
    exact hT'.orthogonalFamily_eigenspaces (hminj.ne hij) ⟨v i, hi⟩ ⟨v j, hj⟩
  have hsep : ∀ i j, i ≠ j → ε ≤ dist (T (v i)) (T (v j)) := by
    intro i j hij
    rw [dist_eq_norm, hTv, hTv]
    have hsq : ‖m i • v i - m j • v j‖ ^ 2 = ‖m i‖ ^ 2 + ‖m j‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_left, inner_smul_right, horth i j hij, norm_smul, norm_smul, hv1, hv1]
      simp
    have h1 : ε ^ 2 ≤ ‖m i • v i - m j • v j‖ ^ 2 := by
      rw [hsq]
      nlinarith [(hm i).2, (hm j).2, sq_nonneg ‖m j‖]
    exact (pow_le_pow_iff_left₀ hε.le (norm_nonneg _) two_ne_zero).mp h1
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (1 : ℝ)
  have hmemK : ∀ n, T (v n) ∈ K := fun n =>
    hTK ⟨v n, by rw [mem_closedBall_zero_iff, hv1], rfl⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmemK
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  have hne : φ N ≠ φ (N + 1) := (hφ (Nat.lt_succ_self N)).ne
  have := hsep _ _ hne
  have htri := dist_triangle_right (T (v (φ N))) (T (v (φ (N + 1)))) a
  simp only [Function.comp] at h1 h2
  linarith

omit [CompleteSpace E] in
/-- **The eigenvalues are countable** (Teschl, Theorem 6.6, p. 136). -/
theorem countable_eigenvalues {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ}.Countable := by
  have hsub : {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ} ⊆
      insert 0 (⋃ n : ℕ, {μ : 𝕜 | HasEigenvalue (T : Module.End 𝕜 E) μ ∧ 1 / ((n : ℝ) + 1) ≤ ‖μ‖}) := by
    intro μ hμ
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · right
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr h0)
      exact Set.mem_iUnion.mpr ⟨n, hμ, hn.le⟩
  refine Set.Countable.mono hsub (Set.Countable.insert _ (Set.countable_iUnion fun n => ?_))
  exact (finite_eigenvalues_ge hT hT' (by positivity)).countable

/-- **A nonzero point of the spectrum is an eigenvalue** (Teschl, Theorem 6.6, p. 136; Mathlib's Fredholm
alternative). -/
theorem hasEigenvalue_of_mem_spectrum {T : E →L[𝕜] E} (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0)
    (h : μ ∈ spectrum 𝕜 T) : HasEigenvalue (T : Module.End 𝕜 E) μ :=
  (hT.hasEigenvalue_iff_mem_spectrum hμ).mpr h

/-- **The spectrum is countable** (Teschl, Theorem 6.6, p. 136). -/
theorem countable_spectrum {T : E →L[𝕜] E} (hT : IsCompactOperator T) (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    (spectrum 𝕜 T).Countable := by
  refine Set.Countable.mono (fun μ hμ => ?_) ((countable_eigenvalues hT hT').insert 0)
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · exact Or.inr (hasEigenvalue_of_mem_spectrum hT h0 hμ)

/-- **The eigenspace to a nonzero eigenvalue is finite dimensional** (Teschl, Theorem 6.6, p. 136; Mathlib). -/
theorem finiteDimensional_eigenspace {T : E →L[𝕜] E} (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace (T : Module.End 𝕜 E) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ

end Lightlike.OperatorAlgebras.CompactSpectral
