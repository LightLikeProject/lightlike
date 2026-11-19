import Lightlike.OperatorAlgebras.Spectral.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The canonical form of a compact operator: singular values

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.2, Theorem 6.7, p. 137: for a compact operator `K` there
are orthonormal sets `{φ̂ⱼ}`, `{φⱼ}` and positive numbers `sⱼ = sⱼ(K)` with
`K = ∑ⱼ sⱼ ⟪φⱼ, ·⟫ φ̂ⱼ` and `K* = ∑ⱼ sⱼ ⟪φ̂ⱼ, ·⟫ φⱼ` (6.6); `Kφⱼ = sⱼ φ̂ⱼ`, `K*φ̂ⱼ = sⱼ φⱼ`, `K*Kφⱼ = sⱼ² φⱼ`,
`KK*φ̂ⱼ = sⱼ² φ̂ⱼ`; the `sⱼ²` are the nonzero eigenvalues of `K*K`, and there are finitely many singular values or they
converge to zero. The proof applies Theorem 6.6 to `K*K`.

* `isCompactOperator_adjoint_comp`, `isSymmetric_adjoint_comp`: `K*K` is compact and symmetric;
* `IsCanonicalForm K φ φ' s`: the canonical form (6.6), with the relations above, and `{j | ε ≤ sⱼ}` finite for every
  `ε > 0`;
* `isCanonicalForm_of_eigenbasis`, `exists_isCanonicalForm`: every compact operator has one, built from a Hilbert basis
  of eigenvectors of `K*K`;
* `IsCanonicalForm.le_opNorm`, `IsCanonicalForm.opNorm_le`: `‖K‖ = sup sⱼ` (6.7), for every canonical form;
* `hasSum_norm_sq_of_orthonormal`: `‖∑ⱼ cⱼ vⱼ‖² = ∑ⱼ |cⱼ|²` for an orthonormal family `v`.
-/

open scoped InnerProductSpace
open Module End

universe u

namespace Lightlike.OperatorAlgebras.CompactSpectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

open ContinuousLinearMap in
/-- `K*K` is compact when `K` is. -/
lemma isCompactOperator_adjoint_comp {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    IsCompactOperator (adjoint K ∘L K) := by
  rw [ContinuousLinearMap.coe_comp]
  exact hK.clm_comp (adjoint K)

open ContinuousLinearMap in
/-- `K*K` is symmetric. -/
lemma isSymmetric_adjoint_comp (K : E →L[𝕜] E) : ((adjoint K ∘L K : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, adjoint_inner_left, adjoint_inner_right]

/-- **A canonical form of `K`** (Teschl, Theorem 6.7, p. 137): orthonormal families `φ`, `φ'` and positive numbers `s`
(the singular values) with `K x = ∑ⱼ sⱼ ⟪φⱼ, x⟫ φ'ⱼ`, `K* x = ∑ⱼ sⱼ ⟪φ'ⱼ, x⟫ φⱼ`, `K φⱼ = sⱼ φ'ⱼ`, `K* φ'ⱼ = sⱼ φⱼ`,
`K*K φⱼ = sⱼ² φⱼ`, `KK* φ'ⱼ = sⱼ² φ'ⱼ`, and only finitely many `sⱼ ≥ ε` for every `ε > 0`. -/
structure IsCanonicalForm {ι : Type*} (K : E →L[𝕜] E) (φ φ' : ι → E) (s : ι → ℝ) : Prop where
  /-- `φ` is orthonormal. -/
  orthonormal_left : Orthonormal 𝕜 φ
  /-- `φ'` is orthonormal. -/
  orthonormal_right : Orthonormal 𝕜 φ'
  /-- The singular values are positive. -/
  pos : ∀ j, 0 < s j
  /-- `K x = ∑ⱼ sⱼ ⟪φⱼ, x⟫ φ'ⱼ`. -/
  hasSum_apply : ∀ x, HasSum (fun j => ((s j : 𝕜) * ⟪φ j, x⟫_𝕜) • φ' j) (K x)
  /-- `K* x = ∑ⱼ sⱼ ⟪φ'ⱼ, x⟫ φⱼ`. -/
  hasSum_adjoint_apply : ∀ x,
    HasSum (fun j => ((s j : 𝕜) * ⟪φ' j, x⟫_𝕜) • φ j) (ContinuousLinearMap.adjoint K x)
  /-- `K φⱼ = sⱼ φ'ⱼ`. -/
  apply_left : ∀ j, K (φ j) = (s j : 𝕜) • φ' j
  /-- `K* φ'ⱼ = sⱼ φⱼ`. -/
  adjoint_apply_right : ∀ j, ContinuousLinearMap.adjoint K (φ' j) = (s j : 𝕜) • φ j
  /-- `K*K φⱼ = sⱼ² φⱼ`. -/
  adjoint_apply_apply_left : ∀ j, ContinuousLinearMap.adjoint K (K (φ j)) = ((s j ^ 2 : ℝ) : 𝕜) • φ j
  /-- `KK* φ'ⱼ = sⱼ² φ'ⱼ`. -/
  apply_adjoint_apply_right : ∀ j, K (ContinuousLinearMap.adjoint K (φ' j)) = ((s j ^ 2 : ℝ) : 𝕜) • φ' j
  /-- Only finitely many singular values are at least `ε`. -/
  finite_ge : ∀ ε > 0, {j | ε ≤ s j}.Finite

open ContinuousLinearMap in
/-- **The canonical form from a Hilbert basis of eigenvectors of `K*K`** (Teschl, Theorem 6.7 and its proof, p. 137):
if `K*K bᵢ = μᵢ bᵢ`, then `φⱼ = bⱼ`, `sⱼ = √μⱼ` and `φ'ⱼ = sⱼ⁻¹ K bⱼ` over the `j` with `μⱼ > 0` are a canonical form. -/
theorem isCanonicalForm_of_eigenbasis {K : E →L[𝕜] E} (hK : IsCompactOperator K) {S : Type*}
    (b : HilbertBasis S 𝕜 E) (μ : S → ℝ) (hμ' : ∀ i, adjoint K (K (b i)) = (μ i : 𝕜) • b i) :
    IsCanonicalForm K (fun j : {i // 0 < μ i} => b j) (fun j => ((Real.sqrt (μ j))⁻¹ : 𝕜) • K (b j))
      (fun j => Real.sqrt (μ j)) := by
  classical
  -- the Gram matrix of the `K bᵢ`
  have hinner : ∀ i j, ⟪K (b i), K (b j)⟫_𝕜 = (μ j : 𝕜) * ⟪b i, b j⟫_𝕜 := by
    intro i j
    rw [← adjoint_inner_right, hμ' j, inner_smul_right]
  have hnorm : ∀ i, ‖K (b i)‖ ^ 2 = μ i := by
    intro i
    have h := hinner i i
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simp only [one_pow, RCLike.ofReal_one, mul_one] at h
    exact_mod_cast h
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => hnorm i ▸ sq_nonneg _
  have hK0 : ∀ i, μ i = 0 → K (b i) = 0 := fun i h => by
    have h2 : ‖K (b i)‖ ^ 2 = 0 := by rw [hnorm i, h]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  let J : Set S := {i | 0 < μ i}
  let sv : J → ℝ := fun j => Real.sqrt (μ j)
  have hsv : ∀ j : J, 0 < sv j := fun j => Real.sqrt_pos.mpr j.2
  have hsvK : ∀ j : J, ‖K (b j)‖ = sv j := fun j => by
    rw [← Real.sqrt_sq (norm_nonneg _), hnorm]
  let φ : J → E := fun j => b j
  let φ' : J → E := fun j => ((sv j)⁻¹ : 𝕜) • K (b j)
  have hKφ : ∀ j : J, K (φ j) = (sv j : 𝕜) • φ' j := fun j => by
    simp only [φ, φ', smul_smul]
    rw [mul_inv_cancel₀ (by exact_mod_cast (hsv j).ne'), one_smul]
  have hsvsq : ∀ j : J, sv j ^ 2 = μ j := fun j => Real.sq_sqrt (hμ0 j)
  have hbinner : ∀ i j : J, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := by
    intro i j
    have := (orthonormal_iff_ite.mp b.orthonormal) i j
    rw [this]
    by_cases h : i = j
    · simp [h]
    · have : (i : S) ≠ j := fun h' => h (Subtype.ext h')
      simp [h, this]
  have hφ : Orthonormal 𝕜 φ := b.orthonormal.comp _ Subtype.val_injective
  have hφ' : Orthonormal 𝕜 φ' := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [φ', inner_smul_left, inner_smul_right, hinner, hbinner]
    by_cases h : i = j
    · subst h
      simp only [if_true, mul_one, map_inv₀, RCLike.conj_ofReal]
      rw [← hsvsq i]
      have : (sv i : 𝕜) ≠ 0 := by exact_mod_cast (hsv i).ne'
      push_cast
      field_simp
    · simp [h]
  -- the expansion of `K x`
  have hKx : ∀ x, HasSum (fun j : J => ((sv j : 𝕜) * ⟪φ j, x⟫_𝕜) • φ' j) (K x) := by
    intro x
    have h := (b.hasSum_repr x).mapL K
    simp only [map_smul, HilbertBasis.repr_apply_apply] at h
    have hsupp : Function.support (fun i : S => ⟪b i, x⟫_𝕜 • K (b i)) ⊆ J := by
      intro i hi
      by_contra hJ
      have : μ i = 0 := le_antisymm (not_lt.mp hJ) (hμ0 i)
      exact hi (by simp [hK0 i this])
    have := (hasSum_subtype_iff_of_support_subset hsupp).mpr h
    convert this using 2 with j
    have hne : (sv j : 𝕜) ≠ 0 := by exact_mod_cast (hsv j).ne'
    simp only [Function.comp_apply, φ, φ', smul_smul]
    congr 1
    field_simp
  -- the expansion of `K* x`
  have hKadx : ∀ x, HasSum (fun j : J => ((sv j : 𝕜) * ⟪φ' j, x⟫_𝕜) • φ j) (adjoint K x) := by
    intro x
    have h := b.hasSum_repr (adjoint K x)
    simp only [HilbertBasis.repr_apply_apply, adjoint_inner_right] at h
    have hsupp : Function.support (fun i : S => ⟪K (b i), x⟫_𝕜 • b i) ⊆ J := by
      intro i hi
      by_contra hJ
      have : μ i = 0 := le_antisymm (not_lt.mp hJ) (hμ0 i)
      exact hi (by simp [hK0 i this])
    have := (hasSum_subtype_iff_of_support_subset hsupp).mpr h
    convert this using 2 with j
    have hne : (sv j : 𝕜) ≠ 0 := by exact_mod_cast (hsv j).ne'
    simp only [Function.comp_apply, φ, φ', inner_smul_left, map_inv₀, RCLike.conj_ofReal]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hKadφ' : ∀ j : J, adjoint K (φ' j) = (sv j : 𝕜) • φ j := fun j => by
    simp only [φ', map_smul, hμ' j, smul_smul, φ]
    rw [← hsvsq j]
    have : (sv j : 𝕜) ≠ 0 := by exact_mod_cast (hsv j).ne'
    congr 1
    push_cast
    field_simp
  refine ⟨hφ, hφ', hsv, hKx, hKadx, hKφ, hKadφ', fun j => ?_, fun j => ?_, ?_⟩
  · show adjoint K (K (φ j)) = ((sv j ^ 2 : ℝ) : 𝕜) • φ j
    rw [hKφ j, map_smul, hKadφ' j, smul_smul]; push_cast; ring_nf
  · show K (adjoint K (φ' j)) = ((sv j ^ 2 : ℝ) : 𝕜) • φ' j
    rw [hKadφ' j, map_smul, hKφ j, smul_smul]; push_cast; ring_nf
  · -- only finitely many singular values `≥ ε`
    intro ε hε
    have hfin := finite_eigenvalues_ge (isCompactOperator_adjoint_comp hK) (isSymmetric_adjoint_comp K)
      (pow_pos hε 2)
    let f : J → 𝕜 := fun j => (μ j : 𝕜)
    have hsub : {j | ε ≤ sv j} ⊆ f ⁻¹' {ν : 𝕜 | HasEigenvalue ((adjoint K ∘L K : E →L[𝕜] E) : Module.End 𝕜 E) ν ∧
        ε ^ 2 ≤ ‖ν‖} := by
      intro j hj
      refine ⟨hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hμ' j), b.orthonormal.ne_zero j⟩, ?_⟩
      simp only [f, RCLike.norm_ofReal, abs_of_nonneg (hμ0 j)]
      rw [← hsvsq j]
      exact pow_le_pow_left₀ hε.le hj 2
    refine Set.Finite.subset (hfin.preimage' fun ν hν => ?_) hsub
    -- the fiber over `ν ≠ 0` is an orthonormal family in a finite-dimensional eigenspace
    have hν0 : ν ≠ 0 := fun h => by
      have := hν.2; rw [h, norm_zero] at this; exact absurd this (not_le.mpr (pow_pos hε 2))
    haveI := finiteDimensional_eigenspace (isCompactOperator_adjoint_comp hK) hν0
    let g : f ⁻¹' {ν} → eigenspace ((adjoint K ∘L K : E →L[𝕜] E) : Module.End 𝕜 E) ν := fun j =>
      ⟨b j.1.1, mem_eigenspace_iff.mpr ((hμ' j.1.1).trans (by rw [show ((μ j.1.1 : ℝ) : 𝕜) = ν from j.2]))⟩
    have hg : Orthonormal 𝕜 g := by
      rw [orthonormal_iff_ite]
      intro i j
      simp only [g, Submodule.coe_inner]
      rw [hbinner]
      by_cases h : i = j
      · simp [h]
      · have : (i : J) ≠ j := fun h' => h (Subtype.ext h')
        simp [h, this]
    have := hg.linearIndependent.finite
    exact Set.toFinite _

/-- **Every compact operator has a canonical form** (Teschl, Theorem 6.7, p. 137): Theorem 6.6 for the compact
symmetric `K*K` and `isCanonicalForm_of_eigenbasis`. -/
theorem exists_isCanonicalForm {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    ∃ (ι : Type u) (φ φ' : ι → E) (s : ι → ℝ), IsCanonicalForm K φ φ' s := by
  obtain ⟨S, b, μ, -, hμ⟩ :=
    exists_hilbertBasis_eigenvectors (isCompactOperator_adjoint_comp hK) (isSymmetric_adjoint_comp K)
  exact ⟨_, _, _, _, isCanonicalForm_of_eigenbasis hK b μ hμ⟩

omit [CompleteSpace E] in
/-- **The norm of an orthonormal expansion**: if `y = ∑ⱼ cⱼ vⱼ` with `v` orthonormal, `‖y‖² = ∑ⱼ |cⱼ|²`. -/
lemma hasSum_norm_sq_of_orthonormal {ι : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) {c : ι → 𝕜} {y : E}
    (h : HasSum (fun j => c j • v j) y) : HasSum (fun j => ‖c j‖ ^ 2) (‖y‖ ^ 2) := by
  classical
  have hc : ∀ k, ⟪v k, y⟫_𝕜 = c k := by
    intro k
    have h' := h.mapL (innerSL 𝕜 (v k))
    simp only [innerSL_apply_apply, inner_smul_right] at h'
    have hfun : (fun j => c j * ⟪v k, v j⟫_𝕜) = fun j => if j = k then c k else 0 := by
      funext j
      rw [orthonormal_iff_ite.mp hv k j]
      by_cases hjk : j = k
      · subst hjk; simp
      · simp [hjk, Ne.symm hjk]
    rw [hfun] at h'
    exact h'.unique (hasSum_ite_eq k (c k))
  have h' := h.mapL (innerSL 𝕜 y)
  simp only [innerSL_apply_apply, inner_smul_right] at h'
  have hfun : (fun j => c j * ⟪y, v j⟫_𝕜) = fun j => ((‖c j‖ ^ 2 : ℝ) : 𝕜) := by
    funext j
    rw [← inner_conj_symm, hc j, RCLike.mul_conj]; push_cast; rfl
  rw [hfun, inner_self_eq_norm_sq_to_K] at h'
  have h'' : HasSum (fun j => ((‖c j‖ ^ 2 : ℝ) : 𝕜)) ((‖y‖ ^ 2 : ℝ) : 𝕜) := by exact_mod_cast h'
  exact (RCLike.hasSum_ofReal 𝕜).mp h''

/-- **A singular value is at most `‖K‖`** (Teschl (6.7), p. 137): `sⱼ = ‖K φⱼ‖`. -/
lemma IsCanonicalForm.le_opNorm {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hc : IsCanonicalForm K φ φ' s) (j : ι) : s j ≤ ‖K‖ := by
  have := K.le_opNorm (φ j)
  rwa [hc.apply_left j, norm_smul, hc.orthonormal_right.1 j, hc.orthonormal_left.1 j, RCLike.norm_ofReal,
    abs_of_nonneg (hc.pos j).le, mul_one, mul_one] at this

/-- **`‖K‖ ≤ M` when every singular value is at most `M`** (Teschl (6.7), p. 137): `‖K x‖² = ∑ⱼ sⱼ² |⟪φⱼ, x⟫|²`
and Bessel's inequality. -/
lemma IsCanonicalForm.opNorm_le {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hc : IsCanonicalForm K φ φ' s) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, s j ≤ M) : ‖K‖ ≤ M := by
  have hφ := hc.orthonormal_left
  have hφ' := hc.orthonormal_right
  have hKx := hc.hasSum_apply
  refine K.opNorm_le_bound hM0 fun x => ?_
  have h := hasSum_norm_sq_of_orthonormal hφ' (hKx x)
  have hb : Summable fun j => ‖⟪φ j, x⟫_𝕜‖ ^ 2 := hφ.inner_products_summable x
  have hle : ‖K x‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
    rw [← h.tsum_eq]
    calc ∑' j, ‖(s j : 𝕜) * ⟪φ j, x⟫_𝕜‖ ^ 2 ≤ ∑' j, M ^ 2 * ‖⟪φ j, x⟫_𝕜‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun j => ?_) h.summable (hb.mul_left _)
          rw [norm_mul, mul_pow, RCLike.norm_ofReal]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _)
            ((abs_of_pos (hc.pos j)).le.trans (hM j)) 2) (sq_nonneg _)
      _ = M ^ 2 * ∑' j, ‖⟪φ j, x⟫_𝕜‖ ^ 2 := tsum_mul_left
      _ ≤ M ^ 2 * ‖x‖ ^ 2 := by gcongr; exact hφ.tsum_inner_products_le x
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (by rw [mul_pow]; exact hle)

end Lightlike.OperatorAlgebras.CompactSpectral
