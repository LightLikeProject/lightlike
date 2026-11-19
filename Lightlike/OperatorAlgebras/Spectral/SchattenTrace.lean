import Lightlike.OperatorAlgebras.Spectral.SchattenHS
import Lightlike.OperatorAlgebras.TraceClass.GeneralProduct

/-!
# `J₁` is the trace class

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.3, p. 142 ("`J₁(H)` is the space of trace class
operators") and Lemma 6.13, pp. 142-143: an operator is trace class iff it is the product `K = K₁ K₂` of two
Hilbert–Schmidt operators, and then `‖K‖₁ ≤ ‖K₁‖₂ ‖K₂‖₂` (6.24).

* `sum_norm_sq_le_tsum_of_isHilbertSchmidt`: `∑ₖ ‖S uₖ‖² ≤ ∑ᵢ ‖S eᵢ‖²` for a finite orthonormal family `u`;
* `schattenSum_one_mul_le`: (6.24), `‖K₁ K₂‖₁ ≤ ‖K₁*‖₂ ‖K₂‖₂` for Hilbert–Schmidt `K₁`, `K₂`;
* `abs_apply_of_adjoint_apply_apply`: `|K| v = √μ v` when `K*K v = μ v`;
* `isTraceClass_iff`: `K` is trace class (the repository's `IsTraceClass`, `∑ᵢ ⟪eᵢ, |K| eᵢ⟫ < ∞`) iff `K` is compact and
  `‖K‖₁ < ∞`.
-/

open scoped InnerProductSpace NNReal ENNReal

namespace Lightlike.OperatorAlgebras.CompactSpectral

open TraceClass TraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A finite orthonormal family sees at most the Hilbert–Schmidt sum**: `∑ₖ ‖S uₖ‖² ≤ ∑ᵢ ‖S eᵢ‖²` (extend `u` to a
Hilbert basis; the square sum does not depend on the basis). -/
lemma sum_norm_sq_le_tsum_of_isHilbertSchmidt {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) {n : ℕ} {u : Fin n → H}
    (hu : Orthonormal ℂ u) {w : Set H} (b : HilbertBasis w ℂ H) :
    ∑ k, ‖S (u k)‖ ^ 2 ≤ ∑' i, ‖S (b i)‖ ^ 2 := by
  classical
  have hinj : Function.Injective u := hu.linearIndependent.injective
  have hs : Orthonormal ℂ ((↑) : Set.range u → H) := (orthonormal_subtype_range hinj).mpr hu
  obtain ⟨w', c, hsub, hc⟩ := hs.exists_hilbertBasis_extension
  have hsc := summable_norm_sq_apply_of_hilbertBasis w' c hS
  have hbc := hasSum_norm_sq_apply_of_basis c b hsc
  rw [hbc.tsum_eq]
  let g : Fin n → w' := fun k => ⟨u k, hsub ⟨k, rfl⟩⟩
  have hg : Function.Injective g := fun k l h => hinj (congrArg Subtype.val h)
  have hsum : ∑ k, ‖S (u k)‖ ^ 2 = ∑ i ∈ Finset.univ.image g, ‖S (c i)‖ ^ 2 := by
    rw [Finset.sum_image fun k _ l _ h => hg h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc]
  rw [hsum]
  exact hsc.sum_le_tsum _ fun _ _ => sq_nonneg _

/-- **(6.24)** (Teschl, Lemma 6.13, p. 143): `‖K₁ K₂‖₁ ≤ ‖K₁*‖₂ ‖K₂‖₂` for Hilbert–Schmidt `K₁`, `K₂`, from
`|⟪ψₖ, K₁ K₂ ϕₖ⟫| = |⟪K₁* ψₖ, K₂ ϕₖ⟫|` and Cauchy–Schwarz. -/
theorem schattenSum_one_mul_le {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    schattenSum 1 (A * B) ≤ ENNReal.ofReal
      (Real.sqrt (∑' i, ‖ContinuousLinearMap.adjoint A (b i)‖ ^ 2) * Real.sqrt (∑' i, ‖B (b i)‖ ^ 2)) := by
  have hA' : IsHilbertSchmidt (ContinuousLinearMap.adjoint A) := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using isHilbertSchmidt_star hA
  refine iSup_le fun n => iSup_le fun ψ => iSup_le fun ϕ => iSup_le fun hψϕ => ?_
  obtain ⟨hψ, hϕ⟩ := hψϕ
  have hterm : ∀ k, ‖⟪ψ k, (A * B) (ϕ k)⟫_ℂ‖ₑ ^ (1 : ℝ) =
      ENNReal.ofReal ‖⟪ContinuousLinearMap.adjoint A (ψ k), B (ϕ k)⟫_ℂ‖ := by
    intro k
    rw [ENNReal.rpow_one, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
      ofReal_norm]
  simp only [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => norm_nonneg _]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∑ k, ‖⟪ContinuousLinearMap.adjoint A (ψ k), B (ϕ k)⟫_ℂ‖
      ≤ ∑ k, ‖ContinuousLinearMap.adjoint A (ψ k)‖ * ‖B (ϕ k)‖ :=
        Finset.sum_le_sum fun k _ => norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ k, ‖ContinuousLinearMap.adjoint A (ψ k)‖ ^ 2) * Real.sqrt (∑ k, ‖B (ϕ k)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := by
        gcongr
        · exact sum_norm_sq_le_tsum_of_isHilbertSchmidt hA' hψ b
        · exact sum_norm_sq_le_tsum_of_isHilbertSchmidt hB hϕ b

/-- **`|K| v = √μ v` when `K*K v = μ v`**: `|K|² = K*K` and `|K| ≥ 0`, so `|K| + √μ` is injective for `μ > 0`, and
`‖|K| v‖² = ⟪v, K*K v⟫ = 0` for `μ = 0`. -/
lemma abs_apply_of_adjoint_apply_apply {K : H →L[ℂ] H} {v : H} {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hv : ContinuousLinearMap.adjoint K (K v) = (μ : ℂ) • v) :
    CFC.abs K v = ((Real.sqrt μ : ℝ) : ℂ) • v := by
  set A := CFC.abs K
  have hA : 0 ≤ A := CFC.abs_nonneg K
  have hApos := ContinuousLinearMap.nonneg_iff_isPositive.mp hA
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hAAv : A (A v) = (μ : ℂ) • v := by
    have h1 : (A * A) v = (star K * K) v := by rw [CFC.abs_mul_abs]
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint] at h1
    rw [h1, hv]
  set c : ℝ := Real.sqrt μ
  have hcc : (c : ℂ) * c = μ := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hμ0]
  set w := A v - (c : ℂ) • v
  have hw : A w + (c : ℂ) • w = 0 := by
    simp only [w, map_sub, map_smul, hAAv, smul_sub, smul_smul, hcc]
    abel
  have hre : (⟪w, A w⟫_ℂ).re + c * ‖w‖ ^ 2 = 0 := by
    have := congrArg (fun x => (⟪w, x⟫_ℂ).re) hw
    simp only [inner_add_right, inner_smul_right, inner_zero_right, Complex.add_re, Complex.zero_re] at this
    rw [inner_self_eq_norm_sq_to_K] at this
    simpa [← Complex.ofReal_pow, Complex.mul_re] using this
  have hnn : 0 ≤ (⟪w, A w⟫_ℂ).re := by
    have := hApos.re_inner_nonneg_right w
    simpa using this
  by_cases hμ : μ = 0
  · -- `μ = 0`: `‖A v‖² = ⟪v, A (A v)⟫ = 0`
    have hc0 : c = 0 := by simp [c, hμ]
    have h0 : ‖A v‖ ^ 2 = 0 := by
      have h := hsa.isSymmetric v (A v)
      simp only [ContinuousLinearMap.coe_coe] at h
      rw [hAAv, hμ] at h
      simp only [Complex.ofReal_zero, zero_smul, inner_zero_right] at h
      have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (A v)
      rw [h] at h2
      exact Complex.ofReal_eq_zero.mp (by push_cast; exact h2.symm)
    rw [hc0, Complex.ofReal_zero, zero_smul]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  · have hc : 0 < c := Real.sqrt_pos.mpr (lt_of_le_of_ne hμ0 (Ne.symm hμ))
    have hw0 : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖]
    have : w = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hw0)
    exact sub_eq_zero.mp this

/-- **`J₁` is the trace class** (Teschl, p. 142 and Lemma 6.13): `K` is trace class (the repository's `IsTraceClass`)
iff `K` is compact and `‖K‖₁ < ∞`. -/
theorem isTraceClass_iff {K : H →L[ℂ] H} : IsTraceClass K ↔ IsCompactOperator K ∧ schattenSum 1 K < ⊤ := by
  constructor
  · intro hK
    obtain ⟨hUS, hS, heq⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hK
    obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
    refine ⟨?_, ?_⟩
    · rw [← heq]
      show IsCompactOperator (⇑(Polar.polarFactor K * CFC.sqrt (CFC.abs K)) ∘ ⇑(CFC.sqrt (CFC.abs K)))
      exact (isCompactOperator_of_isHilbertSchmidt hS).clm_comp _
    · rw [← heq]
      exact (schattenSum_one_mul_le hUS hS b).trans_lt ENNReal.ofReal_lt_top
  · rintro ⟨hK, hlt⟩
    -- a Hilbert basis of eigenvectors of `K*K`
    obtain ⟨s, b, μ, -, hμ⟩ :=
      exists_hilbertBasis_eigenvectors (isCompactOperator_adjoint_comp hK) (isSymmetric_adjoint_comp K)
    have hμ' : ∀ i, ContinuousLinearMap.adjoint K (K (b i)) = (μ i : ℂ) • b i := hμ
    have hμ0 : ∀ i, 0 ≤ μ i := by
      intro i
      have h := congrArg (fun x => (⟪b i, x⟫_ℂ).re) (hμ' i)
      simp only [ContinuousLinearMap.adjoint_inner_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
        b.orthonormal.1 i] at h
      have : (μ i : ℝ) = ‖K (b i)‖ ^ 2 := by simpa [← Complex.ofReal_pow] using h.symm
      rw [this]; positivity
    have hc := isCanonicalForm_of_eigenbasis hK b μ hμ'
    rw [schattenSum_eq_tsum hc le_rfl] at hlt
    simp only [ENNReal.rpow_one] at hlt
    -- `∑ⱼ √μⱼ < ∞` over the positive `μⱼ`, hence over all `i`
    have hsumJ : Summable fun j : {i // 0 < μ i} => Real.sqrt (μ j) := by
      have h := hlt.ne
      simp_rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)] at h
      rw [ENNReal.tsum_coe_ne_top_iff_summable] at h
      exact (NNReal.summable_coe.mpr h).congr fun j => rfl
    have hsum : Summable fun i => Real.sqrt (μ i) := by
      refine (summable_subtype_iff_indicator (f := fun i => Real.sqrt (μ i)) (s := {i | 0 < μ i})).mp hsumJ
        |>.congr fun i => ?_
      by_cases hi : 0 < μ i
      · simp [hi]
      · have : μ i = 0 := le_antisymm (not_lt.mp hi) (hμ0 i)
        simp [this]
    refine ⟨s, b, hsum.congr fun i => ?_⟩
    rw [abs_apply_of_adjoint_apply_apply (hμ0 i) (hμ' i), inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 i]
    simp

end Lightlike.OperatorAlgebras.CompactSpectral
