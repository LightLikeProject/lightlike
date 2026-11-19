import Lightlike.HarmonicAnalysis.PeterWeylBasis
import Lightlike.HarmonicAnalysis.PeterWeylSeparation

/-!
# Completeness of the irreducible matrix coefficients in `L²`

If `χ ∈ L²(G, μ)` is orthogonal to the normalised coefficients of all irreducible representations, then `χ = 0`
(`eq_zero_of_orthogonal_coeffFamily`). The proof follows Tao's Proposition 7: `K_φ χ` vanishes for every
symmetric `φ` because the eigenspaces of `K_φ` are finite sums of minimal invariant subspaces, whose elements
are combinations of coefficients of irreducible representations; then an approximate identity gives
`⟪χ, ψ⟫ = 0` for continuous `ψ`.

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), Proposition 7.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- `χ` is orthogonal to the normalised coefficients of the class representatives. -/
def OrthToCoeff (χ : Lp ℂ 2 μ) : Prop := ∀ a : CoeffIdx G, inner ℂ χ (coeffFamily μ a) = 0

/-- A function orthogonal to the class representatives is orthogonal to every irreducible coefficient. -/
lemma inner_eq_zero_irr {χ : Lp ℂ 2 μ} (hχ : OrthToCoeff μ χ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : UnitaryMatrixRep G ι) (hσ : σ.IsIrreducible) (k l : ι) :
    inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ⟨ι, σ, hσ⟩ k l)) = 0 := by
  let R : IrrRep G := ⟨ι, σ, hσ⟩
  let π : IrrClass G := ⟦R⟧
  have heq : UnitaryMatrixRep.Equivalent (Quotient.out π : IrrRep G).ρ σ :=
    Quotient.exact (Quotient.out_eq π)
  obtain ⟨c, hc⟩ := UnitaryMatrixRep.entry_eq_sum_of_equivalent heq k l
  have hfun : coeffFun R k l = ∑ a, ∑ b, c a b • coeffFun (Quotient.out π : IrrRep G) a b := by
    ext g
    simp only [coeffFun, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    exact hc g
  have hn : ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ) ≠ 0 := by
    haveI := (Quotient.out π : IrrRep G).irr.1
    have : (Fintype.card (Quotient.out π : IrrRep G).ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact_mod_cast Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm this))
  have hab : ∀ a b, inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ
      (coeffFun (Quotient.out π : IrrRep G) a b)) = 0 := by
    intro a b
    have := hχ ⟨π, (a, b)⟩
    simp only [coeffFamily, inner_smul_right] at this
    exact (mul_eq_zero.1 this).resolve_left hn
  rw [hfun]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, hab, mul_zero, Finset.sum_const_zero]

/-- A finite-dimensional left-invariant space of continuous classes is orthogonal to `χ`. -/
lemma inner_eq_zero_of_invariant {χ : Lp ℂ 2 μ} (hχ : OrthToCoeff μ χ)
    (V : Submodule ℂ (Lp ℂ 2 μ)) [FiniteDimensional ℂ V] (hV : IsLeftInvariant μ V)
    (hcont : ∀ v ∈ V, ∃ c : C(G, ℂ), v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c) :
    ∀ v ∈ V, inner ℂ χ v = 0 := by
  obtain ⟨F, hF, hsup⟩ := exists_minimal_decomposition μ (Module.finrank ℂ V) V inferInstance hV le_rfl
  have hle : V ≤ LinearMap.ker (innerSL ℂ χ).toLinearMap := by
    rw [hsup]
    refine Finset.sup_le fun W hW => ?_
    obtain ⟨hmin, hWV⟩ := hF W hW
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWV
    have hcontW : ∀ w ∈ W, ∃ c : C(G, ℂ), w = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c :=
      fun w hw => hcont w (hWV hw)
    let b := stdOrthonormalBasis ℂ W
    have hirr := invRep_isIrreducible μ W hmin.1 b hcontW hmin
    intro v hv
    obtain ⟨c, hc⟩ := hcont v (hWV hv)
    obtain ⟨d, hd⟩ := eq_sum_conj_entries μ W hmin.1 b hcontW c (by rw [← hc]; exact hv)
    have hirr' := hirr.conj
    have hfun : c = ∑ k, ∑ j, d k j •
        coeffFun ⟨_, (invRep μ W hmin.1 b hcontW).conj, hirr'⟩ j k := by
      ext x
      simp only [coeffFun, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      rw [hd x]
      rfl
    show inner ℂ χ v = 0
    rw [hc, hfun]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right,
      inner_eq_zero_irr μ hχ _ hirr', mul_zero, Finset.sum_const_zero]
  intro v hv
  exact hle hv

/-- `K_φ χ = 0` for symmetric `φ`, when `χ` is orthogonal to the irreducible coefficients. -/
theorem convOp_eq_zero_of_orth {χ : Lp ℂ 2 μ} (hχ : OrthToCoeff μ χ) {φ : C(G, ℂ)}
    (hφ : ∀ z, φ z⁻¹ = starRingEnd ℂ (φ z)) : convOp μ φ χ = 0 := by
  have hcpt : IsCompactOperator (convOp μ φ) := isCompactOperator_convOp μ φ
  have hsa : (convOp μ φ).IsSymmetric := (isSelfAdjoint_convOp μ hφ).isSymmetric
  have hdense : (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcpt hsa
  have hle : (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) ≤
      LinearMap.ker (innerSL ℂ (convOp μ φ χ)).toLinearMap := by
    refine iSup_le fun l v hv => ?_
    have hKv : convOp μ φ v = l • v := Module.End.mem_eigenspace_iff.1 hv
    show inner ℂ (convOp μ φ χ) v = 0
    have hsym : inner ℂ (convOp μ φ χ) v = inner ℂ χ (convOp μ φ v) := hsa χ v
    rw [hsym, hKv, inner_smul_right]
    by_cases hl : l = 0
    · simp [hl]
    · haveI : FiniteDimensional ℂ (Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) :=
        ContinuousLinearMap.finite_dimensional_eigenspace (isCompactOperator_convOp μ φ) l hl
      have hI : IsLeftInvariant μ (Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) :=
        fun s w hw => leftTr_mem_eigenspace μ φ s l hw
      have hC : ∀ w ∈ Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l,
          ∃ c : C(G, ℂ), w = ContinuousMap.toLp (E := ℂ) 2 μ ℂ c :=
        fun w hw => ⟨_, eigen_eq_toLp μ φ hl hw⟩
      rw [inner_eq_zero_of_invariant μ hχ _ hI hC v hv, mul_zero]
  have hmem : convOp μ φ χ ∈ (⨆ l, Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact hle hv
  rw [hdense] at hmem
  simpa using hmem

/-- **Completeness.** A function orthogonal to all irreducible matrix coefficients is zero. -/
theorem eq_zero_of_orthogonal_coeffFamily {χ : Lp ℂ 2 μ} (hχ : OrthToCoeff μ χ) : χ = 0 := by
  -- `⟪χ, ψ⟫ = 0` for every continuous `ψ`
  have hψ : ∀ ψ : C(G, ℂ), inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) = 0 := by
    intro ψ
    have hbound : ∀ ε : ℝ, 0 < ε →
        ‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)‖ ≤
          ‖χ‖ * ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ * ε := by
      intro ε hε
      obtain ⟨φ, hφ, happ⟩ := exists_approx_identity μ ψ hε
      have hK := convOp_eq_zero_of_orth μ hχ hφ
      have hsa : (convOp μ φ).IsSymmetric := (isSelfAdjoint_convOp μ hφ).isSymmetric
      have h1 : inner ℂ χ (convOp μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)) = 0 := by
        have hsym : inner ℂ (convOp μ φ χ) (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) =
            inner ℂ χ (convOp μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)) := hsa χ _
        rw [← hsym, hK]; simp
      set Kψ : C(G, ℂ) := convToC μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) with hKψ
      have h2 : convOp μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) = ContinuousMap.toLp (E := ℂ) 2 μ ℂ Kψ := rfl
      rw [h2] at h1
      have hdiff : ‖ψ - Kψ‖ ≤ ε := by
        refine (ContinuousMap.norm_le _ hε.le).2 fun x => ?_
        rw [ContinuousMap.sub_apply, norm_sub_rev]
        exact happ x
      have : inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) =
          inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (ψ - Kψ)) := by
        rw [map_sub, inner_sub_right, h1, sub_zero]
      rw [this]
      calc ‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (ψ - Kψ))‖
          ≤ ‖χ‖ * ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ (ψ - Kψ)‖ := norm_inner_le_norm _ _
        _ ≤ ‖χ‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ * ‖ψ - Kψ‖) := by
            gcongr
            exact (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).le_opNorm _
        _ ≤ ‖χ‖ * (‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ * ε) := by
            gcongr
        _ = _ := by ring
    by_contra hne
    have hpos : 0 < ‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)‖ := norm_pos_iff.2 hne
    set C : ℝ := ‖χ‖ * ‖(ContinuousMap.toLp (E := ℂ) 2 μ ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ)‖ with hC
    have hCnn : 0 ≤ C := by positivity
    have := hbound (‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)‖ / (2 * (C + 1)))
      (by positivity)
    have h3 : C * (‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)‖ / (2 * (C + 1))) <
        ‖inner ℂ χ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ)‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- density of the continuous functions
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := μ) (by norm_num)
  have hzero : inner ℂ χ χ = 0 := by
    have hcl : IsClosed {v : Lp ℂ 2 μ | inner ℂ χ v = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : Set.range (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) ⊆ {v : Lp ℂ 2 μ | inner ℂ χ v = 0} := by
      rintro _ ⟨ψ, rfl⟩; exact hψ ψ
    have : closure (Set.range (ContinuousMap.toLp (E := ℂ) 2 μ ℂ)) ⊆ {v : Lp ℂ 2 μ | inner ℂ χ v = 0} :=
      closure_minimal hsub hcl
    exact this (hd.closure_range ▸ Set.mem_univ χ)
  exact inner_self_eq_zero.1 hzero

end

end Lightlike.HarmonicAnalysis
