import Lightlike.HarmonicAnalysis.PeterWeylIsotypic

/-!
# The isotypic component is isometric to the Hilbert–Schmidt operators

For an irreducible continuous unitary matrix representation `ρ` of a compact group `G` on `ℂ^ι`, with Haar
probability measure `μ`, the map
`T ↦ (g ↦ √(dim ρ) · tr(T ρ(g))) = √(dim ρ) · ∑ i j, T i j · ρ(g) j i`
is a linear isometric isomorphism from the matrices `T` with the Hilbert–Schmidt (Frobenius) inner product,
modelled as `EuclideanSpace ℂ (ι × ι)`, onto the isotypic component of the class of `ρ`
(`exists_isotypic_isometry`).

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1, Proposition 8: `dim(V_ξ)^{1/2} ι_ξ : HS(V_ξ) → L²(G)_ξ` is unitary, where
  `ι_ξ(T)(g) = ⟨T, ρ_ξ(g)*⟩_HS = tr(T ρ_ξ(g))`.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

open UnitaryMatrixRep

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The image of the matrix unit `E_{ij}` under `T ↦ √(dim ρ) · tr(T ρ(·))`: the function
`√(dim ρ) · ρ_{ji}` in `L²(G, μ)`. -/
def hsFamily (ρ : IrrRep G) (ij : ρ.ι × ρ.ι) : Lp ℂ 2 μ :=
  ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ) • ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ ij.2 ij.1)

/-- The functions `√(dim ρ) · ρ_{ji}` span the isotypic component of the class of `ρ`. -/
theorem span_hsFamily (ρ : IrrRep G) :
    Submodule.span ℂ (Set.range (hsFamily μ ρ)) = isotypic μ (Quotient.mk (irrSetoid G) ρ) := by
  rw [isotypic_eq_span_of_mem]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, i), rfl⟩)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℂ (Set.range (hsFamily μ ρ)))
      ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ)⁻¹ (Submodule.subset_span ⟨(j, i), rfl⟩)
    have e : ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ)⁻¹ • hsFamily μ ρ (j, i) =
        ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ i j) := by
      show ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ)⁻¹ • (((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ) • _) = _
      rw [smul_smul, inv_mul_cancel₀ (sqrt_card_ne_zero ρ), one_smul]
    rwa [e] at h

variable [IsProbabilityMeasure μ]

/-- The functions `√(dim ρ) · ρ_{ji}` are orthonormal (Schur orthogonality). -/
theorem orthonormal_hsFamily (ρ : IrrRep G) : Orthonormal ℂ (hsFamily μ ρ) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, j⟩ ⟨l, k⟩
  simp only [hsFamily]
  rw [inner_smul_left, inner_smul_right, inner_toLp_toLp]
  have hs : ∫ x, coeffFun ρ k l x * starRingEnd ℂ (coeffFun ρ j i x) ∂μ =
      if k = j ∧ l = i then 1 / (Fintype.card ρ.ι : ℂ) else 0 :=
    schur_orthogonality_eq μ ρ.irr k l i j
  rw [hs]
  have hn : (Fintype.card ρ.ι : ℂ) ≠ 0 := by
    have := ρ.irr.1
    exact_mod_cast Fintype.card_ne_zero
  have hsq : ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ) * ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ) =
      (Fintype.card ρ.ι : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  by_cases h : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    simp only [Complex.conj_ofReal]
    rw [← mul_assoc, hsq, mul_one_div, div_self hn]
  · rw [if_neg fun h' => h ⟨h'.2.symm, h'.1.symm⟩, if_neg fun h' => h (Prod.mk.inj h')]
    simp

/-- **The isotypic component is the space of Hilbert–Schmidt operators.** For an irreducible unitary matrix
representation `ρ` there is a linear isometric isomorphism from `EuclideanSpace ℂ (ι × ι)` (the matrices with
the Hilbert–Schmidt inner product) onto the isotypic component of `ρ` that sends `T` to the class of
`g ↦ √(dim ρ) · ∑ i j, T (i, j) · ρ(g) j i = √(dim ρ) · tr(T ρ(g))`. -/
theorem exists_isotypic_isometry (ρ : IrrRep G) :
    ∃ U : EuclideanSpace ℂ (ρ.ι × ρ.ι) ≃ₗᵢ[ℂ] isotypic μ (Quotient.mk (irrSetoid G) ρ),
      ∀ T : EuclideanSpace ℂ (ρ.ι × ρ.ι),
        ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) = ∑ ij, T ij • hsFamily μ ρ ij := by
  classical
  have hmem : ∀ ij, hsFamily μ ρ ij ∈ isotypic μ (Quotient.mk (irrSetoid G) ρ) := fun ij => by
    rw [← span_hsFamily]
    exact Submodule.subset_span ⟨ij, rfl⟩
  let w : ρ.ι × ρ.ι → isotypic μ (Quotient.mk (irrSetoid G) ρ) := fun ij => ⟨hsFamily μ ρ ij, hmem ij⟩
  have hw : Orthonormal ℂ w := by
    have h := orthonormal_hsFamily μ ρ
    rw [orthonormal_iff_ite] at h ⊢
    intro a b
    exact h a b
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range w) := by
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ Submodule.span ℂ (Set.range (hsFamily μ ρ)) := by
      rw [span_hsFamily]
      exact hx
    have hmap : Submodule.map (isotypic μ (Quotient.mk (irrSetoid G) ρ)).subtype
        (Submodule.span ℂ (Set.range w)) = Submodule.span ℂ (Set.range (hsFamily μ ρ)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [← hmap] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hyeq : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [hyeq] at hy
  let b : OrthonormalBasis (ρ.ι × ρ.ι) ℂ (isotypic μ (Quotient.mk (irrSetoid G) ρ)) :=
    OrthonormalBasis.mk hw hspan
  refine ⟨b.repr.symm, fun T => ?_⟩
  rw [← b.sum_repr_symm T, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Submodule.coe_smul, show b ij = w ij from by simp [b]]

end

end Lightlike.HarmonicAnalysis
