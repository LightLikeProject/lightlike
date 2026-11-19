import Lightlike.HarmonicAnalysis.PeterWeylHilbertSchmidt

/-!
# The regular representation on an isotypic component

Left translation `(L_s f)(g) = f(s⁻¹ g)` preserves each isotypic component of `L²(G, μ)`
(`isLeftInvariant_isotypic`), and under the isometry `T ↦ √(dim ρ) · tr(T ρ(·))` from the Hilbert–Schmidt
matrices it is right multiplication by `ρ(s⁻¹)`: `L_s (U T) = U (T ρ(s⁻¹))`
(`exists_isotypic_isometry_equivariant`). So the left regular representation on the isotypic component of `ρ`
is the direct sum of `dim ρ` copies (the rows of `T`) of one irreducible representation, which with
`peterWeyl_isHilbertSum` is the Peter–Weyl theorem in the form "the regular representation is the Hilbert sum
of the irreducible representations, each with multiplicity its dimension".

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1, Theorem 1 and Proposition 8 (the map `ι_ξ` is equivariant).
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

open UnitaryMatrixRep

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Left translation of a matrix coefficient: `ρ_{ji}(s⁻¹ g) = ∑ k, ρ(s⁻¹)_{jk} ρ(g)_{ki}`. -/
lemma trC_coeffFun (ρ : IrrRep G) (s : G) (j i : ρ.ι) :
    trC s (coeffFun ρ j i) = ∑ k, ρ.ρ.mat s⁻¹ j k • coeffFun ρ k i := by
  ext g
  simp only [trC_apply, coeffFun, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  rw [ρ.ρ.mat_mul, Matrix.mul_apply]

/-- Left translation of the functions `√(dim ρ) · ρ_{ji}`. -/
theorem leftTr_hsFamily (ρ : IrrRep G) (s : G) (ij : ρ.ι × ρ.ι) :
    leftTr μ s (hsFamily μ ρ ij) = ∑ k, ρ.ρ.mat s⁻¹ ij.2 k • hsFamily μ ρ (ij.1, k) := by
  simp only [hsFamily, map_smul]
  rw [leftTr_toLp, trC_coeffFun, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_comm]

/-- **The isotypic components are invariant under left translation.** -/
theorem isLeftInvariant_isotypic (ρ : IrrRep G) :
    IsLeftInvariant μ (isotypic μ (Quotient.mk (irrSetoid G) ρ)) := by
  intro s v hv
  rw [← span_hsFamily] at hv ⊢
  refine Submodule.span_induction
    (p := fun x _ => leftTr μ s x ∈ Submodule.span ℂ (Set.range (hsFamily μ ρ))) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨ij, rfl⟩
    rw [leftTr_hsFamily]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

/-- Left translation of `∑ T_{ij} · √(dim ρ) ρ_{ji}` replaces `T` by `T ρ(s⁻¹)`. -/
theorem leftTr_sum_hsFamily (ρ : IrrRep G) (s : G) (T : ρ.ι × ρ.ι → ℂ) :
    leftTr μ s (∑ ij, T ij • hsFamily μ ρ ij) =
      ∑ ij : ρ.ι × ρ.ι, (∑ k, T (ij.1, k) * ρ.ρ.mat s⁻¹ k ij.2) • hsFamily μ ρ ij := by
  simp only [map_sum, map_smul, leftTr_hsFamily, Fintype.sum_prod_type, Finset.smul_sum,
    Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

variable [IsProbabilityMeasure μ]

/-- **The regular representation on an isotypic component.** The isometry
`U : T ↦ √(dim ρ) · tr(T ρ(·))` from the Hilbert–Schmidt matrices onto the isotypic component of `ρ`
intertwines right multiplication by `ρ(s⁻¹)` with left translation by `s`: `L_s (U T) = U (T ρ(s⁻¹))`. -/
theorem exists_isotypic_isometry_equivariant (ρ : IrrRep G) :
    ∃ U : EuclideanSpace ℂ (ρ.ι × ρ.ι) ≃ₗᵢ[ℂ] isotypic μ (Quotient.mk (irrSetoid G) ρ),
      (∀ T : EuclideanSpace ℂ (ρ.ι × ρ.ι),
        ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) = ∑ ij, T ij • hsFamily μ ρ ij) ∧
      ∀ (s : G) (T : EuclideanSpace ℂ (ρ.ι × ρ.ι)),
        leftTr μ s ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) =
          ((U (WithLp.toLp 2 fun ij : ρ.ι × ρ.ι => ∑ k, T (ij.1, k) * ρ.ρ.mat s⁻¹ k ij.2) :
            isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) := by
  obtain ⟨U, hU⟩ := exists_isotypic_isometry μ ρ
  refine ⟨U, hU, fun s T => ?_⟩
  rw [hU, hU, leftTr_sum_hsFamily]

end

end Lightlike.HarmonicAnalysis
