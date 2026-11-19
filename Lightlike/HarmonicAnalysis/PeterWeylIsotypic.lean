import Lightlike.HarmonicAnalysis.PeterWeylHilbert

/-!
# The Peter–Weyl theorem: `L²(G)` is the Hilbert sum of the isotypic components

For a class `π` of irreducible continuous unitary matrix representations of a compact group `G`, the
**isotypic component** `isotypic μ π ⊆ L²(G, μ)` is the span of the matrix coefficients of the representative
of `π` (`isotypic`); it is the span of the coefficients of any representation in the class
(`isotypic_eq_span_of_mem`), and has dimension `(dim π)²` (`finrank_isotypic`), the dimension of `End(V_π)`.

`peterWeyl_isHilbertSum`: `L²(G, μ)` is the Hilbert sum of the isotypic components.

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1, Proposition 7 (`L²(G) = ⊕_ξ L²(G)_ξ`) and Proposition 8
  (`dim(V_ξ)^{1/2} ι_ξ : HS(V_ξ) → L²(G)_ξ` is unitary).
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The **isotypic component** of a class `π` of irreducible representations: the span in `L²(G, μ)` of the
(normalised) matrix coefficients of the representative of `π`. -/
def isotypic (π : IrrClass G) : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ (Set.range fun ij : (Quotient.out π : IrrRep G).ι × (Quotient.out π : IrrRep G).ι =>
    coeffFamily μ ⟨π, ij⟩)

instance (π : IrrClass G) : FiniteDimensional ℂ (isotypic μ π) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

lemma coeffFamily_mem_isotypic (a : CoeffIdx G) : coeffFamily μ a ∈ isotypic μ a.1 :=
  Submodule.subset_span ⟨a.2, rfl⟩

lemma sqrt_card_ne_zero (ρ : IrrRep G) : ((Real.sqrt (Fintype.card ρ.ι) : ℝ) : ℂ) ≠ 0 := by
  haveI := ρ.irr.1
  have h : (0 : ℝ) < Fintype.card ρ.ι := by exact_mod_cast Fintype.card_pos
  exact_mod_cast (Real.sqrt_pos.2 h).ne'

/-- The class of a coefficient of the representative lies in the isotypic component. -/
lemma toLp_coeffFun_out_mem_isotypic (π : IrrClass G)
    (i j : (Quotient.out π : IrrRep G).ι) :
    ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun (Quotient.out π) i j) ∈ isotypic μ π := by
  have h := (isotypic μ π).smul_mem ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ)⁻¹
    (coeffFamily_mem_isotypic μ ⟨π, (i, j)⟩)
  have e : ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ)⁻¹ •
      coeffFamily μ ⟨π, (i, j)⟩ =
      ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun (Quotient.out π) i j) := by
    show ((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ)⁻¹ •
      (((Real.sqrt (Fintype.card (Quotient.out π : IrrRep G).ι) : ℝ) : ℂ) • _) = _
    rw [smul_smul, inv_mul_cancel₀ (sqrt_card_ne_zero (Quotient.out π)), one_smul]
  rwa [e] at h

/-- The isotypic component does not depend on the representative: the coefficients of any irreducible
representation in the class `π` span it. -/
theorem isotypic_eq_span_of_mem (ρ : IrrRep G) :
    isotypic μ (Quotient.mk (irrSetoid G) ρ) = Submodule.span ℂ
      (Set.range fun ij : ρ.ι × ρ.ι => ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ ij.1 ij.2)) := by
  set π : IrrClass G := Quotient.mk (irrSetoid G) ρ with hπ
  have heq : UnitaryMatrixRep.Equivalent (Quotient.out π : IrrRep G).ρ ρ.ρ :=
    Quotient.exact (Quotient.out_eq π)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain ⟨c, hc⟩ := UnitaryMatrixRep.entry_eq_sum_of_equivalent heq.symm i j
    have hfun : coeffFun (Quotient.out π : IrrRep G) i j = ∑ a, ∑ b, c a b • coeffFun ρ a b := by
      ext g
      simp only [coeffFun, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      exact hc g
    show coeffFamily μ ⟨π, (i, j)⟩ ∈ _
    simp only [coeffFamily]
    rw [hfun]
    simp only [map_sum, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)
  · rintro _ ⟨⟨k, l⟩, rfl⟩
    obtain ⟨c, hc⟩ := UnitaryMatrixRep.entry_eq_sum_of_equivalent heq k l
    have hfun : coeffFun ρ k l = ∑ a, ∑ b, c a b • coeffFun (Quotient.out π : IrrRep G) a b := by
      ext g
      simp only [coeffFun, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      exact hc g
    show ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffFun ρ k l) ∈ isotypic μ π
    rw [hfun]
    simp only [map_sum, map_smul]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact Submodule.smul_mem _ _ (toLp_coeffFun_out_mem_isotypic μ π a b)

variable [IsProbabilityMeasure μ]

/-- The isotypic component of `π` has dimension `(dim π)²`, the dimension of `End(V_π)`. -/
theorem finrank_isotypic (π : IrrClass G) :
    Module.finrank ℂ (isotypic μ π) = Fintype.card (Quotient.out π : IrrRep G).ι ^ 2 := by
  have hli : LinearIndependent ℂ
      (fun ij : (Quotient.out π : IrrRep G).ι × (Quotient.out π : IrrRep G).ι => coeffFamily μ ⟨π, ij⟩) :=
    ((orthonormal_coeffFamily μ).comp _ fun a b h => by
      simpa using h).linearIndependent
  rw [isotypic, finrank_span_eq_card hli, Fintype.card_prod, sq]

/-- Different isotypic components are orthogonal. -/
theorem isOrtho_isotypic {π π' : IrrClass G} (h : π ≠ π') : isotypic μ π ⟂ isotypic μ π' := by
  rw [isotypic, isotypic, Submodule.isOrtho_span]
  rintro _ ⟨ij, rfl⟩ _ ⟨kl, rfl⟩
  exact (orthonormal_coeffFamily μ).2 fun hab => h (congrArg Sigma.fst hab)

variable [μ.Regular]

/-- **Peter–Weyl theorem (Hilbert sum form).** `L²(G, μ)` is the Hilbert sum of the isotypic components of the
classes of irreducible unitary representations of the compact group `G`. -/
theorem peterWeyl_isHilbertSum :
    IsHilbertSum ℂ (fun π : IrrClass G => isotypic μ π) fun π => (isotypic μ π).subtypeₗᵢ := by
  refine IsHilbertSum.mkInternal _ (OrthogonalFamily.of_pairwise fun π π' h => isOrtho_isotypic μ h) ?_
  obtain ⟨b, hb⟩ := peterWeyl_hilbertBasis μ
  have hle : Submodule.span ℂ (Set.range (coeffFamily μ)) ≤ ⨆ π : IrrClass G, isotypic μ π := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (le_iSup (fun π : IrrClass G => isotypic μ π) a.1) (coeffFamily_mem_isotypic μ a)
  have hdense : (Submodule.span ℂ (Set.range (coeffFamily μ))).topologicalClosure = ⊤ := by
    have h1 := b.dense_span
    have h2 : (b : CoeffIdx G → Lp ℂ 2 μ) = coeffFamily μ := funext hb
    rw [h2] at h1
    exact h1
  rw [← hdense]
  exact Submodule.topologicalClosure_mono hle

end

end Lightlike.HarmonicAnalysis
