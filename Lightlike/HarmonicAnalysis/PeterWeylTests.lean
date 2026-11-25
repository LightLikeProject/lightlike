import Lightlike.HarmonicAnalysis.PeterWeylHilbertSchmidt
import Lightlike.HarmonicAnalysis.PeterWeylCircle
import Lightlike.HarmonicAnalysis.PeterWeylSU2

/-!
# Peter–Weyl: non-vacuity and a wrong-model test

* `peterWeyl_hilbertBasis_haar`, `peterWeyl_isHilbertSum_haar`: for every compact Hausdorff group the
  normalised Haar measure `Measure.haarMeasure ⊤` satisfies all hypotheses of the Peter–Weyl theorem (it is a
  Haar probability measure), so the theorems hold with no hypothesis on a measure. The `example`s
  instantiate them for `U(1)` and `SU(2)`.
* `trivialRep_two_not_isIrreducible`, `integral_trivialRep_two`: the trivial two-dimensional representation
  is not irreducible, and for it `∫ ρ₀₀ conj ρ₀₀ = 1 ≠ 1/2`: Schur orthogonality needs irreducibility.

Tests, and the catalogue entry of `peterWeyl_isHilbertSum_haar`.
-/

open MeasureTheory TopologicalSpace

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

section Haar

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure normalised on the whole compact group is a probability measure. -/
lemma isProbabilityMeasure_haarMeasure_top :
    IsProbabilityMeasure (Measure.haarMeasure (⊤ : PositiveCompacts G)) :=
  ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts G))⟩

/-- **Peter–Weyl for the normalised Haar measure**, with no hypothesis on a measure. -/
theorem peterWeyl_hilbertBasis_haar :
    ∃ b : HilbertBasis (CoeffIdx G) ℂ (Lp ℂ 2 (Measure.haarMeasure (⊤ : PositiveCompacts G))),
      ∀ a, b a = coeffFamily (Measure.haarMeasure (⊤ : PositiveCompacts G)) a := by
  have := isProbabilityMeasure_haarMeasure_top G
  exact peterWeyl_hilbertBasis _

/-- **Peter–Weyl, Hilbert sum form, for the normalised Haar measure.** -/
theorem peterWeyl_isHilbertSum_haar :
    IsHilbertSum ℂ (fun π : IrrClass G => isotypic (Measure.haarMeasure (⊤ : PositiveCompacts G)) π)
      fun π => (isotypic (Measure.haarMeasure (⊤ : PositiveCompacts G)) π).subtypeₗᵢ := by
  have := isProbabilityMeasure_haarMeasure_top G
  exact peterWeyl_isHilbertSum _

end Haar

example : ∃ b : HilbertBasis (CoeffIdx Circle) ℂ (Lp ℂ 2 (Measure.haarMeasure (⊤ : PositiveCompacts Circle))),
    ∀ a, b a = coeffFamily (Measure.haarMeasure (⊤ : PositiveCompacts Circle)) a :=
  peterWeyl_hilbertBasis_haar Circle

example : ∃ b : HilbertBasis (CoeffIdx SU2) ℂ (Lp ℂ 2 (Measure.haarMeasure (⊤ : PositiveCompacts SU2))),
    ∀ a, b a = coeffFamily (Measure.haarMeasure (⊤ : PositiveCompacts SU2)) a :=
  peterWeyl_hilbertBasis_haar SU2

/-- The trivial representation `g ↦ 1` on `ℂ^ι`. -/
def trivialRep (G : Type*) [Group G] [TopologicalSpace G] (ι : Type) [Fintype ι] [DecidableEq ι] :
    UnitaryMatrixRep G ι := ⟨1, continuous_const⟩

lemma trivialRep_mat (G : Type*) [Group G] [TopologicalSpace G] (ι : Type) [Fintype ι] [DecidableEq ι]
    (g : G) : (trivialRep G ι).mat g = 1 := rfl

/-- **Wrong-model test.** For the trivial two-dimensional representation of the circle,
`∫ ρ₀₀ conj ρ₀₀ dμ = 1`, not the value `1/2` of Schur orthogonality. -/
theorem integral_trivialRep_two (μ : Measure Circle) [IsProbabilityMeasure μ] :
    ∫ z, (trivialRep Circle (Fin 2)).mat z 0 0 * starRingEnd ℂ ((trivialRep Circle (Fin 2)).mat z 0 0) ∂μ
      = 1 := by
  simp [trivialRep_mat]

/-- **Wrong-model test.** The trivial two-dimensional representation is not irreducible: Schur orthogonality
would give `1 = 1/2`. -/
theorem trivialRep_two_not_isIrreducible : ¬ (trivialRep Circle (Fin 2)).IsIrreducible := by
  intro h
  have hp := isProbabilityMeasure_haarMeasure_top Circle
  have h1 := schur_orthogonality_eq (Measure.haarMeasure (⊤ : PositiveCompacts Circle)) h 0 0 0 0
  rw [integral_trivialRep_two] at h1
  norm_num at h1

end

end Lightlike.HarmonicAnalysis
