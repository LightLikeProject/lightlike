import Lightlike.HarmonicAnalysis.PeterWeylTests
import Lightlike.HarmonicAnalysis.PeterWeylReal
import Lightlike.HarmonicAnalysis.PeterWeyl

/-!
# Acceptance test for milestone HA5 (the Peter–Weyl theorem)

One place where the done-when of HA5 and its three trust checks are instantiated, each for a named
group, so that a change in the hypotheses of a Peter–Weyl statement breaks this file:

* density of the matrix coefficients in `C(G)` and `L²(G)` for `U(1)` and `SU(2)`
  (`peterWeyl_dense_continuous`, `peterWeyl_dense_L2`);
* `L²(G)` as the Hilbert sum of the isotypic components, for `SU(2)` (`peterWeyl_isHilbertSum_haar`);
* the characters `e^{inθ}` of `U(1)` as an orthonormal basis (`circle_hilbertBasis`);
* Schur orthogonality of the characters of `SU(2)` (`su2_character_orthogonality`);
* no square-integrable matrix coefficients for `ℝ` (`real_not_forall_memLp_two`).

Tests; no catalogue entry.
-/

open MeasureTheory TopologicalSpace

namespace Lightlike.HarmonicAnalysis

example : Dense (matrixCoeffSpan Circle : Set C(Circle, ℂ)) := peterWeyl_dense_continuous

example : Dense (matrixCoeffSpan SU2 : Set C(SU2, ℂ)) := peterWeyl_dense_continuous

example (μ : Measure SU2) [μ.IsHaarMeasure] :
    Dense (((matrixCoeffSpan SU2).map (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).toLinearMap :
      Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  peterWeyl_dense_L2 μ

example :
    IsHilbertSum ℂ
      (fun π : IrrClass SU2 => isotypic (Measure.haarMeasure (⊤ : PositiveCompacts SU2)) π)
      fun π => (isotypic (Measure.haarMeasure (⊤ : PositiveCompacts SU2)) π).subtypeₗᵢ :=
  peterWeyl_isHilbertSum_haar SU2

example (μ : Measure Circle) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ b : HilbertBasis ℤ ℂ (Lp ℂ 2 μ), ∀ n, b n = circleMonoLp μ n :=
  circle_hilbertBasis μ

example (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∫ g, (su2Spin 1).character g * starRingEnd ℂ ((su2Spin 1).character g) ∂μ = 1 := by
  simpa using su2_character_orthogonality μ 1 1

example (ρ : UnitaryMatrixRep (Multiplicative ℝ) (Fin 1)) :
    ¬ ∀ j, MemLp (fun x : ℝ => ρ.mat (Multiplicative.ofAdd x) 0 j) 2 (volume : Measure ℝ) :=
  real_not_forall_memLp_two ρ 0

end Lightlike.HarmonicAnalysis
