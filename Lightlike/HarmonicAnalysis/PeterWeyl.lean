import Lightlike.HarmonicAnalysis.PeterWeylSeparation

/-!
# The Peter–Weyl theorem: density of matrix coefficients

For a compact Hausdorff group `G`, the span of the matrix coefficients of continuous finite-dimensional
unitary representations is dense in `C(G, ℂ)` in the sup norm (`peterWeyl_dense_continuous`) and, for a
Haar measure, in `L²(G, μ)` (`peterWeyl_dense_L2`).

## References

* T. Bröcker and T. tom Dieck, *Representations of compact Lie groups*, Springer (1985), Chapter III.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Peter–Weyl, sup-norm form.** The matrix coefficients of finite-dimensional unitary representations of
a compact Hausdorff group are dense in `C(G, ℂ)`. -/
theorem peterWeyl_dense_continuous : Dense (matrixCoeffSpan G : Set C(G, ℂ)) :=
  dense_matrixCoeffSpan_of_separates fun _ _ hgh => exists_matrixCoeff_ne hgh

/-- **Peter–Weyl, `L²` form.** For a Haar measure the classes of the matrix coefficients are dense in
`L²(G, μ)`. -/
theorem peterWeyl_dense_L2 (μ : Measure G) [μ.IsHaarMeasure] :
    Dense (((matrixCoeffSpan G).map (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).toLinearMap :
      Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := μ) (by norm_num)
  have := hd.dense_image (ContinuousMap.toLp (E := ℂ) 2 μ ℂ).continuous peterWeyl_dense_continuous
  simpa [Submodule.map_coe] using this

end

end Lightlike.HarmonicAnalysis
