import Lightlike.HarmonicAnalysis.ConvolutionOperator

/-!
# The integral formula for the convolution operator

On the class of a continuous function `ψ`, the operator `K_φ` is the integral operator
`(K_φ ψ)(x) = ∫ φ(y⁻¹ x) ψ(y) dμ(y)` (`convOp_toLp_ae`).

Supporting lemma for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- On a continuous function the operator `K_φ` is the integral operator with kernel `φ(y⁻¹ x)`. -/
theorem convToC_toLp_apply [IsFiniteMeasure μ] (φ ψ : C(G, ℂ)) (x : G) :
    convToC μ φ (ContinuousMap.toLp (E := ℂ) 2 μ ℂ ψ) x = ∫ y, φ (y⁻¹ * x) * ψ y ∂μ := by
  rw [convToC_apply, kernelVec, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (kernelMap φ x),
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) ψ] with y h1 h2
  rw [h1, h2, kernelMap_apply]
  simp [mul_comm]

end

end Lightlike.HarmonicAnalysis
