import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.ChartCovariant

/-!
# The Corners layer agrees with the boundaryless layer

For the boundaryless model `𝓘(ℝ, Fin n → ℝ)` (`range 𝓘 = univ`), the declarations of the Corners layer
(`Lightlike/Spacetime/Corners/`, for any model with corners, derivatives within the range of the model) are those of
the boundaryless chart layer: the chart trivializations, the coordinate fields and the components of a vector field
agree by definition, and the coordinate metric agrees because the derivative within `univ` is the derivative
(`mfderivWithin_univ`).
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- For the boundaryless model the derivative within the range of the model is the derivative. -/
theorem mfderivWithin_range_modelWithCornersSelf {f : (Fin n → ℝ) → M} (y : Fin n → ℝ) :
    mfderivWithin 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) f (range 𝓘(ℝ, Fin n → ℝ)) y =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) f y := by
  rw [range_modelWithCornersSelf_eq_univ, mfderivWithin_univ]

/-- **The two coordinate metrics agree** for the boundaryless model. -/
theorem NondegMetric.coordMetricW_eq_coordMetric (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) :
    g.coordMetricW x₀ = g.coordMetric x₀ := by
  funext y i j
  simp only [NondegMetric.coordMetricW, NondegMetric.coordMetric, mfderivWithin_range_modelWithCornersSelf]

/-- The chart trivializations agree. -/
theorem chartTrivW_eq_chartTriv (x₀ : M) : chartTrivW (I := 𝓘(ℝ, Fin n → ℝ)) n x₀ = chartTriv n x₀ := rfl

/-- The tangent trivializations agree. -/
theorem tTrivW_eq_tTriv (x₀ : M) : tTrivW (I := 𝓘(ℝ, Fin n → ℝ)) (E := Fin n → ℝ) x₀ = tTriv (E := Fin n → ℝ) x₀ :=
  rfl

/-- The coordinate fields agree. -/
theorem coordFieldW_eq_coordField (x₀ : M) (i : Fin n) :
    coordFieldW (I := 𝓘(ℝ, Fin n → ℝ)) x₀ i = coordField x₀ i := rfl

/-- The components of a vector field in the trivialization agree. -/
theorem hatW_eq_hat (x₀ : M) (σ : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    hatW (I := 𝓘(ℝ, Fin n → ℝ)) x₀ σ = hat x₀ σ := rfl

/-- **The chart-derivative lemma of the Corners layer is that of the boundaryless layer**: both give the inverse
trivialization. -/
theorem mfderiv_extChartAt_symm_eqW_bridge (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    mfderivWithin 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
        (range 𝓘(ℝ, Fin n → ℝ)) y =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y := by
  rw [mfderiv_extChartAt_symm_eqW x₀ hy, mfderiv_extChartAt_symm_eq x₀ hy]

end Lightlike
