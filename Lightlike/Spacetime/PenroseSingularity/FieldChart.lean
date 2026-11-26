import Lightlike.Spacetime.PenroseSingularity.FutureChart
import Lightlike.Spacetime.PenroseSingularity.ChartLorentz

/-!
# Smooth fields in a chart (G1-012, step D4)

The chart expression `fieldChart p₀ Y` of a smooth vector field `Y` (components in the trivialization at `p₀`, as a
function of chart coordinates) is smooth on the chart target.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The chart expression of a vector field. -/
def fieldChart (p₀ : M) (Y : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (y : Fin n → ℝ) : Fin n → ℝ :=
  comp p₀ (Y ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y))

/-- **A smooth field has a smooth chart expression on the chart target.** -/
theorem contDiffOn_fieldChart (p₀ : M) {Y : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hY : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x => TotalSpace.mk' (Fin n → ℝ) (E := fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x) x (Y x))) :
    ContDiffOn ℝ ∞ (fieldChart p₀ Y) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target := by
  have h1 : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun x => (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ ⟨x, Y x⟩).2) (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet :=
    (Bundle.Trivialization.contMDiffOn_section_baseSet_iff (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀)).1
      hY.contMDiffOn
  have h2 := contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) p₀
  have hmaps : MapsTo (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := fun y hy => by
    have := (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_target hy
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using this
  have h3 := h1.comp h2 hmaps
  exact contMDiffOn_iff_contDiffOn.1 h3

end Lightlike.Penrose
