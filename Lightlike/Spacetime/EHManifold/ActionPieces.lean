import Lightlike.Spacetime.EHManifold.ChartIntegrable
import Lightlike.Spacetime.EHManifold.TensorVariation

/-!
# The Einstein–Hilbert action of a finite disjoint union of pieces

* `continuousOn_ehLagrangian`: `R - 2Λ` (scalar curvature of the Levi-Civita connection) is continuous on
  every chart domain.
* `ehAction_biUnion`: the action of a finite union of pairwise disjoint measurable sets, each inside a compact
  subset of one chart domain, is the sum of the actions.

Supporting lemmas for perturbations that are not supported in one chart; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The Lagrangian `R - 2Λ` of a metric is continuous on every chart domain. -/
theorem continuousOn_ehLagrangian (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (x₀ : M) :
    ContinuousOn (fun p => (leviCivita g).scalarCurvatureAt g p - 2 * Λ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have h1 : ContinuousOn (fun p => scalarCurvature (g.coordMetric x₀)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) - 2 * Λ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (((g.isCoordMetric_coordMetric x₀).contDiffOn_scalarCurvature.continuousOn).comp
      (continuousOn_extChartAt x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).mapsTo).sub continuousOn_const
  refine h1.congr fun p hp => ?_
  have h2 := scalarCurvatureAt_coord (leviCivita g) x₀ g hLC
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp] at h2
  show (leviCivita g).scalarCurvatureAt g p - 2 * Λ = _
  rw [h2]

/-- **The action of a finite disjoint union of pieces** is the sum of the actions of the pieces. -/
theorem ehAction_biUnion (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) {ι : Type*} (s : Finset ι)
    (A T : ι → Set M) (x : ι → M) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : Set.Pairwise (↑s) (Function.onFun Disjoint A)) (hT : ∀ i ∈ s, IsCompact (T i))
    (hT0 : ∀ i ∈ s, T i ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x i)).source) (hAT : ∀ i ∈ s, A i ⊆ T i) :
    ehAction g Λ (⋃ i ∈ s, A i) = ∑ i ∈ s, ehAction g Λ (A i) := by
  unfold ehAction
  exact integral_biUnion_finset s hA hd fun i hi =>
    NondegMetric.integrableOn_of_continuousOn g (x i) (hT i hi) (hT0 i hi)
      ((continuousOn_ehLagrangian g Λ (x i)).mono (hT0 i hi)) (hAT i hi)

end Lightlike
