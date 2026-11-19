import Lightlike.Spacetime.EHManifold.MatterEinstein
import Lightlike.Spacetime.EHManifold.Tests

/-!
# Tests for the matter coupling

The hypothesis `HasMatterVariation` of `total_action_stationary_iff` can be met: the zero matter action has
the zero energy-momentum tensor (`hasMatterVariation_zero`), and then the theorem gives back the vacuum
equation (`total_action_stationary_zero_matter`).

No catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The contraction with the zero field vanishes. -/
lemma contractWith_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (p : M) :
    contractWith g SymBilinField.zero h p = 0 := by
  have hB : ((SymBilinField.zero : SymBilinField 𝓘(ℝ, Fin n → ℝ) M).h p).toBilinForm = 0 :=
    LinearMap.ext₂ fun u v => rfl
  unfold contractWith formContract
  rw [hB, map_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- **Test: the zero matter action has the zero energy-momentum tensor.** -/
theorem hasMatterVariation_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (K : Set M) :
    HasMatterVariation (fun _ => (0 : ℝ)) g SymBilinField.zero K := by
  intro h _
  simp only [contractWith_zero, integral_zero]
  exact hasDerivAt_const 0 0

/-- **Test: without matter, the stationarity of the total action is the vacuum equation.** -/
theorem total_action_stationary_zero_matter (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ κ : ℝ)
    (hκ : κ ≠ 0) :
    (∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M), IsCompact K → (∀ p, p ∉ K → h.h p = 0) →
        HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K / κ + (0 : ℝ)) 0 0) ↔
      ∀ (p : M) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p),
        (leviCivita g).einsteinField g p u v + Λ * g.g p u v = 0 := by
  have h := total_action_stationary_iff (fun _ => (0 : ℝ)) g SymBilinField.zero Λ κ hκ
    (fun K _ => hasMatterVariation_zero g K)
  rw [h]
  refine forall_congr' fun p => forall_congr' fun u => forall_congr' fun v => ?_
  have h0 : (SymBilinField.zero : SymBilinField 𝓘(ℝ, Fin n → ℝ) M).h p u v = 0 := rfl
  rw [h0, mul_zero]

end Lightlike
