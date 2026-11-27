import Mathlib
import Lightlike.Spacetime.VolumeMeasureFinite

/-!
# Tests: chart form, local finiteness and positivity of the volume measure

On Minkowski space (`Fin n → ℝ` with its single chart, the identity) the chart formula of
`NondegMetric.lintegral_chart` is the integral against Lebesgue measure with density `√|det η| = 1`; the volume measure is
locally finite and positive on open sets, and the unit ball has positive finite volume. A wrong density (twice the true
one) is shown to give a different value for the volume of the unit cube.
-/

open MeasureTheory Set Manifold Metric
open scoped ENNReal
noncomputable section
namespace Lightlike.VolumeMeasureFiniteTests

/-- Non-vacuity: the hypotheses are met by Minkowski space and the measure is locally finite. -/
example (n : ℕ) : IsLocallyFiniteMeasure (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure :=
  NondegMetric.isLocallyFiniteMeasure_volumeMeasure _

/-- Non-vacuity: positivity on open sets for Minkowski space. -/
example (n : ℕ) : (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure.IsOpenPosMeasure :=
  NondegMetric.isOpenPosMeasure_volumeMeasure _

/-- The unit ball of Minkowski space has positive and finite volume. -/
example (n : ℕ) :
    0 < (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure (ball 0 1) ∧
      (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure (ball 0 1) < ⊤ := by
  have := NondegMetric.isLocallyFiniteMeasure_volumeMeasure (NondegMetric.ofLorentzian (minkowskiMetric n))
  have := NondegMetric.isOpenPosMeasure_volumeMeasure (NondegMetric.ofLorentzian (minkowskiMetric n))
  exact ⟨isOpen_ball.measure_pos _ ⟨0, mem_ball_self one_pos⟩,
    lt_of_le_of_lt (measure_mono ball_subset_closedBall) (isCompact_closedBall (0 : Fin n → ℝ) 1).measure_lt_top⟩

/-- Trust check: the volume of the unit cube of Minkowski space is `1`, as Lebesgue measure gives. -/
example (n : ℕ) :
    (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure (Set.pi univ fun _ => Icc (0 : ℝ) 1) = 1 := by
  rw [show (NondegMetric.ofLorentzian (minkowskiMetric n)).volumeMeasure = volumeMeasure (minkowskiMetric n) from rfl,
    volumeMeasure_minkowski (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
  rw [volume_pi_pi]; simp [Real.volume_Icc]

/-- A wrong density is caught: twice Lebesgue measure gives the unit cube volume `2 ≠ 1`. -/
example (n : ℕ) : (2 • (volume : Measure (Fin n → ℝ))) (Set.pi univ fun _ => Icc (0 : ℝ) 1) ≠ 1 := by
  rw [Measure.smul_apply, volume_pi_pi]; simp [Real.volume_Icc]

end Lightlike.VolumeMeasureFiniteTests
