import Lightlike.SpinFoam.Tests

/-!
# Gauge-fixed Ooguri state sum: the trust check on the boundary of the 5-simplex

The gauge fixing of the 4D Ooguri state sum (the gauge rule `IsGauge`, the gauge-fixed sum
`amplitudeGF`, its invariance under the five Pachner moves `amplitudeGF_move33_gauge`,
`amplitudeGF_move24_gauge`, `amplitudeGF_move42_gauge`, `Move15.amplitudeGF_move15_gauge`,
`Move15.amplitudeGF_move51_gauge`, and the independence of the gauge choice
`amplitudeGF_eq_of_isGauge_forces`) is in `Lightlike/SpinFoam/`. This file bundles the two trust
checks of the milestone on `∂Δ⁵`: a gauge set that obeys the rule gives the amplitude `1`, and a
gauge set that violates it gives a different amplitude.
-/

namespace Lightlike.SpinFoam

open Lightlike.FourD Lightlike.FourD.Tests

/-- **Trust check on `∂Δ⁵`.** For the boundary of the 5-simplex with cutoff `½` on every
triangle, the gauge set `starT` (the cone from a vertex) obeys the gauge rule and gives the
state sum `1`, while the set `gauge9` (`starT` with one triangle removed) violates the rule and
gives `5 ≠ 1`: a gauge set that breaks the hypotheses changes the amplitude. -/
theorem gaugeFixed_sphere6_trust :
    IsGauge sphere6 starT ∧ amplitudeGF sphere6 starT (fun _ => 1) = 1 ∧
      ¬ IsGauge sphere6 gauge9 ∧ amplitudeGF sphere6 gauge9 (fun _ => 1) = 5 ∧
      amplitudeGF sphere6 gauge9 (fun _ => 1) ≠ amplitudeGF sphere6 starT (fun _ => 1) := by
  refine ⟨isGauge_starT, amplitudeGF_starT _, not_isGauge_gauge9, amplitudeGF_gauge9_one, ?_⟩
  rw [amplitudeGF_gauge9_one, amplitudeGF_starT]
  norm_num

end Lightlike.SpinFoam
