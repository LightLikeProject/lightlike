import Lightlike.GR.HawkingRadiation.Summary

/-! Tests for row G1-068: signatures of the thermality theorems, and the Schwarzschild check
`T = 1/(8πM)`. -/

open Lightlike.GR.HawkingRadiation

#check @hawking_collapse_thermal
#check @hawking_schwarzschild_thermal

example {M : ℝ} (hM : 0 < M) :
    (1 / (4 * M)) / (2 * Real.pi) = 1 / (8 * Real.pi * M) :=
  schwarzschild_surfaceGravity_temperature hM

/-- Occupation at unit `κ`, `T = 1/(2π)`: the Planck law `1/(e^{2πω} - 1)`. -/
example {ω w : ℝ} (hω : 0 < ω) (hw : 0 < w) (c : ℂ)
    (hc : ‖c‖ ^ 2 = (ω / 1) / (2 * Real.pi)) :
    ‖c * kernelMinus (ω / 1) w‖ ^ 2 = 1 / (Real.exp (ω / (1 / (2 * Real.pi))) - 1) :=
  (hawking_collapse_thermal one_pos hω hw c hc).2

#print axioms hawking_collapse_thermal
#print axioms hawking_schwarzschild_thermal
