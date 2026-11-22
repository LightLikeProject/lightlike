import Lightlike.Rows.G1_028.SlowRoll
import Lightlike.Rows.G1_028.SlowRollDynamics

/-! Sanity checks for row G1-028 (CO9 slow roll): `ε = 1` at `φ = √2`, `N = φi²/4 − 1/2`,
`r = 16ε`, for `V = m²φ²/2`. -/

open Lightlike.Cosmology.SlowRoll

example : epsilonV (quadPot 1) (Real.sqrt 2) = 1 := epsilonV_quadPot_sqrt_two one_ne_zero

example (φi : ℝ) : eFolds (quadPot 1) φi (Real.sqrt 2) = φi ^ 2 / 4 - 1 / 2 :=
  eFolds_quadPot_end one_ne_zero φi

example : tensorToScalar (epsilonV (quadPot 1) (Real.sqrt 2)) = 16 := by
  rw [epsilonV_quadPot_sqrt_two one_ne_zero]
  unfold tensorToScalar
  norm_num

example {φ : ℝ} (hφ : φ ≠ 0) :
    tensorToScalar (epsilonV (quadPot 1) φ) = 8 / (φ ^ 2 / 4) :=
  tensorToScalar_quadPot one_ne_zero hφ
