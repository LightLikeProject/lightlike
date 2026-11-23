module

public import Lightlike.Rows.G1_033.BoseIntegral

/-! Test file for row G1-033: the statements as they are used downstream. -/

open MeasureTheory Set Real

example : ∫ x in Ioi (0 : ℝ), x ^ 3 / (rexp x - 1) = π ^ 4 / 15 :=
  Lightlike.Rows.G1_033.integral_cube_div_exp_sub_one
