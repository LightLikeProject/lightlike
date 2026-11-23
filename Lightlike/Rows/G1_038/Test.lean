module

public import Lightlike.Rows.G1_038.SachsWolfe

/-! Tests for the Sachs–Wolfe row G1-038. -/

open Lightlike.Cosmology.SachsWolfe

-- numeric check: `Φ = 3` gives `ΔT/T = 1` in matter domination, and `3` without the intrinsic term.
example : swAnisotropy (-2 * (3 : ℝ) / 3) 3 = 1 := by unfold swAnisotropy; norm_num

example : swAnisotropy 0 (3 : ℝ) ≠ swAnisotropy (-2 * 3 / 3) 3 :=
  (sachsWolfe_ne_without_intrinsic (by norm_num : (3 : ℝ) ≠ 0)).symm

#print axioms sachsWolfe
#print axioms sachsWolfe_flrw
#print axioms sachsWolfe_ne_without_intrinsic
