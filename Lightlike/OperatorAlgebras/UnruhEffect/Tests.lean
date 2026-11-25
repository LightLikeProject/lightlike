import Lightlike.OperatorAlgebras.UnruhEffect.Summary

/-! Tests for row G1-049. -/

namespace Lightlike.Rows.G1_049

open Real

example : 0 < planck 1 1 := planck_pos one_pos one_pos

example : unruhAlpha 1 2 ^ 2 - unruhBeta 1 2 ^ 2 = 1 :=
  unruhAlpha_sq_sub_unruhBeta_sq one_pos two_pos

example : unruhTemp (2 * π) = 1 := by
  unfold unruhTemp
  field_simp

example (z : ℂ) : (OperatorAlgebras.Bogoliubov.id ℂ).betaPart z = 0 := (unruh_planck one_pos one_pos).2 z

#check @unruh_planck

end Lightlike.Rows.G1_049
