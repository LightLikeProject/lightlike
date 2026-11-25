import Lightlike.OperatorAlgebras.UnruhEffect.Planck

/-!
# The Unruh effect in coordinates: summary

Row G1-049 (milestone SC1).  Source: `crispino-higuchi-matsas-2008`, Section II (Unruh 1976).
-/

namespace Lightlike.Rows.G1_049

open Real
open scoped Complex
open Lightlike.OperatorAlgebras

/-- **Unruh effect in coordinates (Planck spectrum).**  For a Rindler mode of frequency `ω > 0` and
acceleration `a > 0`, the Minkowski-Rindler Bogoliubov coefficients `α, β` satisfy `α² - β² = 1` and
`β = e^{-πω/a} α` (the weight of the continued mode `unruhMode_rindler_left`); the particle number
`β²` is the Planck factor `1/(e^{2πω/a} - 1) = 1/(e^{ω/T} - 1)` at `T = a/2π`; the squeezing built from
`α, β` has `‖β z‖² = β² ‖z‖²`.  An inertial observer (identity transformation) sees no particles:
its antilinear part vanishes.  See Crispino-Higuchi-Matsas 2008, Section II. -/
theorem unruh_planck {ω a : ℝ} (hω : 0 < ω) (ha : 0 < a) :
    (∃ α β : ℝ, α ^ 2 - β ^ 2 = 1 ∧ β = Real.exp (-(π * ω / a)) * α ∧
        β ^ 2 = 1 / (Real.exp (ω / unruhTemp a) - 1) ∧
        ∃ B : Bogoliubov ℂ, ∀ z : ℂ, ‖B.betaPart z‖ ^ 2 = β ^ 2 * ‖z‖ ^ 2) ∧
    (∀ z : ℂ, (Bogoliubov.id ℂ).betaPart z = 0) := by
  refine ⟨⟨unruhAlpha ω a, unruhBeta ω a, unruhAlpha_sq_sub_unruhBeta_sq hω ha,
    unruhBeta_eq_exp_mul_unruhAlpha hω ha, ?_, unruhSqueeze ω a hω ha, ?_⟩, fun z => betaPart_id z⟩
  · rw [← planck_eq_bose ha, unruhBeta_sq hω ha]
    rfl
  · intro z
    rw [unruhSqueeze_norm_betaPart_sq hω ha z, unruhBeta_sq hω ha]

end Lightlike.Rows.G1_049
