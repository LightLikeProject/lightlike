import Lightlike.OperatorAlgebras.KantorovichRubinstein

/-!
# Tests for Kantorovich-Rubinstein duality

* `sSup_dirac`: for Dirac measures the Lipschitz supremum is `d(x, y)`;
* `two_lipschitz_exceeds`: with `2`-Lipschitz tests the pairing `2 d(x, y)` exceeds `W₁(δₓ, δ_y)` for `x ≠ y`, so the
  constant `1` in (KR) cannot be raised (wrong input);
* `ctrans_zero`: the `c`-transform of `0` is `0`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **(KR) for Dirac measures**: `sup {u(x) - u(y) | u 1-Lipschitz} = d(x, y)`. -/
theorem sSup_dirac (x y : X) :
    sSup {r | ∃ u : X → ℝ, LipschitzWith 1 u ∧
      r = ∫ z, u z ∂(Measure.dirac x) - ∫ z, u z ∂(Measure.dirac y)} = dist x y := by
  rw [← wasserstein1_eq_sSup, wasserstein1_dirac]

/-- **Wrong input**: the `2`-Lipschitz test `2 d(·, y)` pairs to `2 d(x, y) > W₁(δₓ, δ_y)` for `x ≠ y`. -/
theorem two_lipschitz_exceeds {x y : X} (hxy : x ≠ y) :
    LipschitzWith 2 (fun z => 2 * dist z y) ∧
      wasserstein1 (Measure.dirac x) (Measure.dirac y) <
        ∫ z, 2 * dist z y ∂(Measure.dirac x) - ∫ z, 2 * dist z y ∂(Measure.dirac y) := by
  refine ⟨?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_two]
    push_cast
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le a b y) zero_le_two
  · rw [wasserstein1_dirac, integral_dirac, integral_dirac, dist_self, mul_zero, sub_zero]
    have := dist_pos.mpr hxy
    linarith

/-- The `c`-transform of `0` is `0`: `inf_y d(x, y) = 0`. -/
theorem ctrans_zero (x : X) : ctrans (0 : C(X, ℝ)) x = 0 := by
  have : Nonempty X := ⟨x⟩
  apply le_antisymm
  · have := ctrans_le (0 : C(X, ℝ)) x x
    simpa using this
  · exact le_ciInf fun y => by simp

end Lightlike.OperatorAlgebras.Transport
