import Lightlike.OperatorAlgebras.PureStates

/-!
# Tests for the pure states of `C(X)`

* `isPure_evalAt_true`: the evaluation at a point of `Bool` is pure;
* `not_isPure_half`: the average `½(δ_true + δ_false)` is a state and is not pure (a mixed state, the wrong input):
  for the indicator `f` of `true`, `ω(f²) = ½ ≠ ¼ = ω(f)²`.
-/

open scoped ComplexOrder

namespace Lightlike.OperatorAlgebras.PureStates

/-- The evaluation at `true` is a pure state of `C(Bool)`. -/
theorem isPure_evalAt_true : IsPure Bool (evalAt true) := isPure_evalAt true

/-- The indicator function of `true`. -/
def indTrue : C(Bool, ℂ) := ⟨fun b => if b then 1 else 0, continuous_of_discreteTopology⟩

/-- **`½(δ_true + δ_false)` is a state.** -/
lemma half_mem_states : ((1 / 2 : ℂ) • (evalAt true + evalAt false) : C(Bool, ℂ) →ₗ[ℂ] ℂ) ∈ states Bool := by
  refine ⟨fun f hf => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.add_apply, evalAt_apply, smul_eq_mul]
    exact mul_nonneg (by rw [Complex.nonneg_iff]; norm_num) (add_nonneg (hf true) (hf false))
  · simp only [LinearMap.smul_apply, LinearMap.add_apply, evalAt_apply, ContinuousMap.one_apply, smul_eq_mul]
    norm_num

/-- **`½(δ_true + δ_false)` is not pure**: it is not multiplicative. -/
theorem not_isPure_half : ¬ IsPure Bool ((1 / 2 : ℂ) • (evalAt true + evalAt false)) := by
  intro h
  have := ((isPure_iff_mul _).mp h).2 indTrue indTrue
  simp only [LinearMap.smul_apply, LinearMap.add_apply, evalAt_apply, ContinuousMap.mul_apply, indTrue,
    ContinuousMap.coe_mk, smul_eq_mul] at this
  norm_num at this

end Lightlike.OperatorAlgebras.PureStates
