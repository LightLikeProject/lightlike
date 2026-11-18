import Lightlike.Spacetime.CausalLadder.StrongCausality
import Lightlike.Spacetime.Causal.MinkowskiGH

/-!
# Non-vacuity for stable causality implies strong causality

Minkowski space is stably causal: the time coordinate is a time function (its increase along causal
curves follows from the description of the causal future as the closed light cone). Hence the
theorem `isStronglyCausal_of_isStablyCausal_aux` applies to a concrete space, and the conclusion is
the strong causality of Minkowski space.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

open Lightlike.CausalSets

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 200000 in
/-- **Minkowski space is stably causal**: the time coordinate is a time function. -/
theorem minkowski_isStablyCausal : IsStablyCausal (minkowskiOrientation d) := by
  refine ⟨fun y => y 0, continuous_apply 0, fun x y hy hne => ?_⟩
  rw [minkowski_causalFuture_eq] at hy
  obtain ⟨h0, hform⟩ := hy
  have hco : coneLE x y := ⟨h0, hform⟩
  have hn := norm_le_of_coneLE hco
  rcases h0.eq_or_lt with h | h
  · exfalso
    apply hne
    have : ‖y - x‖ ≤ 0 := by rw [← h] at hn; exact hn
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  · simpa using h

set_option synthInstance.maxHeartbeats 200000 in
/-- Minkowski space is strongly causal, by `isStronglyCausal_of_isStablyCausal_aux`. -/
theorem minkowski_isStronglyCausal_of_stablyCausal : IsStronglyCausal (minkowskiOrientation d) :=
  isStronglyCausal_of_isStablyCausal_aux _ minkowski_isStablyCausal

end Lightlike.Causal
