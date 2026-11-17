import Lightlike.CausalSets.Myrheim4D

/-!
# Task T-CS2-P2

The Myrheim–Meyer relation probability in four dimensions is 1/20.

The statement is `Lightlike.CausalSets.relProb_three`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Either specialise `myrheimMeyer` (`Γ(5) Γ(2) / (4 Γ(6)) = 1/20`) or compute the volume of the
intersection of the future cone of a point with the diamond directly.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/CausalSets/Sprinkling.lean`: `CausalSets.relProb`

Lemmas about them, which a proof may use:

* `CausalSets.relProb_eq` (`Lightlike/CausalSets/Sprinkling.lean`)
* `CausalSets.relProb_one` (`Lightlike/CausalSets/Myrheim.lean`)
* `CausalSets.expected_relations_diamond` (`Lightlike/CausalSets/Sprinkling.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.CausalSets.relProb_three

## References

Milestone CS2 (Poisson sprinkling into Minkowski regions; the Myrheim–Meyer relation count), ROADMAP
section "Causal sets".
Source: S. Surya, The causal set approach to quantum gravity, Living Rev. Relativ. 22 (2019) 5, §4.1
(`surya-2019` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Lightlike

namespace Lightlike.CausalSets

/-- **Four dimensions.** Two uniform points of the causal diamond of `ℝ^{3+1}` satisfy `x ≺ y` with probability `1/20`, so `n` points have `n (n - 1) / 20` relations in expectation. -/
theorem relProb_three : relProb 3 = 1 / 20 := by
  exact relProb_three_eq

end Lightlike.CausalSets
