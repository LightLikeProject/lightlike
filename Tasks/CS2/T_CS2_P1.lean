import Lightlike.CausalSets.MyrheimGen

/-!
# Task T-CS2-P1

The Myrheim–Meyer relation probability in every dimension.

The statement is `Lightlike.CausalSets.myrheimMeyer`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Light-cone-type coordinates are not available beyond `d = 1`. Reduce, by the symmetry of the
diamond, to the volume of the set of `y` in the diamond that are in the causal future of a point
`x`, and integrate over `x`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/CausalSets/Sprinkling.lean`: `CausalSets.relProb`

Lemmas about them, which a proof may use:

* `CausalSets.relProb_eq` (`Lightlike/CausalSets/Sprinkling.lean`)
* `CausalSets.relProb_one` (`Lightlike/CausalSets/Myrheim.lean`)
* `CausalSets.expected_relations_diamond` (`Lightlike/CausalSets/Sprinkling.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.CausalSets.myrheimMeyer

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

/-- **Myrheim–Meyer (dimension `D = d + 1`).** The probability that two independent uniform points `x`, `y` of the causal diamond satisfy `x ≺ y` is `Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))`, so `n` points have `n (n - 1)` times this many relations in expectation (`expected_relations_diamond`). The comparison of the formula with the sources is pending. -/
theorem myrheimMeyer (d : ℕ) :
    relProb d = Real.Gamma ((d : ℝ) + 2) * Real.Gamma (((d : ℝ) + 1) / 2) /
      (4 * Real.Gamma (3 * ((d : ℝ) + 1) / 2)) := by
  exact myrheimMeyer_eq d

end Lightlike.CausalSets
