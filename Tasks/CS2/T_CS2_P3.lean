import Lightlike.CausalSets.Rectangle

/-!
# Task T-CS2-P3

A rectangle instead of the diamond gives a different relation probability.

The statement is `Lightlike.CausalSets.rectangle_relProb`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. For `s = t' - t ∈ [0, 1]` the density of the time difference is `1 - s`, and `|x' - x| ≤ s`
has probability `s - s²/4` for the width `2`; integrate `(1 - s)(s - s²/4)` over `[0, 1]` to get
`7/48`. The diamond value is `relProb_one`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/CausalSets/Sprinkling.lean`: `CausalSets.regionRelProb`, `CausalSets.relProb`

Lemmas about them, which a proof may use:

* `CausalSets.rectangle_relProb_eq` (`Lightlike/CausalSets/Rectangle.lean`)
* `CausalSets.relProb_eq` (`Lightlike/CausalSets/Sprinkling.lean`)
* `CausalSets.relProb_one` (`Lightlike/CausalSets/Myrheim.lean`)
* `CausalSets.relProb_zero` (`Lightlike/CausalSets/MyrheimGen.lean`)
* `CausalSets.relProb_beta` (`Lightlike/CausalSets/MyrheimGen.lean`)
* `CausalSets.relProb_gamma` (`Lightlike/CausalSets/MyrheimGen.lean`)
* `CausalSets.myrheimMeyer_eq` (`Lightlike/CausalSets/MyrheimGen.lean`)
* `CausalSets.relProb_three_eq` (`Lightlike/CausalSets/Myrheim4D.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.CausalSets.rectangle_relProb

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

/-- **Wrong model.** Uniform points of the rectangle `[0, 1] × [0, 2]` of `ℝ^{1+1}`, with the first coordinate the time (extent `1`) and the second the space (extent `2`), are related with probability `7/48`, not the `1/4` of the diamond (`relProb_one`). -/
theorem rectangle_relProb :
    regionRelProb {x : Fin 2 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 2} = 7 / 48 ∧
      regionRelProb {x : Fin 2 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 2} ≠ relProb 1 := by
  exact rectangle_relProb_eq

end Lightlike.CausalSets
