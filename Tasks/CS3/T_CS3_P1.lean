import Lightlike.CausalSets.LongestChain

/-!
# Task T-CS3-P1

The longest chain of n uniform points of the 1+1 diamond is about 2 sqrt(n).

The statement is `Lightlike.CausalSets.expected_longestChain_asymptotic`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. The order of the sprinkled points is the dominance order of a uniform random permutation
(`coneLE_sprinklePt`), so the longest chain is the longest increasing subsequence. The limit `2` is
the theorem of Vershik–Kerov and Logan–Shepp.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/CausalSets/LongestChain.lean`: `CausalSets.longestChain`

Lemmas about them, which a proof may use:

* `CausalSets.sum_longestChain_two` (`Lightlike/CausalSets/LongestChain.lean`)
* `CausalSets.sum_longestChain_one` (`Lightlike/CausalSets/LongestChain.lean`)
* `CausalSets.sum_longestChain_four` (`Lightlike/CausalSets/LongestChain.lean`)
* `CausalSets.sum_longestChain_three` (`Lightlike/CausalSets/LongestChain.lean`)
* `CausalSets.expected_longestChain_three` (`Lightlike/CausalSets/LongestChain.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.CausalSets.expected_longestChain_asymptotic

## References

Milestone CS3 (Longest chains), ROADMAP section "Causal sets".
Source: D. Romik, The Surprising Mathematics of Longest Increasing Subsequences, Cambridge
University Press (2015), Chapter: Longest increasing subsequences in random permutations
(`romik-2015` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Filter Topology

namespace Lightlike.CausalSets

/-- **The expected longest chain grows like `2 √n`.** The average of `longestChain σ` over the
`n!` permutations of `Fin n`, divided by `√n`, tends to `2`. -/
theorem expected_longestChain_asymptotic :
    Tendsto (fun n : ℕ =>
      (∑ σ : Equiv.Perm (Fin n), (longestChain σ : ℝ)) / ((n.factorial : ℝ) * Real.sqrt n))
      atTop (𝓝 2) := by
  sorry

end Lightlike.CausalSets
