import Lightlike.Spacetime.CausalLadder.StablyCausalSimple

/-!
# Task T-GE2-P11

Causal simplicity implies stable causality.

The statement is `Lightlike.Causal.isStablyCausal_of_isCausallySimple`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Construct a time function by Hawking's averaging of volumes of futures, using closedness of
`J±`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsCausallySimple`, `Causal.IsStablyCausal`

Lemmas about them, which a proof may use:

* `Causal.isStronglyCausal_of_isStablyCausal_aux` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)
* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.isOpen_coverSet` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.ReachIn.left_mem` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isStablyCausal_of_isCausallySimple

## References

Milestone GE2 (Causal structure), ROADMAP section "Lorentzian and Riemannian geometry".
Source: S. W. Hawking and G. F. R. Ellis, The Large Scale Structure of Space-Time, Cambridge
University Press (1973), Chapter: Causal structure (`hawking-ellis-1973` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : TimeOrientation g)

/-- **Causal simplicity implies stable causality.** The statement is over manifolds modelled on `ℝⁿ`
(`Fin n → ℝ`, with the model `𝓘(ℝ, Fin n → ℝ)`, hence without boundary), the setting of Hawking–Ellis'
space-time: the volume measure used by Hawking's time function exists only for such charts (representation
difference from the earlier statement over a general normed model; approved by the integrator for the
maintainers, 18 November 2026). -/
theorem isStablyCausal_of_isCausallySimple [T2Space M] [SecondCountableTopology M]
    (h : IsCausallySimple T) : IsStablyCausal T := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M := IsManifold.of_le (n := ∞) (by norm_num)
  exact isStablyCausal_of_isCausallySimple_euclid T h

end Lightlike.Causal
