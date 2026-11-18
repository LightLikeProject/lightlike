import Lightlike.Spacetime.Causal.Extension
import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# Task T-GE2-P13

A Cauchy surface is achronal.

The statement is `Lightlike.Causal.IsCauchySurface.isAchronal`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Extend a timelike curve by Zorn's lemma to an inextendible one; it meets `S` at both points,
contradicting uniqueness.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsCauchySurface`, `Causal.IsAchronal`

Lemmas about them, which a proof may use:

* `Causal.isCauchySurface_of_domainDep_eq_univ` (`Lightlike/Spacetime/Causal/CauchyDomain.lean`)
* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.isOpen_coverSet` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.ReachIn.left_mem` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.IsCauchySurface.isAchronal

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A Cauchy surface is achronal.** The hypotheses `[BoundarylessManifold I M]` and
`[SecondCountableTopology M]` match the source (Hawking–Ellis: a connected paracompact Hausdorff
manifold without boundary is second countable); approved by the maintainers, 18 November 2026.
With boundary allowed the statement is false: in a half-space of Minkowski space there is no
inextendible timelike curve, so every set is a Cauchy surface. -/
theorem IsCauchySurface.isAchronal [T2Space M] [BoundarylessManifold I M]
    [SecondCountableTopology M] {S : Set M} (h : IsCauchySurface T S) :
    IsAchronal T S := by
  exact h.isAchronal_of_boundaryless

end Lightlike.Causal
