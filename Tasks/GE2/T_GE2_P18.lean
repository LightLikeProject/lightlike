import Lightlike.Spacetime.Causal.DomainOfDependence

/-!
# Task T-GE2-P18

An achronal set is a Cauchy surface iff its domain of dependence is the whole manifold.

The statement is `Lightlike.Causal.isCauchySurface_iff_domainDep_eq_univ`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Both directions go through extension of a timelike curve to an inextendible one; achronality
gives the uniqueness of the meeting point.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Ladder.lean`: `Causal.IsAchronal`, `Causal.IsCauchySurface`
* `Lightlike/Spacetime/Causal/DomainOfDependence.lean`: `Causal.domainDep`

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

    scripts/context-pack Lightlike.Causal.isCauchySurface_iff_domainDep_eq_univ

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

/-- **An achronal set is a Cauchy surface iff its domain of dependence is the whole manifold.** -/
theorem isCauchySurface_iff_domainDep_eq_univ {S : Set M} (h : IsAchronal T S) :
    IsCauchySurface T S ↔ domainDep T S = Set.univ := by
  sorry

end Lightlike.Causal
