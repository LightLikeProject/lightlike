import Lightlike.Spacetime.Causal.MinkowskiCausal
import Lightlike.Spacetime.CausalLadder.PerturbTimelike

/-!
# Task T-GE2-P7

The chronological future is open.

The statement is `Lightlike.Causal.isOpen_chronFuture`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Perturb the end of a timelike curve inside a chart; the open future cone at the end point
supplies the room.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Spacetime/Lorentzian.lean`: `LorentzianMetric`
* `Lightlike/Spacetime/Causal/TimeOrientation.lean`: `Causal.TimeOrientation`
* `Lightlike/Spacetime/Causal/Relations.lean`: `Causal.chronFuture`

Lemmas about them, which a proof may use:

* `Causal.chron_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.chron_subset_causal` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_self` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.causal_trans` (`Lightlike/Spacetime/Causal/BasicRelations.lean`)
* `Causal.fieldAt_coord` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.isOpen_coverSet` (`Lightlike/Spacetime/Causal/SmoothOrientation.lean`)
* `Causal.exit_or_diamond` (`Lightlike/Spacetime/CausalLadder/ExitDiamond.lean`)
* `Causal.ReachIn.left_mem` (`Lightlike/Spacetime/CausalLadder/StrongCausality.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Causal.isOpen_chronFuture

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **The chronological future is open.**

Matches the source (Hawking–Ellis: space-time has no boundary); the hypothesis `BoundarylessManifold I M`
was added to the statement, approved by the maintainers, 18 November 2026. -/
theorem isOpen_chronFuture (x : M) : IsOpen (chronFuture T x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨γ, a, b, hab, hγ, rfl, rfl⟩
  obtain ⟨U, hU, hreach⟩ := exists_nhds_reach T hab hγ
  filter_upwards [hU] with z hz
  obtain ⟨G, e, hae, hG, hG1, hG2⟩ := hreach z hz
  exact ⟨G, a, e, hae, hG, hG1, hG2⟩

end Lightlike.Causal
