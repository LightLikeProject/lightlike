import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P2

q-Biedenharn–Elliott identity at r = 4.

The statement is `Lightlike.TV.qBiedenharnElliott_four`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. As `qBiedenharnElliott_three` with colours `Fin 3`, exact arithmetic in ℚ(√2).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qBiedenharnElliott`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.turaevViro_move23` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qBiedenharnElliott_three` (`Lightlike/TuraevViro/LevelOne.lean`)

Everything they depend on in one block:

    scripts/context-pack Lightlike.TV.qBiedenharnElliott_four

## References

Milestone QU1 (q-deformed Biedenharn–Elliott identity and orthogonality for `r ≥ 4`), ROADMAP
section "Quantum groups and state-sum TQFTs".
Source: V. G. Turaev, Quantum Invariants of Knots and 3-Manifolds, de Gruyter Studies in Mathematics
18 (1994), Chapter VI. 6j-symbols (`turaev-1994` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- **q-Biedenharn–Elliott at `r = 4`.** -/
theorem qBiedenharnElliott_four : qBiedenharnElliott (r := 4) (by norm_num) := by
  sorry

end Lightlike.TV
