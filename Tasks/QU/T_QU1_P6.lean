import Lightlike.TuraevViro.TuraevViro

/-!
# Task T-QU1-P6

q-Biedenharn–Elliott identity for every r ≥ 2.

The statement is `Lightlike.TV.qBiedenharnElliott_all`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. The q-Racah formula and q-hypergeometric identities (Kirillov–Reshetikhin 1989).
2. Representation theory of U_q(sl₂) at roots of unity (Turaev 1994).
3. Kauffman–Lins recoupling theory (1994).

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/TuraevViro/TuraevViro.lean`: `TV.qBiedenharnElliott`

Lemmas about them, which a proof may use:

* `TV.turaevViro_move14` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.turaevViro_move23` (`Lightlike/TuraevViro/TuraevViro.lean`)
* `TV.qBiedenharnElliott_three` (`Lightlike/TuraevViro/LevelOne.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.TV.qBiedenharnElliott_all

## References

Milestone QU1 (q-deformed Biedenharn–Elliott identity and orthogonality for `r ≥ 4`), ROADMAP
section "Quantum groups and state-sum TQFTs".
Source: V. G. Turaev, Quantum Invariants of Knots and 3-Manifolds, de Gruyter Studies in Mathematics
18 (1994), Chapter VI. 6j-symbols; R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (3.2.1); R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (3.2.2); R. Koekoek and R. F. Swarttouw, The Askey-scheme of
hypergeometric orthogonal polynomials and its q-analogue, Delft University of Technology report
98-17 (arXiv:math/9602214), eq. (0.5.11) (`turaev-1994`, `koekoek-swarttouw-1996`,
`koekoek-swarttouw-1996`, `koekoek-swarttouw-1996` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- **q-Biedenharn–Elliott** for every `r ≥ 2`. -/
theorem qBiedenharnElliott_all {r : ℕ} (hr : 2 ≤ r) : qBiedenharnElliott hr := by
  sorry

end Lightlike.TV
