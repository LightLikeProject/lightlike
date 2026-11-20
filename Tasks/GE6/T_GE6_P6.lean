import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P6

Extreme Kerr: M - M_irr = (1 - 1/√2) M, about 29 % of M (Carroll (7.149), (7.152)).

The statement is `Lightlike.kerr_extreme_extraction`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. At `a = M`, `r₊ = M`, so `M_irr² = M²/2`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/GR/KerrHorizon.lean`: `kerrRplus`

Lemmas about them, which a proof may use:

* `kerrΔ_rplus` (`Lightlike/GR/KerrHorizon.lean`)
* `rplus_sq_add` (`Lightlike/GR/KerrHorizon.lean`)
* `kerrKappa_eq` (`Lightlike/GR/KerrHorizon.lean`)
* `kerr_chi_null` (`Lightlike/GR/KerrHorizon.lean`)
* `kerrKappa_eq_altas` (`Lightlike/GR/KerrHorizon.lean`)
* `kerr_schwarzschild_limit` (`Lightlike/GR/KerrHorizon.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.kerr_extreme_extraction

## References

Milestone GE6 (Kerr in Boyer–Lindquist coordinates; Killing horizons, surface gravity and angular
velocity), ROADMAP section "Lorentzian and Riemannian geometry".
Source: M. Visser, The Kerr spacetime: a brief introduction (2007), in The Kerr Spacetime, Cambridge
University Press (2009), Section 9; S. M. Carroll, Lecture Notes on General Relativity (1997), eq.
(7.125); S. M. Carroll, Lecture Notes on General Relativity (1997), eq. (7.126); S. M. Carroll,
Lecture Notes on General Relativity (1997), eq. (7.127); S. M. Carroll, Lecture Notes on General
Relativity (1997), eq. (7.117); S. M. Carroll, Lecture Notes on General Relativity (1997), eq.
(7.149); S. M. Carroll, Lecture Notes on General Relativity (1997), eq. (7.152); S. M. Carroll,
Lecture Notes on General Relativity (1997), eq. (7.154) (`visser-2007`, `carroll-1997`,
`carroll-1997`, `carroll-1997`, `carroll-1997`, `carroll-1997`, `carroll-1997`, `carroll-1997` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Matrix

namespace Lightlike

/-- **Extreme Kerr: the energy extractable by the Penrose process is `M - M_irr = (1 - 1/√2) M`, about 29 % of `M` (Carroll, eqs. (7.149), (7.152) and the sentence after it, `G = 1`).** -/
theorem kerr_extreme_extraction (M : ℝ) (hM : 0 < M) :
    M - Real.sqrt ((kerrRplus M M ^ 2 + M ^ 2) / 4) = (1 - Real.sqrt 2 / 2) * M ∧
      0.29 < 1 - Real.sqrt 2 / 2 ∧ 1 - Real.sqrt 2 / 2 < 0.30 := by
  sorry

end Lightlike
