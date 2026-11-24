import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P1

The Kerr metric component g_tt = -(Δ - a² sin²θ)/ρ² (Carroll (7.125)).

The statement is `Lightlike.kerr_gtt_eq`, at the end of this file. Replace its `sorry` by a proof
and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Unfold `kerrMetric`, `kerrS`, `kerrD`; clear the denominator with `kerrS_pos` and use `sin² +
cos² = 1`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/GR/Kerr.lean`: `kerrMetric`, `kerrD`, `kerrS`

Lemmas about them, which a proof may use:

* `det_kerrMetric` (`Lightlike/GR/Kerr.lean`)
* `kgg11_eq` (`Lightlike/GR/KerrControl.lean`)
* `kgg22_eq` (`Lightlike/GR/KerrControl.lean`)
* `pd_kerrS` (`Lightlike/GR/Kerr.lean`)
* `pd_kerrD` (`Lightlike/GR/Kerr.lean`)
* `kerrS_pos` (`Lightlike/GR/Kerr.lean`)
* `ricci_kerr` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_02` (`Lightlike/GR/KerrRicci.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.kerr_gtt_eq

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

/-- **The Kerr metric component `g_tt = -(Δ - a² sin²θ)/ρ²` (Carroll, eq. (7.125)).** -/
theorem kerr_gtt_eq (M a : ℝ) {y : Fin 4 → ℝ} (hr : 0 < y 1) :
    kerrMetric M a y 0 0 = -(kerrD M a y - a ^ 2 * Real.sin (y 2) ^ 2) / kerrS a y := by
  sorry

end Lightlike
