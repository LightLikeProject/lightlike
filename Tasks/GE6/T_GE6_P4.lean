import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P4

The Kerr metric at M = 0 is flat space in ellipsoidal coordinates, diagonal form (Carroll (7.117)).

The statement is `Lightlike.kerr_mass_zero`, at the end of this file. Replace its `sorry` by a proof
and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Entrywise: `Matrix.ext` with `fin_cases`, then `simp [kerrMetric, kerrD]` and `field_simp`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/GR/Kerr.lean`: `kerrMetric`, `kerrS`

Lemmas about them, which a proof may use:

* `det_kerrMetric` (`Lightlike/GR/Kerr.lean`)
* `kgg11_eq` (`Lightlike/GR/KerrControl.lean`)
* `kgg22_eq` (`Lightlike/GR/KerrControl.lean`)
* `pd_kerrS` (`Lightlike/GR/Kerr.lean`)
* `kerrS_pos` (`Lightlike/GR/Kerr.lean`)
* `ricci_kerr` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_02` (`Lightlike/GR/KerrRicci.lean`)
* `kerr_chi_null` (`Lightlike/GR/KerrHorizon.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.kerr_mass_zero

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

/-- **For `M = 0` the Kerr metric is `-dt² + (ρ²/(r²+a²)) dr² + ρ² dθ² + (r²+a²) sin²θ dφ²` (Carroll, eq. (7.117)).** -/
theorem kerr_mass_zero (a : ℝ) {y : Fin 4 → ℝ} (hr : 0 < y 1) :
    kerrMetric 0 a y = Matrix.diagonal ![-1, kerrS a y / (y 1 ^ 2 + a ^ 2), kerrS a y,
      (y 1 ^ 2 + a ^ 2) * Real.sin (y 2) ^ 2] := by
  sorry

end Lightlike
