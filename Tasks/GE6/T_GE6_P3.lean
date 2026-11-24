import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P3

The ergosurface g_tt = 0 is (r - M)² = M² - a² cos²θ (Carroll (7.127)).

The statement is `Lightlike.kerr_ergosurface_iff`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Reduce to the numerator `Δ - a² sin²θ = r² - 2Mr + a² cos²θ` of `kerr_gtt_eq`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/GR/Kerr.lean`: `kerrMetric`

Lemmas about them, which a proof may use:

* `ricci_kerr` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_02` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_21` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_13` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_22` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_11` (`Lightlike/GR/KerrRicci.lean`)
* `ricci_kerr_00` (`Lightlike/GR/KerrRicci.lean`)
* `kerr_chi_null` (`Lightlike/GR/KerrHorizon.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.kerr_ergosurface_iff

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

/-- **The locus `g_tt = 0` of the Kerr metric is `(r - M)² = M² - a² cos²θ` (Carroll, eq. (7.127)).** -/
theorem kerr_ergosurface_iff (M a : ℝ) {y : Fin 4 → ℝ} (hr : 0 < y 1) :
    kerrMetric M a y 0 0 = 0 ↔ (y 1 - M) ^ 2 = M ^ 2 - a ^ 2 * Real.cos (y 2) ^ 2 := by
  sorry

end Lightlike
