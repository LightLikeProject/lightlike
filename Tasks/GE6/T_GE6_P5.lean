import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P5

The irreducible mass of a Kerr black hole: A/(16π) = (M² + √(M⁴ - (Ma)²))/2 (Carroll (7.148),
(7.149)).

The statement is `Lightlike.kerr_irreducible_mass`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. `rplus_sq_add` gives `r₊² + a² = 2 M r₊`; then `√(M⁴ - M² a²) = M √(M² - a²)`.

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

    scripts/context-pack Lightlike.kerr_irreducible_mass

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

/-- **The irreducible mass: `M_irr² = A/(16π) = (r₊² + a²)/4 = (M² + √(M⁴ - (Ma)²))/2` for `A = 4π(r₊² + a²)` (Carroll, eqs. (7.148), (7.149), `G = 1`).** -/
theorem kerr_irreducible_mass (M a : ℝ) (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) :
    (4 * Real.pi * (kerrRplus M a ^ 2 + a ^ 2)) / (16 * Real.pi) =
        (M ^ 2 + Real.sqrt (M ^ 4 - (M * a) ^ 2)) / 2 := by
  sorry

end Lightlike
