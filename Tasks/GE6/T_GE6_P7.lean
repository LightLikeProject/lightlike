import Lightlike.GR.KerrHorizon

/-!
# Task T-GE6-P7

The first law of Kerr black holes dM = (κ/8π) dA + Ω_H dJ along a differentiable family (Carroll
(7.154), (7.155)).

The statement is `Lightlike.kerr_first_law`, at the end of this file. Replace its `sorry` by a proof
and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Differentiate `r₊ = M + √(M² - a²)` (differentiable since `M² - a² > 0`); use `kerrKappa_eq`
and `rplus_sq_add`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/GR/KerrHorizon.lean`: `kerrKappa`, `kerrRplus`, `kerrOmega`

Lemmas about them, which a proof may use:

* `kerr_schwarzschild_limit` (`Lightlike/GR/KerrHorizon.lean`)
* `kerrKappa_eq` (`Lightlike/GR/KerrHorizon.lean`)
* `kerr_chi_null` (`Lightlike/GR/KerrHorizon.lean`)
* `kerrKappa_eq_altas` (`Lightlike/GR/KerrHorizon.lean`)
* `kerrΔ_rplus` (`Lightlike/GR/KerrHorizon.lean`)
* `rplus_sq_add` (`Lightlike/GR/KerrHorizon.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.kerr_first_law

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

/-- **The first law of Kerr black holes: `dM = (κ/8π) dA + Ω_H dJ` along any differentiable family `(M(s), a(s))` with `0 < M`, `a² < M²`, `A = 4π(r₊² + a²)`, `J = M a` (Carroll, eqs. (7.146), (7.148), (7.154), (7.155), `G = 1`).** -/
theorem kerr_first_law (M a : ℝ → ℝ) (s : ℝ) (hM : DifferentiableAt ℝ M s) (ha : DifferentiableAt ℝ a s)
    (hpos : 0 < M s) (hlt : a s ^ 2 < M s ^ 2) :
    deriv M s = kerrKappa (M s) (a s) / (8 * Real.pi) *
        deriv (fun u => 4 * Real.pi * (kerrRplus (M u) (a u) ^ 2 + a u ^ 2)) s +
      kerrOmega (M s) (a s) * deriv (fun u => M u * a u) s := by
  sorry

end Lightlike
