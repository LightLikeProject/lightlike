import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P4

Finiteness and classification of the critical points of the Lorentzian vertex action.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_criticalSet_finite`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. The bivector reconstruction theorem for Lorentzian data (BDFHP Sec. 5.4.3, via
Barrett–Dowdall–Fairbairn–Gomes–Hellmann, arXiv:0902.1170): critical points give bivector
geometries. The SU(2) case is `Lightlike/Asymptotics/Lorentzian/Classification.lean`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Asymptotics/EPRL/Amplitude.lean`: `Asymptotics.EPRL.BdryData`,
  `Asymptotics.EPRL.edgeSrc`, `Asymptotics.EPRL.edgeTgt`
* `Lightlike/Asymptotics/Lorentzian/Action.lean`: `Asymptotics.Lorentzian.Spinor`
* `Lightlike/Asymptotics/Lorentzian/Classification.lean`: `Asymptotics.Lorentzian.firstCol`
* `Lightlike/Asymptotics/Lorentzian/Stationary.lean`: `Asymptotics.Lorentzian.spinVec`
* `Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`: `Asymptotics.Lorentzian.CriticalSetIs`

Lemmas about them, which a proof may use:

* `Asymptotics.Lorentzian.hessXX_curve` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXX_block` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.closure_of_stationary` (`Lightlike/Asymptotics/Lorentzian/ClosureFromCritical.lean`)
* `Asymptotics.Lorentzian.no_critical_without_closure` (`Lightlike/Asymptotics/Lorentzian/ClosureFromCritical.lean`)
* `Asymptotics.Lorentzian.lorVertex_suppressed_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexSuppressed.lean`)
* `Asymptotics.Lorentzian.lorVertex_asymptotics_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`)
* `Asymptotics.Lorentzian.critical_configuration_closure` (`Lightlike/Asymptotics/Lorentzian/ClosureFromCritical.lean`)
* `Asymptotics.Lorentzian.critZ_tgt` (`Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Asymptotics.Lorentzian.lorVertex_criticalSet_finite

## References

Milestone SF10 (Lorentzian EPRL vertex asymptotics (Barrett et al. 2010)), ROADMAP section "Spin
foams".
Source: J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin
foam amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, §6.4; J.
W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, §4.2.2; J. W.
Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, §5.4.2; J. W.
Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, §5.4.3; J. W.
Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, §6.2; J. W.
Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, eq. (53); J.
W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, eq. (56); J.
W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann and R. Pereira, Lorentzian spin foam
amplitudes: graphical calculus and asymptotics, Class. Quantum Grav. 27 (2010) 165009, eq. (57)
(`bdfhp-2010`, `bdfhp-2010`, `bdfhp-2010`, `bdfhp-2010`, `bdfhp-2010`, `bdfhp-2010`, `bdfhp-2010`,
`bdfhp-2010` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Filter MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL
open _root_.Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.Lorentzian

/-- **The critical set** (the hypothesis `CriticalSetIs` of `lorVertex_asymptotics_fixChart`): for positive spin
parameters, `p = γ j`, unit boundary spinors, closure at every node and nondegenerate boundary data, and a
smooth cutoff `χ` with compact support, the points of the support of `χ a` with `Re S = 0` and `dS = 0` form a
finite set `K` (`CriticalSetIs`). By BDFHP the set has two points for the boundary data of a non-degenerate
Lorentzian 4-simplex; the finiteness is the part of the classification the vertex formula needs. -/
theorem lorVertex_criticalSet_finite {j p : Fin 10 → ℝ} {γ : ℝ} (hj : ∀ k, 0 < j k)
    (hp : ∀ k, p k = γ * j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (hclos : ∀ (a : Fin 5) (i : Fin 3), ∑ k, ((if edgeSrc k = a then j k * spinVec (firstCol (g k 0)) i else 0) +
      (if edgeTgt k = a then j k * spinVec (firstCol (g k 1)) i else 0)) = 0)
    (hnd : ∀ (a : Fin 5) (v : Fin 3 → ℝ), (∀ k, (edgeSrc k = a → ∑ i, v i * spinVec (firstCol (g k 0)) i = 0) ∧
      (edgeTgt k = a → ∑ i, v i * spinVec (firstCol (g k 1)) i = 0)) → v = 0)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) (χ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ K : Finset (Fin 44 → ℝ), CriticalSetIs j p g e χ K := by
  sorry

end Lightlike.Asymptotics.Lorentzian
