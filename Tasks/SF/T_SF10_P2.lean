import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P2

Invertibility of the Hessian of the Lorentzian vertex action at a critical point.

The statement is `Lightlike.Asymptotics.Lorentzian.lorHessian_invertible_at_critical`, at the end of
this file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Reduce to `Im(-H)` injective on the kernel of `Re(-H)`: `Re(-H)` is positive semidefinite (a sum
   of squares of the linearised alignment conditions) and `-H v = 0` forces `Re(-H) v = 0` and
   `Im(-H) v = 0`. The closed form of the blocks is `hessBlockMatrix`
   (`Lightlike/Asymptotics/Lorentzian/HessianAssembly.lean`).
2. A certified computation for the regular simplex (numerical evidence:
   `scripts/asymptotics/lorentzian_hessian_kernel_check.py`) does not settle all nondegenerate data.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Asymptotics/EPRL/Amplitude.lean`: `Asymptotics.EPRL.BdryData`,
  `Asymptotics.EPRL.edgeSrc`, `Asymptotics.EPRL.edgeTgt`
* `Lightlike/Asymptotics/Lorentzian/Action.lean`: `Asymptotics.Lorentzian.Spinor`
* `Lightlike/Asymptotics/Lorentzian/Classification.lean`: `Asymptotics.Lorentzian.firstCol`
* `Lightlike/Asymptotics/Lorentzian/Stationary.lean`: `Asymptotics.Lorentzian.spinVec`
* `Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`: `Asymptotics.Lorentzian.fixDomain`
* `Lightlike/Asymptotics/Lorentzian/Vertex.lean`: `Asymptotics.Lorentzian.lorChartAction`,
  `Asymptotics.Lorentzian.lorHessian`
* `Lightlike/Asymptotics/Lorentzian/VertexHaarChart.lean`: `Asymptotics.Lorentzian.fixVertexChart`

Lemmas about them, which a proof may use:

* `Asymptotics.Lorentzian.lorVertex_suppressed_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexSuppressed.lean`)
* `Asymptotics.Lorentzian.lorVertex_asymptotics_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`)
* `Asymptotics.Lorentzian.lorChartAction_fixVertexChart_contDiffOn` (`Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`)
* `Asymptotics.Lorentzian.lorVertex_asymptotics` (`Lightlike/Asymptotics/Lorentzian/Vertex.lean`)
* `Asymptotics.Lorentzian.lorVertex_asymptotics_local` (`Lightlike/Asymptotics/Lorentzian/VertexLocal.lean`)
* `Asymptotics.Lorentzian.hasDerivAt_chartAction_aligned` (`Lightlike/Asymptotics/Lorentzian/VertexSuppressed.lean`)
* `Asymptotics.Lorentzian.lorVertex_asymptotics_vertexChart` (`Lightlike/Asymptotics/Lorentzian/VertexChart.lean`)
* `Asymptotics.Lorentzian.hessXX_block` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Asymptotics.Lorentzian.lorHessian_invertible_at_critical

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

/-- **Invertibility of the Hessian at a critical point** (the hypothesis `HessianInvertible` of
`lorVertex_asymptotics_fixChart`): for positive spin parameters `j`, `p = γ j`, unit boundary spinors, closure
of the normals at every node and nondegenerate boundary data (at each node the normals span `ℝ³`), at every
point `x` of the chart domain with `Re S(x) = 0` and `dS(x) = 0` the matrix `-H(x)` has nonzero determinant.
The hypotheses are the natural ones; whether they suffice is part of the task. -/
theorem lorHessian_invertible_at_critical {j p : Fin 10 → ℝ} {γ : ℝ} (hj : ∀ k, 0 < j k)
    (hp : ∀ k, p k = γ * j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (hclos : ∀ (a : Fin 5) (i : Fin 3), ∑ k, ((if edgeSrc k = a then j k * spinVec (firstCol (g k 0)) i else 0) +
      (if edgeTgt k = a then j k * spinVec (firstCol (g k 1)) i else 0)) = 0)
    (hnd : ∀ (a : Fin 5) (v : Fin 3 → ℝ), (∀ k, (edgeSrc k = a → ∑ i, v i * spinVec (firstCol (g k 0)) i = 0) ∧
      (edgeTgt k = a → ∑ i, v i * spinVec (firstCol (g k 1)) i = 0)) → v = 0)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) (x : Fin 44 → ℝ) (hx : x ∈ fixDomain e)
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0)
    (hd : fderiv ℝ (lorChartAction j p g (fixVertexChart e)) x = 0) :
    (-lorHessian j p g (fixVertexChart e) x).det ≠ 0 := by
  sorry

end Lightlike.Asymptotics.Lorentzian
