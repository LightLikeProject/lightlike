import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P1

Joint integrability of the Lorentzian vertex integrand.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_jointIntegrable`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. Bound the modulus of the integrand by the product of the weights `triWeight` of the ten edges
and integrate edge by edge: the finiteness of the Lorentzian EPRL vertex
(Kaminski–Kisielowski–Lewandowski, arXiv:0909.0939) or a direct estimate of `∏_e ∫ ‖g_e‖ dw` from
`norm_exp_triAction` and the integrability of the `Ω` density
(`Lightlike/Asymptotics/Lorentzian/Amplitude.lean`).

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Asymptotics/EPRL/Amplitude.lean`: `Asymptotics.EPRL.BdryData`
* `Lightlike/Asymptotics/Lorentzian/Action.lean`: `Asymptotics.Lorentzian.Spinor`
* `Lightlike/Asymptotics/Lorentzian/Classification.lean`: `Asymptotics.Lorentzian.firstCol`
* `Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`:
  `Asymptotics.Lorentzian.VertexJointIntegrable`

Lemmas about them, which a proof may use:

* `Asymptotics.Lorentzian.lorVertex_asymptotics_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`)
* `Asymptotics.Lorentzian.critZ_src` (`Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean`)
* `Asymptotics.Lorentzian.critZ_tgt` (`Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean`)
* `Asymptotics.Lorentzian.hessXZ_tgt` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXZ_src` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessZZ_line` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXX_block` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXX_cross` (`Lightlike/Asymptotics/Lorentzian/HessianAssembly.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Asymptotics.Lorentzian.lorVertex_jointIntegrable

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

/-- **Joint integrability of the vertex integrand** (the hypothesis `VertexJointIntegrable` of
`lorVertex_asymptotics_fixChart`): for positive spin parameters and unit boundary spinors, for every
`λ ∈ ℕ` the outer integral of the vertex of the scaled data is measurable and the integrand is jointly
integrable in the fixed charts. The hypotheses are those of the vertex formula; whether they suffice is part
of the task (a smaller range of spins may be needed). -/
theorem lorVertex_jointIntegrable {j p : Fin 10 → ℝ} (hj : ∀ k, 0 < j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1) :
    VertexJointIntegrable j p g := by
  sorry

end Lightlike.Asymptotics.Lorentzian
