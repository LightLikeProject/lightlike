import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P3

The far part of the Lorentzian vertex integral is of lower order.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Where `Re S ≤ -δ` on the support of `1 - χ` the integrand decays exponentially; the
non-compact directions need an integrability estimate of `e^{λ S}` against the amplitude (`Ω`
density) uniform in `λ`, and non-stationary phase (`nonstationary_phase`,
`Lightlike/Oscillatory/Localisation.lean`) where `Re S = 0` and `dS ≠ 0`.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Asymptotics/EPRL/Amplitude.lean`: `Asymptotics.EPRL.BdryData`
* `Lightlike/Asymptotics/Lorentzian/Action.lean`: `Asymptotics.Lorentzian.Spinor`
* `Lightlike/Asymptotics/Lorentzian/Classification.lean`: `Asymptotics.Lorentzian.firstCol`
* `Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`: `Asymptotics.Lorentzian.CriticalSetIs`,
  `Asymptotics.Lorentzian.FarRemainderBound`

Lemmas about them, which a proof may use:

* `Asymptotics.Lorentzian.lorVertex_asymptotics_fixChart` (`Lightlike/Asymptotics/Lorentzian/VertexFixChart.lean`)
* `Asymptotics.Lorentzian.critZ_src` (`Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean`)
* `Asymptotics.Lorentzian.critZ_tgt` (`Lightlike/Asymptotics/Lorentzian/CriticalSpinors.lean`)
* `Asymptotics.Lorentzian.hessXZ_tgt` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXZ_src` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessZZ_line` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXX_cross` (`Lightlike/Asymptotics/Lorentzian/HessianAssembly.lean`)
* `Asymptotics.Lorentzian.hessXX_curve` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder

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

/-- **The far remainder** (the hypothesis `FarRemainderBound` of `lorVertex_asymptotics_fixChart`): for
positive spin parameters, unit boundary spinors, a smooth compactly supported cutoff `χ` with values in
`[0, 1]` equal to `1` near the finite set `K` of critical points in the support (`CriticalSetIs`), the integral
`∫ (1 - χ) a e^{λ S}` is integrable for every `λ ∈ ℕ` and `O(λ^{-23})`. This is not in BDFHP; the hypotheses
may need to be strengthened. -/
theorem lorVertex_farRemainder {j p : Fin 10 → ℝ} {γ : ℝ} (hj : ∀ k, 0 < j k)
    (hp : ∀ k, p k = γ * j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) (χ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (K : Finset (Fin 44 → ℝ)) (hK : CriticalSetIs j p g e χ K)
    (hχ1 : ∀ x ∈ K, χ =ᶠ[nhds x] fun _ => 1) :
    FarRemainderBound j p g e χ := by
  sorry

end Lightlike.Asymptotics.Lorentzian
