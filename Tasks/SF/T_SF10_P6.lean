import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P6

The non-compact tail of the Lorentzian far remainder is of lower order.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder_tail`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. For `Re S ≤ 0` (`re_lorAction_le_zero`) the modulus of the integrand at `λ ≥ 1` is at most that at `λ = 1`, which gives the integrability for every `λ ∈ ℕ` once it holds for `λ = 1` (the weights `triWeight` of the ten edges, `VertexJointIntegrable`). The decay needs a quantitative gap `Re S ≤ -δ` away from a neighbourhood of `K` in the non-compact directions and non-stationary phase (`nonstationary_phase`, `Lightlike/Oscillatory/Localisation.lean`) where `Re S = 0` and `dS ≠ 0`. If the estimate is false, report a counterexample (`docs/notes/sf10-p3-assessment.md`).

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

open Filter MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL Matrix
open _root_.Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.Lorentzian

/-- **The non-compact tail of the far remainder is `O(λ^{-23})`** (the new estimate). For a smooth compactly supported
cutoff `ψ` in the chart domain `U` with `ψ = 1` near each point of the finite critical set `K`, where `K` contains every
point of `tsupport A` with `Re S = 0` and `dS = 0` (`CriticalSetIs` with the cutoff `1`), `(1 - ψ) A e^{λ S}` is
integrable for every `λ ∈ ℕ` and its integral is `O(λ^{-23})`. This needs an integrable majorant uniform in `λ` and a
quantitative gap `Re S ≤ -δ` away from a neighbourhood of `K` in the non-compact directions; it is not in BDFHP. If it
is false, the task is to report a counterexample like the one for the first form of `lorVertex_farRemainder` (the
`λ^{-22}` contribution of a critical point outside the support of the cutoff, `docs/notes/sf10-p3-assessment.md`).
No decay hypothesis is assumed. -/
theorem lorVertex_farRemainder_tail
    {j p : Fin 10 → ℝ} {γ : ℝ} (hj : ∀ k, 0 < j k)
    (hp : ∀ k, p k = γ * j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ fixDomain e)
    (hP : ∀ x ∈ U, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane)
    (hA : ContDiffOn ℝ ∞ (chartAmplitude e) U) (K : Finset (Fin 44 → ℝ))
    (hK : CriticalSetIs j p g e (fun _ => 1) K)
    (ψ : (Fin 44 → ℝ) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hψ01 : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (hψ1 : ∀ x ∈ K, ψ =ᶠ[nhds x] fun _ => 1) :
    (∀ lam : ℕ, Integrable fun x => (((1 - ψ x : ℝ) : ℂ) * chartAmplitude e x) *
        Complex.exp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) ∧
      (fun lam : ℕ => ∫ x, (((1 - ψ x : ℝ) : ℂ) * chartAmplitude e x) *
          Complex.exp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) =O[atTop]
        fun lam : ℕ => ((lam : ℝ) ^ (-((44 : ℝ) / 2) - 1)) := by
  sorry

end Lightlike.Asymptotics.Lorentzian
