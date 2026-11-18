import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P5

The compact part of the Lorentzian far remainder is of rapidly decreasing order.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder_compact`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. `(ψ - χ) A` is smooth with compact support in `U` and vanishes near `K`, so every point of its support has `Re S < 0` or `dS ≠ 0` (`CriticalSetIs` with the cutoff `1`, `re_lorAction_le_zero` for `Re S ≤ 0`): apply `expPhase_suppressed` (`Lightlike/Asymptotics/Lorentzian/Suppression.lean`) with `S` the chart action, smooth on `U` by the hypothesis `hP`, as in `lorVertex_asymptotics_fixChart`.

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

/-- **The compact part of the far remainder is `O(λ^{-N})` for every `N`.** For smooth cutoffs `χ`, `ψ`
with compact supports in the chart domain `U` and `χ = ψ = 1` near each point of the finite critical set `K`, where `K`
contains every point of `tsupport A` with `Re S = 0` and `dS = 0` (`CriticalSetIs` with the cutoff `1`; see the change
below), `∫ (ψ - χ) A e^{λ S}` is `O(λ^{-N})` for every `N`: the amplitude `(ψ - χ) A` is smooth with compact support and
no critical point of `S` lies in its support (`expPhase_suppressed`).

**Change from the first form of `lorVertex_farRemainder`.** `CriticalSetIs j p g e χ K` described the critical points only
inside `tsupport (χ A)`. A critical point `x₁` of `S` with `Re S (x₁) = 0`, `A x₁ ≠ 0` and a nondegenerate Hessian outside
`tsupport χ` (BDFHP eq. (53) has two parity-related critical points; a cutoff around one leaves the other) contributes
`c λ^{-22}`, `c ≠ 0`, to `∫ (1 - χ) A e^{λ S}`, contradicting the claimed `O(λ^{-23})`. The hypothesis is now
`CriticalSetIs j p g e (fun _ => 1) K`: every critical point of `tsupport A` is in `K`. See `docs/notes/sf10-p3-assessment.md`. -/
theorem lorVertex_farRemainder_compact
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
    (χ ψ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hχ1 : ∀ x ∈ K, χ =ᶠ[nhds x] fun _ => 1) (hψ1 : ∀ x ∈ K, ψ =ᶠ[nhds x] fun _ => 1) (N : ℕ) :
    (fun lam : ℕ => ∫ x, (((ψ x - χ x : ℝ) : ℂ) * chartAmplitude e x) *
        Complex.exp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))) := by
  sorry

end Lightlike.Asymptotics.Lorentzian
