import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# Task T-SF10-P3

The far part of the Lorentzian vertex integral is of lower order.

The statement is `Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Split `1 - χ = (ψ - χ) + (1 - ψ)` for a smooth compactly supported cutoff `ψ ≥ χ` in `U`, equal to `1` near `K`, and apply `lorVertex_farRemainder_compact` and `lorVertex_farRemainder_tail`; the sum of an integrable function and an integrable function is integrable and the `O` bounds add.

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
* `Asymptotics.Lorentzian.hessXX_block` (`Lightlike/Asymptotics/Lorentzian/HessianNode.lean`)
* `Asymptotics.Lorentzian.hessXX_cross` (`Lightlike/Asymptotics/Lorentzian/HessianAssembly.lean`)

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


/-- **The far remainder** (the hypothesis `FarRemainderBound` of `lorVertex_asymptotics_fixChart`): for positive spin
parameters, unit boundary spinors, smooth compactly supported cutoff `χ` with values in `[0, 1]`, supported in the chart
domain `U`, equal to `1` near the finite set `K` of critical points of the support of `A`, the integral
`∫ (1 - χ) A e^{λ S}` is integrable for every `λ ∈ ℕ` and `O(λ^{-23})`.

**Change from the first form.** `CriticalSetIs j p g e χ K` (critical points only inside `tsupport (χ A)`) is replaced by
`CriticalSetIs j p g e (fun _ => 1) K` (every critical point of `tsupport A` is in `K`), and the chart hypotheses of
`lorVertex_asymptotics_fixChart` (`U`, `hP`, `hA`) are added. Without the change the statement is false: a nondegenerate
critical point outside `tsupport χ` contributes `c λ^{-22}` (`docs/notes/sf10-p3-assessment.md`). The proof is the sum of
`lorVertex_farRemainder_compact_proof` (the part `ψ - χ`, in `Lightlike/SpinFoam/VertexAsymptoticsHyp/FarCompact.lean`)
and `lorVertex_farRemainder_tail` (the part `1 - ψ`), for a cutoff `ψ`
chosen in the proof. Not in BDFHP. -/
theorem lorVertex_farRemainder
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
    (χ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ1 : ∀ x ∈ K, χ =ᶠ[nhds x] fun _ => 1) :
    FarRemainderBound j p g e χ := by
  sorry

end Lightlike.Asymptotics.Lorentzian
