import Lightlike.Canonical.Hypersurface

/-!
# Task T-CA1-P5

The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint on a hypersurface is the Hamiltonian constraint smeared with the derivative of the lapse along the shift.

The statement is `Lightlike.Canonical.bracket_momentum_hamiltonian_M`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. In every chart the integrands are those of `admBracket_momentum_hamiltonian` (`Lightlike/Canonical/HamiltonianBracket.lean`); the new content is the chart independence of the sum over the atlas pieces, as for T-CA1-P4, and the covariance of the scalar curvature under a chart change (`Lightlike/Spacetime/Chart*.lean`).

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Canonical.bracket_momentum_hamiltonian_M

## References

Milestone CA1 (ADM formulation, constraint algebra), ROADMAP section "Canonical quantum gravity"; design:
`docs/notes/ca1-hypersurface-design.md`.
Source: T. Thiemann, arXiv:gr-qc/0110034, §I.1.1, eqs. (I.1.1.28), (I.1.1.36), (I.1.1.37) (the lecture-note version of
`thiemann-2007`; the constraint algebra is stated there for a spatial manifold `σ` with `∂σ = ∅`); Hojman–Kuchař–Teitelboim
1976 has not been read. Differences from the source, to be approved by the maintainers: (a) same setting as the source
(smooth data, positive definite `h`, compactly supported smearing fields); (b) the manifold `Σ` has no boundary and is
second countable Hausdorff, a chart-wise data model (`IsCovTensor`, `IsVec`, `IsDensity`) instead of sections of tensor
bundles: a representation difference; (c) units `16πG = 1` and the kinetic coefficient `1/(d - 1)`: a convention; (d) the
momentum constraint in the Lie-derivative form, equal to the ADM form by `momentumConstraint_eq_adm_of_smooth` on one
chart: a representation; (e) the bracket through `π`-gradients and Gateaux derivatives along chart families:
a representation. Comparison with the source: the structure of the statements and the signs agree (arXiv:gr-qc/0110034
eq. (I.1.1.37)); the manifold-level data model is this library's.
-/

open Matrix MeasureTheory
open scoped ContDiff Manifold

namespace Lightlike.Canonical

theorem bracket_momentum_hamiltonian_M {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
    (hR : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin d → ℝ) ∞ (Fin d → ℝ)
      (fun x : M => TangentSpace 𝓘(ℝ, Fin d → ℝ) x))
    {π : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)} (hπ : IsDensity π)
    {ξ : ChartFam M d (Fin d → ℝ)} (hξ : IsVec ξ) (hξc : HasCompactSupportFam ξ) {N : M → ℝ}
    (hN : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ N) (hNc : HasCompactSupport N) :
    admBracketM (momentumConstraintM ξ) (hamiltonianConstraintM N) (fun h _ => momentumPiGradM ξ h)
        (hamiltonianPiGradM N) (fun x₀ => (NondegMetric.ofRiemannian hR).coordMetric x₀) π =
      hamiltonianConstraintM (shiftLapse ξ N) (fun x₀ => (NondegMetric.ofRiemannian hR).coordMetric x₀) π := by
  sorry

end Lightlike.Canonical
