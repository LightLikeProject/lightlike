import Lightlike.Canonical.HypersurfaceBridge

/-!
# Task T-CA1-P7

On a single global chart the constraints on a hypersurface are the constraints of the chart.

The statement is `Lightlike.Canonical.constraintM_bridge`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. On `M = ℝᵈ` every chart is the identity (`extChartAt_model_space_eq_id`) and the atlas pieces partition `ℝᵈ`; the integrands are continuous with compact support, so the sum of the integrals over the pieces is the integral over `ℝᵈ` (`integral_iUnion`, `tsum` over the countable disjoint measurable pieces).

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Canonical.constraintM_bridge

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

theorem constraintM_bridge {d : ℕ} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) {N : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N)
    (hNc : HasCompactSupport N) {h π : TensorField d} (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef)
    (hπ : SmoothTensor π) :
    momentumConstraintM (M := Fin d → ℝ) (fun _ => ξ) (fun _ => h) (fun _ => π) = momentumConstraint ξ h π ∧
      hamiltonianConstraintM (M := Fin d → ℝ) N (fun _ => h) (fun _ => π) = hamiltonianConstraint N h π := by
  exact constraintM_bridge_global ξ N h π

end Lightlike.Canonical
