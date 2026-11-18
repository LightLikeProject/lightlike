import Lightlike.Canonical.MomentumADM

/-!
# Task T-CA1-P3

The Lie-derivative form of the smeared momentum constraint equals the ADM form:
`∫ π^{ij} (ℒ_ξ h)_ij dx = ∫ ξ^i R_i dx` with `R_i = −2 π^{ij}{}_{|j}` (ADM 1962, eq. (3.14b)).

The statement is `Lightlike.Canonical.momentumConstraint_eq_adm`, at the end of this file. Replace its `sorry` by a
proof and change nothing else in the file: the proof-task check rejects any other change (CONTRIBUTING.md).

`momentumConstraint ξ h π` is the integral of `π^{ij} (ℒ_ξ h)_ij` (`Lightlike/Canonical/ADM.lean`); the right-hand
side integrates `−2 (h ξ)_i ∇_k π^{ik}` with the covariant divergence `momentumDivergence` of a symmetric tensor
density of weight one, `∂_k π^{ik} + Γ^i_{kl} π^{kl}`, and the Christoffel symbols of `Lightlike.christoffel`.

Hint. Pointwise, `π^{ij} (ℒ_ξ h)_ij + 2 (h ξ)_i ∇_k π^{ik} = 2 ∂_j (π^{ij} h_{ik} ξ^k)`: the Leibniz rule, the symmetry of
`π`, and `h_{ki} Γ^i_{jl} = ½ (∂_j h_{kl} + ∂_l h_{kj} − ∂_k h_{jl})`. The right-hand side integrates to zero for a
compactly supported `ξ` (`Lightlike.Canonical.integral_pd_eq_zero`).

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Canonical.momentumConstraint_eq_adm

## References

Milestone CA1 (ADM formulation, constraint algebra), ROADMAP section "Canonical quantum gravity".
Source: R. Arnowitt, S. Deser and C. W. Misner, The dynamics of general relativity (1962), eq. (3.14b)
(`adm-1962` in docs/tasks/sources.yaml); I read that equation at that location. Differences: the source writes the
constraint as `R_i = −2 π^{ij}{}_{|j}` and smears it as `∫ ξ^i R_i`; here `D[ξ]` is defined in the Lie-derivative form
and this task states that the two agree. The setting is the ADM one: smooth data, a positive definite `h`, a compactly
supported smearing field, one global chart `ℝᵈ` (a hypersurface in a manifold is the task of the geometry layer). A
difference of representation, approved by the maintainers (17 November 2026).
-/

open Matrix MeasureTheory
open scoped ContDiff

namespace Lightlike.Canonical

theorem momentumConstraint_eq_adm {d : ℕ} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) {h π : TensorField d} (hh : SmoothTensor h)
    (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) :
    momentumConstraint ξ h π =
      ∫ x, -2 * ∑ i, (∑ k, h x i k * ξ x k) * momentumDivergence h π i x := by
  exact momentumConstraint_eq_adm_of_smooth hξ hξc hh hpos hπ hπs

end Lightlike.Canonical
