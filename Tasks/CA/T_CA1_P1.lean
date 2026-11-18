import Lightlike.Canonical.MomentumBracket

/-!
# Task T-CA1-P1

The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint is a smeared
Hamiltonian constraint.

The statement is `Lightlike.Canonical.bracket_momentum_hamiltonian`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Covariance of the scalar density `√h R` under the flow of `ξ`, from
   `Lightlike.scalarCurvature_pullback`, and the first variation of the scalar curvature.
2. Hojman–Kuchař–Teitelboim (1976) and Thiemann (2007), Chapter 1: the hypersurface deformation
   algebra.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Canonical/ADM.lean`: `Canonical.VectorField`, `Canonical.TensorField`,
  `Canonical.admBracket`, `Canonical.momentumConstraint`, `Canonical.hamiltonianConstraint`,
  `Canonical.lieTensor`, `Canonical.hamiltonianPiGradient`
* `Lightlike/Canonical/LieDeriv.lean`: `Canonical.SmoothVec`, `Canonical.SmoothTensor`
* `Lightlike/Spacetime/Curvature.lean`: `pd`

Lemmas about them, which a proof may use:

* `Canonical.admBracket_momentum_hamiltonian` (`Lightlike/Canonical/HamiltonianBracket.lean`)
* `Canonical.bracket_pointwise` (`Lightlike/Canonical/HamiltonianBracket.lean`)
* `Canonical.bracket_momentum_momentum` (`Lightlike/Canonical/MomentumBracket.lean`)
* `Canonical.fderivRjet_lie` (`Lightlike/Canonical/CurvatureCovariance.lean`)
* `Canonical.hasDerivAt_scalar_lie` (`Lightlike/Canonical/CurvatureCovariance.lean`)
* `Canonical.pd_lower` (`Lightlike/Canonical/MomentumADM.lean`)
* `Canonical.pd_lieDeriv` (`Lightlike/Canonical/LieDeriv.lean`)
* `Canonical.hamDerivH_add_pi` (`Lightlike/Canonical/DensityCovariance.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Canonical.bracket_momentum_hamiltonian

## References

Milestone CA1 (ADM formulation), ROADMAP section "Canonical quantum gravity".
Source: R. Arnowitt, S. Deser and C. W. Misner, The dynamics of general relativity (1962), reprinted
Gen. Rel. Grav. 40 (2008) 1997, Section 4; T. Thiemann, Modern Canonical Quantum General Relativity,
Cambridge University Press (2007), Chapter: Classical Hamiltonian formulation of General Relativity
(`adm-1962`, `thiemann-2007` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Matrix
open scoped ContDiff

namespace Lightlike.Canonical

theorem bracket_momentum_hamiltonian {d : ℕ} {ξ : VectorField d} {N : (Fin d → ℝ) → ℝ}
    (hξ : SmoothVec ξ) (hξc : ∀ k, HasCompactSupport (fun y => ξ y k))
    (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N) {h π : TensorField d}
    (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) :
    admBracket (momentumConstraint ξ) (hamiltonianConstraint N) (fun h _ => lieTensor ξ h)
        (hamiltonianPiGradient N) h π =
      hamiltonianConstraint (fun x => ∑ k, ξ x k * Lightlike.pd k N x) h π := by
  sorry

end Lightlike.Canonical
