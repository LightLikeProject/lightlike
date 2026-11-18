import Lightlike.Canonical.HamiltonianHHBracket

/-!
# Task T-CA1-P2

The bracket of two smeared Hamiltonian constraints is a smeared momentum constraint with the
structure function h^{ij}.

The statement is `Lightlike.Canonical.bracket_hamiltonian_hamiltonian`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. The first variation of `√h R` (Palatini identity in coordinates), an integration by parts, and
   the antisymmetry in `N, M`.
2. Hojman–Kuchař–Teitelboim (1976) and Thiemann (2007), Chapter 1: the hypersurface deformation
   algebra.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Canonical/ADM.lean`: `Canonical.TensorField`, `Canonical.admBracket`,
  `Canonical.hamiltonianConstraint`, `Canonical.hamiltonianPiGradient`,
  `Canonical.momentumConstraint`
* `Lightlike/Canonical/LieDeriv.lean`: `Canonical.SmoothTensor`
* `Lightlike/Spacetime/Curvature.lean`: `pd`

Lemmas about them, which a proof may use:

* `Canonical.admBracket_momentum_hamiltonian` (`Lightlike/Canonical/HamiltonianBracket.lean`)
* `Canonical.V1_split` (`Lightlike/Canonical/HamiltonianHH.lean`)
* `Canonical.first_deriv_split` (`Lightlike/Canonical/HamiltonianHH.lean`)
* `Canonical.bracket_pointwise` (`Lightlike/Canonical/HamiltonianBracket.lean`)
* `Canonical.bracket_momentum_momentum` (`Lightlike/Canonical/MomentumBracket.lean`)
* `Canonical.pd_wJ` (`Lightlike/Canonical/FirstOrderPotential.lean`)
* `Canonical.pd_kinJ` (`Lightlike/Canonical/DensityDeriv.lean`)
* `Canonical.pd_lower` (`Lightlike/Canonical/MomentumADM.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Canonical.bracket_hamiltonian_hamiltonian

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

theorem bracket_hamiltonian_hamiltonian {d : ℕ} (hd : 2 ≤ d) {N M : (Fin d → ℝ) → ℝ}
    (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N) (hM : ContDiff ℝ ∞ M) (hMc : HasCompactSupport M)
    {h π : TensorField d} (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π)
    (hπs : ∀ x, (π x)ᵀ = π x) :
    admBracket (hamiltonianConstraint N) (hamiltonianConstraint M) (hamiltonianPiGradient N)
        (hamiltonianPiGradient M) h π =
      momentumConstraint
        (fun x i => ∑ j, (h x)⁻¹ i j * (N x * Lightlike.pd j M x - M x * Lightlike.pd j N x)) h π := by
  exact bracket_hamiltonian_hamiltonian_of_smooth hd hN hNc hM hMc hh hpos hπ hπs

end Lightlike.Canonical
