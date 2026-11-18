import Lightlike.Canonical.MomentumBracket

/-!
# Task T-CA1-P3

The Lie-derivative form of the smeared momentum constraint equals the ADM form with the covariant
divergence of the momentum.

The statement is `Lightlike.Canonical.momentumConstraint_eq_adm`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Pointwise `π^{ij} (ℒ_ξ h)_ij + 2 (h ξ)_i ∇_k π^{ik} = 2 ∂_j (π^{ij} h_{ik} ξ^k)` and
   `integral_pd_eq_zero`.
2. ADM (1962), eq. (3.14b).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Canonical/ADM.lean`: `Canonical.VectorField`, `Canonical.TensorField`,
  `Canonical.momentumConstraint`, `Canonical.momentumDivergence`
* `Lightlike/Canonical/LieDeriv.lean`: `Canonical.SmoothVec`, `Canonical.SmoothTensor`

Lemmas about them, which a proof may use:

* `Canonical.momentumConstraint_eq_adm_of_smooth` (`Lightlike/Canonical/MomentumADM.lean`)
* `Canonical.momentum_pointwise` (`Lightlike/Canonical/MomentumADM.lean`)
* `Canonical.dirDeriv_momentum_h` (`Lightlike/Canonical/MomentumBracket.lean`)
* `Canonical.bracket_momentum_momentum` (`Lightlike/Canonical/MomentumBracket.lean`)
* `Canonical.admBracket_momentum_hamiltonian` (`Lightlike/Canonical/HamiltonianBracket.lean`)
* `Canonical.pd_lower` (`Lightlike/Canonical/MomentumADM.lean`)
* `Canonical.pd_lieDeriv` (`Lightlike/Canonical/LieDeriv.lean`)
* `Canonical.lieDeriv_comm` (`Lightlike/Canonical/LieDeriv.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.Canonical.momentumConstraint_eq_adm

## References

Milestone CA1 (ADM formulation), ROADMAP section "Canonical quantum gravity".
Source: R. Arnowitt, S. Deser and C. W. Misner, The dynamics of general relativity (1962), reprinted
Gen. Rel. Grav. 40 (2008) 1997, Section 4; T. Thiemann, Modern Canonical Quantum General Relativity,
Cambridge University Press (2007), Chapter: Classical Hamiltonian formulation of General Relativity
(`adm-1962`, `thiemann-2007` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Matrix MeasureTheory
open scoped ContDiff

namespace Lightlike.Canonical

theorem momentumConstraint_eq_adm {d : ℕ} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) {h π : TensorField d} (hh : SmoothTensor h)
    (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π) (hπs : ∀ x, (π x)ᵀ = π x) :
    momentumConstraint ξ h π =
      ∫ x, -2 * ∑ i, (∑ k, h x i k * ξ x k) * momentumDivergence h π i x := by
  sorry

end Lightlike.Canonical
