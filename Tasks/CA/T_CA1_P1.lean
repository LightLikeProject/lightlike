import Lightlike.Canonical.MomentumBracket

/-!
# Task T-CA1-P1

The bracket of a smeared momentum constraint with a smeared Hamiltonian constraint:
`{D[ξ], H[N]} = H[ξ^k ∂_k N]`.

The statement is `Lightlike.Canonical.bracket_momentum_hamiltonian`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

The bracket is `admBracket` of `Lightlike/Canonical/ADM.lean`: Gateaux derivatives along compactly supported
variations, with the `π`-gradients `ℒ_ξ h` of `D[ξ]` and `hamiltonianPiGradient N` of `H[N]`. The numerical
value of both sides was checked on a grid in dimension two (`4.9662` against `4.9687` for the companion
statement T-CA1-P2, `0.5713` against `0.5710` here); that is evidence, not a proof.

Hint. `H[N]` is a scalar density, so under the simultaneous change `(h, π, N) ↦ (ℒ_ξ h, ℒ_ξ π, ℒ_ξ N)` its
density changes by `∂_k (ξ^k N ℋ)`, which integrates to zero; the curvature part follows from
`Lightlike.scalarCurvature_pullback` for the flow `x ↦ x + t ξ(x)` and a first-variation formula.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Canonical.bracket_momentum_hamiltonian

## References

Milestone CA1 (ADM formulation, constraint algebra), ROADMAP section "Canonical quantum gravity".
Source: Thiemann (2007), Modern Canonical Quantum General Relativity, Chapter 1 (`thiemann-2007` in
docs/tasks/sources.yaml); the constraints are ADM (1962) eqs. (3.14a), (3.14b) (`adm-1962`). Compared with Thiemann, arXiv:gr-qc/0110034 (the lecture-note version of the cited book), §I.1.1, eqs. (I.1.1.27), (I.1.1.28), (I.1.1.36), (I.1.1.37); Hojman-Kuchar-Teitelboim 1976 has not been read. Differences, approved by the owner (17 November 2026): (a) same setting as the source (`C^∞` data, positive definite `h`, symmetric `π`, compactly supported test fields, `2 ≤ d`); (b) partial: one global chart `ℝᵈ`; (c) convention: units `16πG = 1` and the kinetic coefficient `1/(d − 1)`; (d) representation: `D[ξ]` in Lie-derivative form; (e) representation: the bracket through `π`-gradients and Gateaux derivatives, with the sign conventions of `admBracket` and `lieBracket`.
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
