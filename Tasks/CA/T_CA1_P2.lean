import Lightlike.Canonical.MomentumBracket

/-!
# Task T-CA1-P2

The bracket of two smeared Hamiltonian constraints, with the structure function `h^{ij}`:
`{H[N], H[M]} = D[Y]` with `Y^i = h^{ij} (N ∂_j M − M ∂_j N)`.

The statement is `Lightlike.Canonical.bracket_hamiltonian_hamiltonian`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

The bracket is `admBracket` of `Lightlike/Canonical/ADM.lean`, with the `π`-gradient `hamiltonianPiGradient`.
The dimension is `d ≥ 2` because the kinetic coefficient `1/(d − 1)` is the one for which the algebra closes
(in dimension two a grid computation gives `4.9662` for the bracket and `4.9687` for `D[Y]`; with the coefficient
`1/2` of dimension three in dimension two the bracket is `2.6811`, which differs: the coefficient matters). The
numerical values are evidence, not a proof.

Hint. The terms of the bracket without a derivative of `N` or `M` cancel by antisymmetry. What is left comes
from the first variation `δ(√h R)[k] = −√h G^{ij} k_ij + ∂_a (√h V^a)` with `V^a = h^{ij} δΓ^a_{ij} − h^{ia} δΓ^j_{ij}`
along `k = M·δH[N]/δπ`, an integration by parts, and `∇_j P^{ij}` for `P = (2π^{ij} − (2/(d−1)) π h^{ij})/√h`.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Canonical.bracket_hamiltonian_hamiltonian

## References

Milestone CA1 (ADM formulation, constraint algebra), ROADMAP section "Canonical quantum gravity".
Source: Thiemann (2007), Modern Canonical Quantum General Relativity, Chapter 1 (`thiemann-2007` in
docs/tasks/sources.yaml); the constraints are ADM (1962) eqs. (3.14a), (3.14b) (`adm-1962`). The comparison of
the bracket with the cited source is pending: the chapter has not been read. Differences to be approved:
(a) `C^∞` data, positive definite `h`, symmetric `π`, compactly supported test fields, `2 ≤ d`; (b) one global chart `ℝᵈ`;
(c) units `16πG = 1` and the kinetic coefficient `1/(d − 1)`; (d) `D[ξ]` in Lie-derivative form; (e) the bracket
through `π`-gradients and Gateaux derivatives, with the sign conventions of `admBracket` and `lieBracket`.
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
  sorry

end Lightlike.Canonical
