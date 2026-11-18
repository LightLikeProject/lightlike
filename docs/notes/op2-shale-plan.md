# T-OP2-P3 (Shale's criterion): assessment and plan

Statement: for a Fock representation `R` of a complex Hilbert space `h` and a Bogoliubov transformation `T`,
`Implements R T ↔ IsHilbertSchmidt T.betaPart`.

## What exists

`FockRep` (a cyclic vacuum representation of the Weyl relations with the Fock expectation), existence
(`fockRepOf`, the reproducing kernel Hilbert space of the Fock kernel) and uniqueness (`fockUnitary`), the
Gram-matrix unitary (`exists_unitary_of_gram_eq`), the Gram function `fockGram`. No Fock number operator, no
second quantization, no Gaussian measures on finite-dimensional subspaces.

## The mathematical route (both directions need analysis not in the library)

* Reduction. `T` is implemented iff the Weyl relations twisted by `T`, `W'(f) = W(T f)`, give a representation
  equivalent to `W`. Since `fockGram (T f) (T g) = ⟪W f Ψ, W g Ψ⟫` for a vector `Ψ` with
  `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)` (the Gram argument of the uniqueness proof), `T` is implemented iff there is
  a *cyclic* vector `Ψ` of `W` with that Gaussian characteristic function. Cyclicity of every nonzero vector is
  the irreducibility of the Fock representation, itself a consequence of the vacuum being the only vector
  with the Fock characteristic function (the projection onto the vacuum is a limit of Gaussian averages of
  the Weyl unitaries).
* `⇒`. For `Ψ = U⁻¹ Ω` the overlap `|⟪Ω, Ψ⟫|² = lim_N ∏_{i ≤ N} (1 + ‖β e_i‖²)^{-1}` (Gaussian integrals over
  the span of the first `N` basis vectors); it is positive, so `∑ ‖β e_i‖² < ∞`.
* `⇐`. For `β` Hilbert-Schmidt, the squeezed vector `Ψ` is a limit of finite-mode squeezed vectors, which
  needs the finite-dimensional symplectic structure (polar decomposition of `T` restricted to finite
  subspaces) and a Cauchy estimate from `∑ ‖β e_i‖² < ∞`.

## Pieces and estimate

1. Irreducibility of the Fock representation, and the projection onto the vacuum as a Gaussian limit: 2-3 days.
2. The reduction above (twisted representation, cyclic vector with Gaussian characteristic function): 1 day.
3. The direction `⇒`, the infinite product and Gaussian integrals: 2 days.
4. The direction `⇐`, finite-mode squeezing and the limit: 2-3 days.

Research-level, about a week of work, with no standard Mathlib support for Gaussian integrals over
finite-dimensional subspaces of a Hilbert space (finite-dimensional Gaussian integrals exist in Mathlib).
