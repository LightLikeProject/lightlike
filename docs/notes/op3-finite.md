# OP3 in finite dimensions: the KMS condition and the GNS representation on `Mₙ(ℂ)`

Sources read:
- V. Jakšić, Y. Ogata, Y. Pautrat, C.-A. Pillet, "Entropic fluctuations in quantum statistical mechanics. An introduction",
  arXiv:1106.3786: Section 2.4 "States", p. 42; eq. (2.23), Section 2.8 "Dynamical systems", p. 52; Section 2.9 "Gibbs states, KMS condition and variational
  principle", eq. (2.24) and Proposition 2.20, p. 53; Exercise 2.15 "The GNS representation", p. 61; Section 2.12.1 "Modular group and
  modular operator", pp. 62-63, with eq. (2.34).
- E. Witten, "Notes on some entanglement properties of quantum field theory", arXiv:1803.04993, Section 4.1 (eqs. (4.26)-(4.32),
  pp. 35-36) and Section 4.2 (eqs. (4.35)-(4.37), p. 37, and (4.42)-(4.47), pp. 38-39): the same objects in the tensor-product picture
  `H = H₁ ⊗ H₂`, `Δ_Ψ = ρ₁ ⊗ ρ₂⁻¹`, `Δ^{is} (a ⊗ 1) Δ^{-is} = ρ₁^{is} a ρ₁^{-is} ⊗ 1`, and the thermal (KMS) boundary values
  of `F(z) = Tr e^{-H} b e^{-izH} a e^{izH}` with `ρ₁ = e^{-H}` (eq. (4.46)-(4.47)). Used for orientation; the statements below are
  compared with the JOPP locations.

Scope: everything here is finite-dimensional (`Matrix n n ℂ`). The general statements of the gap rows (states and GNS on arbitrary
C*-algebras, KMS states of C*-dynamical systems, Tomita-Takesaki for von Neumann algebras, standard subspaces of arbitrary Hilbert spaces)
remain open.

| Source | Library | Check |
|---|---|---|
| (2.23), p. 52, `τ^t(A) = e^{itH} A e^{-itH}` for self-adjoint `H`; (2.24) `ρ(AB) = ρ(τ^{-iβ}(B) A)`, p. 53 | `imagEvol H β B = e^{βH} B e^{-βH}`, `IsKMS H ρ β` (`FiniteKMS`) | matches |
| p. 53, the Gibbs state is `β`-KMS | `isKMS_gibbs` | matches |
| Proposition 2.20, p. 53: `ρ` is `β`-KMS iff `ρ = ρ_β` | `isKMS_iff_eq_gibbs` (for `ρ` of trace `1`, `tr e^{-βH} ≠ 0`) | matches, and more general: `H` is any matrix with `tr e^{-βH} ≠ 0` (true for the source's self-adjoint `H`), `ρ` only of trace `1` |
| Exercise 2.15 (1)-(2), p. 61: `(ξ|η)_ν = tr(η ν ξ*)`, `π_ν(A) ξ = A ξ`, `η_ν` cyclic, `ν(A) = (η_ν|π_ν(A) η_ν)` | `GNSMat ν` (Mathlib's `Matrix.toMatrixInnerProductSpace`), `gnsRep`, `gnsRep_star`, `gnsVec`, `inner_gnsVec_gnsRep`, `gnsRep_gnsVec_surjective` (`FiniteGNS`) | matches, for a faithful `ν` (`ν` positive definite); the non-faithful case (`H_ν` = maps on `Ran ν`) is not stated |
| Exercise 2.15 (3), p. 61: a cyclic representation associated with `ν` is equivalent to the GNS representation | `gns_unique` (a unitary `U` with `U ψ = η_ν` and `U π(A) = π_ν(A) U`), through the repo's `exists_unitary_of_gram_eq` | matches, for a faithful `ν` |

Checks (task OP3, the qubit Gibbs state and a non-Gibbs state) are not in this change.

Reused: Mathlib's matrix exponential (`Matrix.exp_add_of_commute`), the repo's `exists_unitary_of_gram_eq`, the center of a matrix algebra
(`mem_range_scalar_of_commute_single`), the trace (`trace_mul_comm`, `trace_mul_single`), and the inner product `tr(y M xᴴ)` of
`Analysis/Matrix/Order`. Mathlib has `StandardSubspace` (with Tomita's theorem and the KMS condition as a TODO) and the GNS construction
for positive functionals on C*-algebras (`PositiveLinearMap.GNS`, with the cyclic vector as a TODO); neither covers the finite-dimensional
statements above. Physlib has no KMS or modular theory.

Not stated here: the state-density matrix correspondence (Section 2.4), the modular theory of Section 2.12.1 and standard subspaces; GNS for a
non-faithful state; the general (infinite-dimensional) statements named under Scope.
