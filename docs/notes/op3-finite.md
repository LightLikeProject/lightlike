# OP3 in finite dimensions: states, GNS, the KMS condition and modular theory on `Mₙ(ℂ)`

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
- R. Longo, "Lectures on Conformal Nets, Part I" (lecture notes, Università di Roma Tor Vergata), Chapter 2, Section 2.1, pp. 21-22:
  standard subspaces (closed real subspaces `H` with `H + iH` dense and `H ∩ iH = 0`), the Tomita operator `S : ξ + iη ↦ ξ - iη`, and
  Lemma 2.1.1 (the fixed points `ker(1 - S)` of a closed densely defined anti-linear involution form a standard subspace), with eq.
  (2.1.2).

Scope: everything here is finite-dimensional (`Matrix n n ℂ`). The general statements of the gap rows (states and GNS on arbitrary
C*-algebras, KMS states of C*-dynamical systems, Tomita-Takesaki for von Neumann algebras, standard subspaces of arbitrary Hilbert spaces)
remain open.

| Source | Library | Check |
|---|---|---|
| (2.23), p. 52, `τ^t(A) = e^{itH} A e^{-itH}` for self-adjoint `H`; (2.24) `ρ(AB) = ρ(τ^{-iβ}(B) A)`, p. 53 | `imagEvol H β B = e^{βH} B e^{-βH}`, `IsKMS H ρ β` (`FiniteKMS`) | matches |
| p. 53, the Gibbs state is `β`-KMS | `isKMS_gibbs` | matches |
| Proposition 2.20, p. 53: `ρ` is `β`-KMS iff `ρ = ρ_β` | `isKMS_iff_eq_gibbs` (for `ρ` of trace `1`, `tr e^{-βH} ≠ 0`) | matches, and more general: `H` is any matrix with `tr e^{-βH} ≠ 0` (true for the source's self-adjoint `H`), `ρ` only of trace `1` |
| §2.4 "States", p. 42: states are density matrices `ρ ≥ 0`, `tr ρ = 1`, identified with `A ↦ tr(ρ A)`, and are exactly the positive normalized linear functionals | `exists_density_of_state` (a positive linear functional `φ` with `φ 1 = 1` is `tr(ρ ·)` with `ρ ≥ 0`, `tr ρ = 1`), `state_of_density` (converse), `density_unique`, `posSemidef_densityOf` (`FiniteStates`) | matches |
| Exercise 2.15 (1)-(2), p. 61: `(ξ|η)_ν = tr(η ν ξ*)`, `π_ν(A) ξ = A ξ`, `η_ν` cyclic, `ν(A) = (η_ν|π_ν(A) η_ν)` | `GNSMat ν` (Mathlib's `Matrix.toMatrixInnerProductSpace`), `gnsRep`, `gnsRep_star`, `gnsVec`, `inner_gnsVec_gnsRep`, `gnsRep_gnsVec_surjective` (`FiniteGNS`) | matches, for a faithful `ν` (`ν` positive definite); the non-faithful case (`H_ν` = maps on `Ran ν`) is not stated |
| Exercise 2.15 (3), p. 61: a cyclic representation associated with `ν` is equivalent to the GNS representation | `gns_unique` (a unitary `U` with `U ψ = η_ν` and `U π(A) = π_ν(A) U`), through the repo's `exists_unitary_of_gram_eq` | matches, for a faithful `ν` |
| Exercise 2.15 (1)-(3), p. 61, for every state `ν` (not only faithful ones) | `densityState` (`A ↦ tr(ν A)` as a positive functional), `inner_gnsCyclicVec_densityState` with Mathlib's GNS space `PositiveLinearMap.GNS`; `gnsCyclicVec`, `inner_gnsCyclicVec`, `denseRange_gnsCyclicVec`, `gns_unique_cstar` for every positive functional on a unital C*-algebra (`GNSCyclic`, `StateGNS`); the non-faithful pure state `|0⟩⟨0|` as a check (`gns_pureState0`) | matches |
| §2.12.1, pp. 62-63: `ς_ρ^t(A) = e^{it log ρ} A e^{-it log ρ}`, `L(ς_ρ^t(A)) = Δ_ρ^{it} L(A) Δ_ρ^{-it}` | `modGroup`, `modOpPow`, `modOpPow_mul_modOpPow_neg` | matches |
| §2.12.1, p. 63: the faithful `ρ` is `(β = -1)`-KMS for `ς_ρ^t(A) = e^{it log ρ} A e^{-it log ρ}` | `isKMS_modular` (`FiniteModular`), with `log ρ` from the spectral decomposition (`logPosDef`, `exp_logPosDef`) | matches |
| (2.34), p. 63: `J Δ_ρ^{1/2} A ξ_ρ = A* ξ_ρ`, `Δ_ρ^z ξ = ρ^z ξ ρ^{-z}`, `J ξ = ξ*`, `ξ_ρ = ρ^{1/2}` | `modConj_modOp_sqrt`, `modOpSqrt`, `modConj`, `sqrtPosDef` | matches |
| p. 63: `Δ_ρ ξ = ρ ξ ρ^{-1}` (and `Δ_ρ^{1/2}` as the positive factor) | `modOpSqrt_modOpSqrt`: `Δ_ρ^{1/2} Δ_ρ^{1/2} ξ = ρ ξ ρ^{-1}`; `modConj_modOpSqrt_modConj`: `J Δ_ρ^{1/2} J = Δ_ρ^{-1/2}` | matches (`Δ^z` only for `z = 1/2, 1`) |
| Longo, §2.1, pp. 21-22, and Lemma 2.1.1 with (2.1.2): `ker(1 - S)` is standard | `hermStandardSubspace` (Mathlib's `StandardSubspace`): the self-adjoint vectors `A η_ν` of the GNS space of a faithful state; `mem_hermStandardSubspace_iff` (it is `ker(1 - S)` for Tomita's `S (A η_ν) = A* η_ν`, `tomitaS`) (`FiniteStandard`) | matches, in the GNS space of a faithful state on `Matrix n n ℂ` |

Checks (task OP3): the Gibbs state of a qubit (`H = diag(0, 1)`, `β = 1`) is KMS (`qubit_gibbs_isKMS`), the maximally mixed state is not
(`qubit_maximallyMixed_not_isKMS`) (`TestsFiniteKMS`).

Reused: Mathlib's matrix exponential (`Matrix.exp_add_of_commute`, `exp_units_conj`, `exp_diagonal`), the center of a matrix algebra
(`mem_range_scalar_of_commute_single`), the trace (`trace_mul_comm`, `trace_mul_single`), the spectral theorem for Hermitian matrices
(`IsHermitian.spectral_theorem`, `eigenvectorUnitary`, `PosDef.eigenvalues_pos`), and the inner product `tr(y M xᴴ)` of
`Analysis/Matrix/Order`. Mathlib's `StandardSubspace` (with Tomita's theorem and the KMS condition as a TODO) is used for `hermStandardSubspace`, and Mathlib's GNS
construction for positive functionals on C*-algebras (`PositiveLinearMap.GNS`, with the cyclic vector as a TODO) for `GNSCyclic`, which
adds the cyclic vector and the uniqueness; the positive-map `StarHomClass` instance gives the hermiticity in `FiniteStates`. Physlib has no KMS or modular theory.

Not stated (open): the general (infinite-dimensional) statements named under Scope; for GNS the general unital C*-algebra case is proved
(`GNSCyclic`), but the source compared with it here is the matrix case.
