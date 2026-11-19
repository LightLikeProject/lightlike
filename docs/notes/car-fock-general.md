# G3-158 continued: the Fock representation of the CAR over a general Hilbert space `Z` (Dereziński, Theorem 28)

Source read: J. Dereziński, arXiv:math-ph/0511030 (key `derezinski-2006`): §5.3, p. 20 (the antisymmetric Fock space
`Γₐ(Z)`), §7.1, p. 29 (the creation and annihilation operators `a*(w)`, `a(w)` on `Γₐ(Z)`, `Y = Re(Z ⊕ Z̄)` with
`(z, z̄)α(w, w̄) = Re(z|w)`, `φ(y) = a*(w) + a(w)` bounded self-adjoint with `[φ(y₁), φ(y₂)]₊ = 2 y₁αy₂`, Theorem 28).

| Source | Library | Check |
|---|---|---|
| §5.3, p. 20: `Γₐ(Z)` | a Hilbert space `Γ` with a Hilbert basis `B : HilbertBasis (Finset ι) ℂ Γ` (`FermiFockGeneral`; for instance `ℓ²(Finset ι)` with its canonical basis) | (representation) for a Hilbert basis `(eᵢ)_{i ∈ ι}` of `Z` and a linear order on `ι`, the basis vector `B S` stands for the normalized `e_{i₁} ∧ ⋯ ∧ e_{iₖ}`, `i₁ < ⋯ < iₖ`; the identification with the antisymmetric tensors is not built |
| §7.1, p. 29: `a*(w)`, `a(w)` | `fermiCre B j`, `fermiAnn B j` (`a*(eⱼ) B S = (-1)^{#{i ∈ S, i < j}} B (S ∪ {j})`, `fermiCre_basis`), `creW B b w` (`a*(w)`, `‖a*(w)‖ ≤ ‖w‖`), `annW B b w = a*(w)*` | the CAR `fermiAnn_fermiCre_anticomm`, `fermiCre_anticomm`; for general `w`: `annW_creW_anticomm` (`a(w)a*(w') + a*(w')a(w) = ⟪w, w'⟫`), `creW_anticomm`, `annW_anticomm`, from finite combinations of the `eⱼ` by continuity and density |
| §7.1, p. 29: `φ(y) = a*(w) + a(w)`, `[φ(y₁), φ(y₂)]₊ = 2 y₁αy₂` | `fockField`, `isSelfAdjoint_fockField`, `fockField_anticomm` (`= 2 Re⟪w, w'⟫`) | matches, with `Y = Re(Z ⊕ Z̄)` written as `Z` (`y = (w, w̄) ↦ w`, `α = Re⟪·,·⟫`) |
| Theorem 28, p. 29: the Fock representation is irreducible | `fockField_irreducible` (from `fermiFock_irreducible` for the `a*(eⱼ)`, `a(eⱼ)`) | matches; proof: lower a nonzero coefficient to the vacuum with annihilation operators, extract the vacuum by the restrictions to the sets disjoint from finite `J` (limits of products of `a(eⱼ)a*(eⱼ)`), and the vacuum is cyclic |
