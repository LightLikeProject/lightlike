# G3-156: the Stone-von Neumann theorem for finitely many degrees of freedom

Sources read:
- J. Dereziński, arXiv:math-ph/0511030 (key `derezinski-2006`): §3.1, pp. 9-10 (representations of the CCR, eq. (9);
  irreducibility; regular = strongly continuous along lines, p. 10); Theorem 4 (Stone-von Neumann) and Corollary 1, p. 12
  (statements only; the proof is referred to the literature).
- M. Faulhuber, *Time-Frequency Analysis*, lecture notes, arXiv:2204.01596 (key `faulhuber-2022`), §7.3.1, pp. 90-94:
  Theorem 7.32 (irreducible case) with von Neumann's proof: Lemma 7.34 (Gaussian coefficients and the twisted
  convolution `Φ ♮ Φ^{ξ,η} = e^{-π(ξ²+η²)/2} Φ`), eq. (7.14) (`π(Φ) π(ξ,η) π(Φ) = e^{-π(ξ²+η²)/2} π(Φ)`, so `π(Φ)` is a
  projection), `π(Φ) ≠ 0` from Theorem 7.31(ii) (Fourier inversion), eq. (7.15) (the coefficients of a unit vector of
  `π(Φ)H` are the Schrödinger ones); Theorem 7.35 (a representation is a direct sum of copies).

| Source | Library | Check |
|---|---|---|
| Dereziński (9), p. 9; regular, p. 10 | the repository's `CCRRep h K` (`W f W g = e^{-iσ(f,g)/2} W(f+g)`, `σ = Im⟪f, g⟫`, strongly continuous along lines) | (representation) the symplectic space is a finite-dimensional complex inner product space `h` with `σ = Im⟪·,·⟫`, as in the repository's OP2 setting; every finite-dimensional symplectic space is of this form |
| (joint continuity, used implicitly by the integrals of Lemma 7.34) | `CCRRep.continuous_W` (`CCRJoint`) | from continuity along lines and the Weyl relation, one basis direction at a time |
| Lemma 7.34(b), p. 91 | `integral_gauss_kernel` (`GaussKernel`) | the twisted convolution identity in the normalization of `CCRRep` (Gaussian `e^{-‖z‖²/4}`, constant `(2π)^{dim h}`) |
| eq. (7.14), p. 93 | `gaussAvg_W_gaussAvg`, `vnProj_W_vnProj`, `vnProj_idem` (`GaussAvg`, `StoneVN`) | `P W f P = (2π)^d e^{-‖f‖²/4} P` for `P = ∫ e^{-‖z‖²/4} W z dz`; `P₀ = (2π)^{-d} P` is an orthogonal projection |
| Theorem 7.31(ii), p. 89 | `exists_gaussAvg_ne_zero` (`GaussAvg`) | `P ≠ 0` on a nonzero space, by Mathlib's Fourier inversion (`Continuous.fourierInv_fourier_eq`) |
| eq. (7.15), p. 93 | `inner_W_of_vnProj` | a unit vector of `ran P₀` has the Fock vacuum expectation `⟪g, W f g⟫ = e^{-‖f‖²/4}` |
| Theorem 7.32, p. 90; Dereziński Corollary 1, p. 12 | `exists_fockRep_of_irreducible`, `stone_von_neumann_irreducible` | an irreducible representation is a Fock representation, unitarily equivalent to `fockRepOf h` (the Schrödinger representation of the source is the Fock representation, by the repository's `fockUnitary_spec`) |
| Theorem 7.35, p. 94; Dereziński Theorem 4, p. 12 | `stone_von_neumann` (`StoneVN`) | (representation) `L²(X) ⊗ K` is the Hilbert sum `⊕ᵢ orbitSpan R gᵢ` over an orthonormal basis `(gᵢ)` of `ran P₀` (`K ≅ ℓ²(ι)`), each summand a Fock representation |
| Dereziński Theorem 4, p. 12: "irreducible iff `K = ℂ`" | `isIrreducible_iff_finrank_vnRange` | (convention) irreducibility as defined on p. 10; stated for `H ≠ {0}`. Source error: as printed, Theorem 4 fails at `H = {0}` (irreducible by the p. 10 definition, `K = {0}`) |

Representation (all statements): the reference representation is the repository's Fock representation `fockRepOf h`
(cyclic vacuum with `⟪Ω, W f Ω⟫ = e^{-‖f‖²/4}`, OP2), not the Schrödinger representation `e^{i(ηx + qD)}` on `L²(X)` of the
sources; the two are unitarily equivalent (Bargmann transform), which is not formalized here. Module layout: `CCRJoint`,
`GaussKernel`, `GaussAvg` (with the identity (7.14) and `P ≠ 0`), `StoneVN`, `TestsStoneVN`.
