# G1-050: second quantization in the Fock representation (Dereziński, Theorems 13 and 24)

Source read: J. Dereziński, arXiv:math-ph/0511030 (key `derezinski-2006`): Section 5.2, Theorem 13, p. 19 (`Γ(p)` on the full
Fock space, `Γ(p₂)Γ(p₁) = Γ(p₂p₁)`, `Γ(p)` unitary iff `p` is); Section 5.5, p. 21 (`Γ(p)` restricted to `Γₛ(Z)`, the second
quantization of `p`); Section 6.1, Theorem 21, p. 25 (the Fock representation `y ↦ W(y) = e^{iφ(y)}` on `Γₛ(Z)`); Section 6.4,
Theorem 24, p. 27 (Shale: an implementer `U W(y) U* = W(ry)` is unique up to a phase, `U_r^j` of (46) is the one with
`(Ω|U_r^j Ω) > 0`, (47); for a unitary `r` of `Z`, `p = r`, `c = d = 0` and `U_r^j = Γ(r)`).

| Source | Library | Check |
|---|---|---|
| Theorem 21, p. 25: the Fock representation | `FockRep h K` (the repository's characterization: a representation of the Weyl relations with a unit cyclic vector `Ω` and `⟪Ω, W f Ω⟫ = exp(-‖f‖²/4)`; unique up to unitary equivalence, `fockUnitary_spec`) | (representation) as in the repository's Fock files; `Y = Re(Z ⊕ Z̄)` is `h` with `σ = Im⟪·,·⟫` |
| §5.5, p. 21: `Γ(r)` on `Γₛ(Z)` for a unitary `r`, the unitary case | `FockRep.secondQuant R U`: the unitary with `Γ(U) Ω = Ω` and `Γ(U) W(f) = W(U f) Γ(U)` (`secondQuant_vacuum`, `secondQuant_W`), built from the uniqueness of the Fock representation applied to `f ↦ W(U f)` (`FockRep.precomp`) | (representation) `Γ(U)` is characterized by its action on the vectors `W f Ω` (`secondQuant_unique`), not by `U^{⊗n}` on the `n`-particle spaces, which are not built |
| §5.2, p. 19 and §5.5, p. 21: `Γ(p)` for `‖p‖ ≤ 1` on `Γₛ(Z)` | `FockRep.gamma R p`, the contraction with `Γ(p) W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω` (`gamma_W_Ω`), i.e. `Γ(p) e(f) = e(p f)` on the exponential vectors `e(f) = e^{‖f‖²/4} W(f) Ω`; `norm_gamma_le` (`‖Γ(p)‖ ≤ 1`) | (representation) `Γ(p)` is characterized by its action on the exponential vectors, not by `p^{⊗n}` on the `n`-particle spaces, which are not built; proof: the kernel `exp(⟪f, g⟫/2) - exp(⟪p f, p g⟫/2)` is positive semidefinite (`posSemidef_kernel`, by the Schur product theorem and the exponential series), so `Γ(p)` is a contraction on the span of the `W f Ω`, extended by density |
| Theorem 13, p. 19: `Γ(p₂)Γ(p₁) = Γ(p₂p₁)`; `Γ(p)` bounded iff `‖p‖ ≤ 1`; `Γ(p)` unitary iff `p` is | `gamma_comp` (`Γ(q) Γ(p) = Γ(q p)`), `gamma_one`, `adjoint_gamma` (`Γ(p)* = Γ(p*)`), `gamma_unitary` (`Γ(U) = secondQuant U` for a unitary `U`); for unitaries also `secondQuant_refl`, `secondQuant_trans`, `secondQuant_symm` | for contractions `‖p‖ ≤ 1` |
| Theorem 13, (35), p. 19: `Γ(e^{ih}) = exp(dΓ(ih))`, for self-adjoint `h` | `FockRep.secondQuantGroup R U` (`t ↦ Γ(U(t))` for a strongly continuous unitary group `U(t) = e^{ith}` of `h`, a strongly continuous unitary group of the Fock space), `FockRep.dGamma R U` its generator, `isSelfAdjoint_dGamma` | (representation) `dΓ(h)` is defined as the self-adjoint generator of `t ↦ Γ(e^{ith})` (Stone), so (35) holds by construction; the formula `dΓ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` on the `n`-particle spaces is not stated |
| Theorem 24, (45), p. 27, for a unitary `r`: `U W(y) U* = W(ry)` | `secondQuant_conj` | matches |
| Theorem 24 (2), p. 27, for a unitary `r`: unique up to a phase, and the one with `(Ω|U Ω) > 0` is `U_r^j = Γ(r)` | `eq_smul_secondQuant` (every implementer is `c Γ(U)`, `|c| = 1`, from the triviality of the commutant, `commutant_scalar`), `eq_secondQuant_of_pos` | matches, for unitary `r` (the general `r ∈ Sp₂(Y)` is Shale's theorem, in the repository's Shale files) |

Not stated (open): `Γ(p)` for unbounded closed `p`; `[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])` (Theorem 13); the Weyl C*-algebra of a
symplectic space as an abstract C*-algebra.
