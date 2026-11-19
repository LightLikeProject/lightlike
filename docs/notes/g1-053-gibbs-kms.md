# G1-053: the KMS condition for the Gibbs state in infinite dimension

Source read: J. Panangaden, *Energy Full Counting Statistics and Return to Equilibrium*, master's thesis, McGill
University (2021), arXiv:2110.01678 (source key `panangaden-2021`), Section 5.2: Proposition 5.4 with its proof and the
remark after it (p. 43), Remark 5.1, Definitions 5.5 and 5.8 (pp. 44-46), Proposition 5.9 (p. 47). For the eigenbasis:
G. Teschl, *Mathematical Methods in Quantum Mechanics*, Theorem 6.6, p. 136 (read).

| Source | Library | Check |
|---|---|---|
| p. 43: `τᵗ(A) = e^{itH} A e^{-itH}`; the Gibbs state `ω_β(A) = tr(e^{-βH} A)/tr(e^{-βH})`, existing when `e^{-βH}` is trace class | `evol`, `dyn`, `gibbs`, for `H x = ∑ₙ λₙ ⟪bₙ, x⟫ bₙ` with `∑ e^{-βλₙ} < ∞` | (representation) `H` is the self-adjoint operator of a Hilbert basis `b` and real eigenvalues `λ` on its natural domain `{x \| ∑ λₙ² \|⟪bₙ, x⟫\|² < ∞}`; every self-adjoint `H` with a trace-class `e^{-βH}` has this form, since `e^{-βH}` is then compact and self-adjoint and has a Hilbert basis of eigenvectors (Teschl, Theorem 6.6, p. 136); `e^{itH} = diag(e^{itλₙ})`, and `tr(e^{-βH} A)` is the diagonal sum in the eigenbasis |
| the Gibbs state is a state | `gibbs_one`, `gibbs_star_mul_self_nonneg` | matches |
| (invariance, used throughout) `ω(τᵗ(A)) = ω(A)` | `gibbs_dyn` | matches |
| Remark 5.1, Proposition 5.9, p. 47: `F_{A,B}` bounded and continuous on `0 ≤ Im z ≤ β`, analytic inside, `F_{A,B}(t) = ω(A τᵗ(B))`, `F_{A,B}(t + iβ) = ω(τᵗ(B) A)` | `kmsFun` (the double series of `ω(A τᶻ(B))`), `norm_kmsFun_le`, `continuousOn_kmsFun`, `differentiableOn_kmsFun`, `kmsFun_ofReal`, `kmsFun_add_I_mul` | matches, for the Gibbs state (Proposition 5.4: Gibbs ⇒ KMS "as long as the Gibbs state exists") |

Not stated: the converse (a KMS state is the Gibbs state, Proposition 5.4 in finite dimensions, which is on main as
`isKMS_iff_eq_gibbs`), the general C*-dynamical setting of Definition 5.8, Haag-Hugenholtz-Winnink.

Tests (`TestsGibbsKMS.lean`): the oscillator `λₙ = n` on `ℓ²(ℕ)` at every `β > 0`; at `β = 0` the partition sum
diverges.
