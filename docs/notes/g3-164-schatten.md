# G3-164 (Schatten norms): the Schatten classes, `J₁` and `J₂`

Source read: G. Teschl, *Mathematical Methods in Quantum Mechanics, With Applications to Schrödinger Operators*, Graduate
Studies in Mathematics 99, American Mathematical Society (2009), online edition (source key `teschl-2009`), Section 6.3:
Lemma 6.10 (p. 140), (6.19)-(6.23) and Lemma 6.12 with its proof (pp. 141-142), the identification of `J₁`, `J₂` (p. 142)
and Lemma 6.13 with (6.24) (pp. 142-143).

| Source | Library | Check |
|---|---|---|
| (6.19)-(6.20): `‖K‖_p = (∑ⱼ sⱼ(K)^p)^{1/p}`, `J_p = {K ∈ C(H) \| ‖K‖_p < ∞}` | `schattenSum p K` (the supremum (6.23), in `ℝ≥0∞`), `schattenSum_eq_tsum` (it equals `∑ⱼ sⱼ^p` for every canonical form, `p ≥ 1`); `J_p` is `IsCompactOperator K ∧ schattenSum p K < ⊤` | (representation) the norm is defined by (6.23) and shown equal to (6.19); the sum does not depend on the canonical form; values in `ℝ≥0∞` |
| (6.23): `‖K‖_p = sup {(∑ⱼ \|⟪ψⱼ, Kϕⱼ⟫\|^p)^{1/p} \| {ψⱼ}, {ϕⱼ} ONS}` | `schattenSum_le_tsum` (the source's Hölder and Cauchy-Schwarz argument, `schatten_core`), `tsum_le_schattenSum` | (representation) the supremum is over finite orthonormal families (the same supremum) |
| (6.21) `‖K‖ ≤ ‖K‖_p`, (6.22) `‖K‖_p = ‖K*‖_p` | `norm_rpow_le_schattenSum`, `ofReal_norm_le_schattenNorm`, `schattenSum_adjoint` | matches |
| Lemma 6.12: `J_p` with `‖.‖_p` is a Banach space | `schattenNorm_add_le`, `schattenSum_smul`, `schattenNorm_eq_zero_iff`, `schattenSum_le_of_tendsto`, `exists_tendsto_schattenNorm` | (representation) the norm axioms and completeness are stated; no normed-space instance on `J_p` is built |
| Lemma 6.10, p. 140 and p. 142: `J₂` is the Hilbert-Schmidt class, `∑ₙ ‖Kψₙ‖² = ‖K‖₂²` for every ONB | `tsum_norm_sq_apply_eq`, `schattenSum_two_eq_tsum_norm_sq`, `isHilbertSchmidt_iff` (the repository's `IsHilbertSchmidt`) | matches |
| p. 142, Lemma 6.13, (6.24): `J₁` is the trace class, `‖K₁K₂‖₁ ≤ ‖K₁‖₂‖K₂‖₂` | `isTraceClass_iff` (the repository's `IsTraceClass`), `schattenSum_one_mul_le` | (representation) (6.24) with `‖K₁*‖₂`, equal to `‖K₁‖₂` |

Tests (`Spectral/TestsSchatten.lean`): `diag(1/(n+1))` on `ℓ²(ℕ)` is in `J₂` and not in `J₁`; `‖0‖_p = 0`.

With the spectral theorem for compact self-adjoint operators and the canonical form (the two previous entries), this
completes row G3-164 ("Compact and trace-class operators, Hilbert-Schmidt, Schatten norms").
