# G3-087: finite spectral triples

Sources (read; arXiv v1 PDF pages):

* T. Krajewski, *Classification of finite spectral triples*, arXiv:hep-th/9701081 (source key `krajewski-1998`).
* M. Paschke, A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029 (source key
  `paschke-sitarz-1998`).

| Source location | Statement | Lean |
|---|---|---|
| Krajewski §2, p. 2 | a finite spectral triple: `A`, `H` finite-dimensional, `π` faithful, `A = ⊕ Mₙᵢ(K)`, `K = ℝ, ℂ, ℍ` | `FiniteSpectralTriple` (real `*`-algebra, real-linear `π`) |
| Krajewski §2.1, p. 3 | Reality (finite case): `J* = J⁻¹ = J`, `[π(x), J π(y) J⁻¹] = 0` | `RealStructure.inner_J`, `J_J`, `order_zero` |
| Krajewski §2.4, p. 9 | first order condition `[[D, π(x)], J π(y) J⁻¹] = 0` | `RealStructure.first_order` |
| Paschke-Sitarz §2, p. 2 | `J` antilinear isometry, `J² = 1`, `π⁰ = J π* J` commutes with `π`; grading `γ* = γ`, `γ² = 1`, `Jγ = γJ`, `γπ(a) = π(a)γ` | `RealStructure`, `Grading` |
| Paschke-Sitarz §2, p. 5 | `D` self-adjoint, `DJ = JD`, `Dγ = -γD`, (2) | `RealStructure.D_J`, `Grading.D_γ` |
| Paschke-Sitarz Lemma 1, p. 2 | `H = ⊕ Hᵢⱼ`, `Hᵢⱼ = Pᵢ H Pⱼ` | FST2 |
| Paschke-Sitarz Lemma 2, pp. 2-3 | `Hᵢⱼ = ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ` | FST2 |
| Paschke-Sitarz Lemma 3, p. 3 | `γ` preserves `Hᵢⱼ` (and is `±1` there, by the Hochschild-cocycle axiom) | FST2 (first half) |
| Paschke-Sitarz Lemma 4, p. 3 | `J Hᵢⱼ = Hⱼᵢ`, `rᵢⱼ = rⱼᵢ` | FST2 |
| Paschke-Sitarz Lemma 6, p. 5 | `Dᵢⱼ,ₖₗ = 0` unless `i = k` or `j = l` | FST2 |
| Krajewski §3.2, Conclusion, p. 13 | a real structure exists iff the multiplicity matrix is symmetric | FST3 |
| Krajewski §3.3-3.4, Conclusions, pp. 14, 17 | the triple is given by a symmetric multiplicity matrix, the chirality signs and `D` | FST3 |

The KO-dimension is `0` (`J² = 1`, `JD = DJ`, `Jγ = γJ`), the signs of the finite case in both sources; the sign table
for the other KO-dimensions is G3-084.

FST1 (this piece): the definitions, and the two-point space `ℂ ⊕ ℂ` on `ℂ²` with `J` the complex conjugation, where the
first-order condition holds iff `D` is diagonal (`firstOrder_iff`), so `D = σₓ` is rejected (`not_firstOrder_sigmaX`).
Here `Hᵢⱼ = 0` for `i ≠ j`, and this is the instance `H = H₀₀ ⊕ H₁₁` of Paschke-Sitarz, Lemma 6.

Reused: Mathlib's `StarAlgHom`, `Matrix.toEuclideanCLM` (`M₂(ℂ) ≃⋆ₐ End(ℂ²)`), the adjoint star on `H →L[ℂ] H`,
`Matrix.diagonalAlgHom`. Mathlib and Physlib have no spectral triples.

## FST2: the bimodule `H = ⊕ Hᵢⱼ` and the links of `D`

Statement draft (each against its read location):

* `completeOrthogonalIdempotents_proj` (Paschke-Sitarz, Lemma 1, p. 2): for a central partition `Pᵢ` of `A`,
  `Eᵢⱼ = π(Pᵢ) J π(Pⱼ) J` are complete orthogonal idempotents of `End(H)`, so `H = ⊕ᵢⱼ Hᵢⱼ` with `Hᵢⱼ = range Eᵢⱼ`.
* `J_mem_Hsub`, `finrank_Hsub_symm` (Paschke-Sitarz, Lemma 4, p. 3; Krajewski §3.2, p. 12): `J Hᵢⱼ ⊆ Hⱼᵢ` and
  `dim Hᵢⱼ = dim Hⱼᵢ`.
* `grading_mem_Hsub` (Paschke-Sitarz, Lemma 3, p. 3, first half): `γ Hᵢⱼ ⊆ Hᵢⱼ`. The second half (`γ = ±1` on `Hᵢⱼ`) uses
  the axiom that `γ` is the image of a Hochschild cycle and is not stated.
* `proj_D_proj_eq_zero` (Paschke-Sitarz, Lemma 6, p. 5): `i ≠ k → j ≠ l → Eᵢⱼ D Eₖₗ = 0`.
* `tensorEquiv`, `tensorEquiv_pi`, `tensorEquiv_rightOp_star`, `finrank_Hsub_eq` (Paschke-Sitarz, Lemma 2, pp. 2-3;
  Krajewski §3.1, p. 10): for `A = ⊕ Mₙᵢ(ℂ)` with `π` complex-linear, `Hᵢⱼ ≃ (Fin nᵢ → Fin nⱼ → Vᵢⱼ)`,
  `x ↦ (π(Eᵢ,0α) J π(Eⱼ,0β) J x)_{αβ}`, with `Vᵢⱼ = π(Eᵢ,00) J π(Eⱼ,00) J H` of dimension `rᵢⱼ`; `π(a)` acts as the
  left multiplication by `aᵢ` and `J π(b*) J` as the right multiplication by `bⱼ`; `dim Hᵢⱼ = nᵢ nⱼ rᵢⱼ`. The proof
  uses the matrix units of the summands directly (the content of Mathlib's Morita equivalence
  `toModuleCatFromModuleCatLinearEquiv`, applied once on each side).

The lemmas other than the tensor form hold for any finite-dimensional real `*`-algebra with a central partition (real
summands `Mₙ(ℝ)`, `Mₙ(ℍ)` included); the tensor form is stated for complex summands acting complex-linearly.

Test (`TestsBimodule.lean`): the two-point space with `J` the complex conjugation is a real structure, and its
off-diagonal vertex `H₀₁` is zero.
