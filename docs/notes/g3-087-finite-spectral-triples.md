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

## FST3: the multiplicity matrix and its realization

* `multiplicity_symm` (Krajewski §3.2, p. 12): `rᵢⱼ = dim Vᵢⱼ` is symmetric, from `dim Hᵢⱼ = dim Hⱼᵢ` (Lemma 4) and
  `dim Hᵢⱼ = nᵢ nⱼ rᵢⱼ` (Lemma 2).
* `krajewskiTriple`, `krajewskiReal`, `krajewskiGrading`, `multiplicity_krajewskiReal` (Krajewski §3.2, p. 13 and §3.3,
  p. 13): for `A = ⊕ Mₙᵢ(ℂ)` and a symmetric `r` in which every summand acts on some vertex, `H = ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ`
  (`EuclideanSpace` over `Σ (i, j), Fin rᵢⱼ × Fin nᵢ × Fin nⱼ`), `π(a)` block diagonal with blocks `1 ⊗ aᵢ ⊗ 1`
  (`Matrix.blockDiagonal'` and the Kronecker product, so the star-homomorphism property is Mathlib's), `J` the conjugate
  swap `(i, j, ρ, α, β) ↦ (j, i, ρ, β, α)` and `D = 0` form a real finite spectral triple; symmetric signs `sᵢⱼ = ±1` give
  a grading; and the multiplicity matrix of this triple is `r` (`Vᵢⱼ` is spanned by the basis vectors at
  `(i, j, ρ, 0, 0)`). So a matrix is the multiplicity matrix of a real structure exactly when it is symmetric.

Not yet stated: Krajewski's real summands `Mₙ(ℝ)`, `Mₙ(ℍ)` in the tensor form and the model (see below).

Tests (`TestsClassification.lean`): the two-point data have `r₀₀ = 1`, `r₀₁ = 0`; a non-symmetric matrix is the
multiplicity matrix of no real structure; on `ℂ ⊕ ℂ` every first-order `D` has `E₀₀ D E₁₁ = 0`.

## FST3c: uniqueness up to unitary equivalence (Krajewski §3.2, p. 13)

* `exists_orthonormalBasis_fixed` (`RealForm.lean`): an antiunitary involution has an orthonormal basis of fixed vectors
  (`V = V_ℝ ⊕ i V_ℝ`, `dim_ℝ V_ℝ = dim_ℂ V`, the inner product is real on `V_ℝ`). This is the source's choice of a basis
  with `Lᵢᵢ ψᵖ = ψᵖ` after removing the phases.
* `exists_compatible_bases`: orthonormal bases `bᵢⱼ` of the multiplicity spaces `Vᵢⱼ` with `J bᵢⱼ ρ = bⱼᵢ ρ` (for `i ≠ j`
  one side is chosen freely and the other is its `J`-transport; for `i = j` the fixed basis).
* `coordIso`, `coordIso_surjective`, `exists_unitary_krajewski`: the coordinates `⟪bᵢⱼ ρ, π(Eᵢ,0α) J π(Eⱼ,0β) J x⟫` are a
  unitary `H ≃ ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ` with `U π(a) = π_model(a) U` and `U J = J_model U`: every complex-linear real structure
  is unitarily equivalent to `krajewskiReal` of its multiplicity matrix.

## Real summands `Mₙ(ℝ)`, `Mₙ(ℍ)` (Krajewski §2, p. 2; §3.1, p. 10; Table 1, p. 14): two attempts

The definitions (`FiniteSpectralTriple`, `RealStructure`, `Grading`) and FST2a (`Bimodule.lean`: Lemmas 1, 3, 4, 6) take
a real `*`-algebra and a real-linear `π`, so they cover real summands. The tensor form, the model and uniqueness are
stated for `⊕ Mₙᵢ(ℂ)` acting complex-linearly.

Attempt 1, complexification. A real-linear `π` extends to `A_ℂ = A ⊗_ℝ ℂ` by `π_ℂ(a ⊗ c) = c π(a)`. The order-zero and
first-order conditions carry over, since `J π_ℂ(∑ aₖ ⊗ cₖ) J = ∑ c̄ₖ J π(aₖ) J`. For `Mₙ(ℝ)`, `Mₙ(ℝ) ⊗ ℂ = Mₙ(ℂ)`, and
the complex results apply with the same `H` and `J`. The attempt stops at the other two summand types:
* `Mₙ(ℍ) ⊗_ℝ ℂ ≅ M₂ₙ(ℂ)` needs a `*`-isomorphism `ℍ ⊗_ℝ ℂ ≃ M₂(ℂ)`. Mathlib has the quaternion algebra but not this
  isomorphism.
* `Mₙ(ℂ)` as a real algebra has `Mₙ(ℂ) ⊗_ℝ ℂ ≅ Mₙ(ℂ) ⊕ Mₙ(ℂ)` (`z ⊗ w ↦ (z w, z̄ w)`): the fundamental and the conjugate
  representation. The summands of `A_ℂ` are then not indexed by those of `A`, and `J` pairs the fundamental block of one
  summand with the conjugate block of another. Stating the result on `A`'s index set needs the bookkeeping of
  Krajewski's Table 1 (`μ_{iαj}`, `μ_{iᾱj}`). Neither the `*`-isomorphism nor the transport of multiplicity matrices is
  constructed.

Attempt 2, real matrix units. `Mₙ(ℝ)` and `Mₙ(ℍ)` contain the real matrix units `E_{αβ}`, and the tensor-form
argument of `TensorForm.lean` uses only their relations and `∑ E_{αα} = Pᵢ`. It needs complex linearity only for the
left-action formula, and that formula holds for real coefficients. This gives `Hᵢⱼ ≅ (Fin nᵢ → Fin nⱼ → Vᵢⱼ)` with
`Vᵢⱼ = E₀₀ H E₀₀` as before. The attempt stops at the multiplicity space. For a quaternionic summand,
`E₀₀ Mₙ(ℍ) E₀₀ = ℍ` still acts on `Vᵢⱼ`, so `Vᵢⱼ` is an `ℍ`-module (or an `ℍ ⊗ ℍᵒᵖ`-module for two quaternionic
summands). Its complex dimension alone no longer fixes the bimodule. The missing step is the classification of these
modules together with `J`: a basis `(v, j v)` for an antilinear `j` with `j² = -1`, the analogue of `RealForm.lean`,
and the sign relation between `J` and `j` that gives Table 1's conditions.

So the uniqueness and the model are stated for complex summands (`A = ⊕ Mₙᵢ(ℂ)` acting complex-linearly). Both
attempts above stop at a missing piece of algebra, not at length.

Attempt 3, the two missing pieces of attempt 1, built. New compared with attempts 1 and 2:
* `QuaternionMatrix.lean`: `quatToMat : ℍ →⋆ₐ[ℝ] M₂(ℂ)`, `q ↦ [[a + b i, c + d i], [-c + d i, a - b i]]`, injective,
  with the four matrix units as explicit complex combinations of `ι(1), ι(i), ι(j), ι(k)` (`single_eq_quat`). This is the
  `*`-isomorphism `ℍ ⊗_ℝ ℂ ≅ M₂(ℂ)` where attempt 1 stopped.
* `QuaternionComplexify.lean`: the coordinates `quatCoord M` of `M ∈ M₂(ℂ)` in that basis (`quat_decomp`), and for a
  real-linear `ρ : ℍ → End(H)` its complexification `ρ_ℂ(M) = ∑ₖ quatCoord M k • ρ(bₖ)`, with `ρ_ℂ ∘ ι = ρ`, complex-linear
  (`complexifyL`) and multiplicative for multiplicative `ρ` (`complexify_mul`). A quaternionic `π` thus gives a complex
  representation of `M₂(ℂ)`, and so complex matrix units on `H`.
* `ComplexSplitting.lean`: for a complex summand acting real-linearly, `Q± = (1 ∓ i π(i·1))/2` are complementary
  idempotents commuting with `π(A)`, `π(i·1) = ±i` on `Q± H`, `π` complex-linear on `Q₊ H` (`Qp_pi_smul`) and antilinear
  on `Q₋ H` (`Qm_pi_smul`). This is `Mₙ(ℂ) ⊗_ℝ ℂ ≅ Mₙ(ℂ) ⊕ Mₙ(ℂ)` in representation form, the second stop of attempt 1.

Where each Krajewski clause stands:
* §2, p. 2, `A = ⊕ Mₙᵢ(K)` with `K = ℝ, ℂ, ℍ` and a real-linear `π`: the definitions and FST2a cover it (proved).
* §3.1, p. 10, "`Mₙ(ℝ)` and `Mₙ(ℍ)` have only one irreducible representation ... `Mₙ(ℂ)` has two ... the fundamental one
  and its complex conjugate": the split of a complex summand into its fundamental and conjugate parts is proved
  (`ComplexSplitting.lean`). The complex matrix units of a quaternionic summand are proved in the single-summand form
  (`QuaternionComplexify.lean`). Open: assembling the matrix units of all summands' irreducible representations on `H`
  and running the tensor-form argument over them, which gives `H_{(iα)(jβ)} ≅ ℂ^{nᵢ} ⊗ ℂ^{r} ⊗ ℂ^{nⱼ}` with `nᵢ` the
  dimension of the irreducible representation (`2n` for `Mₙ(ℍ)`).
* The assembly (`Complexification.lean`): a complexification of a triple over a real algebra `A` is a faithful
  complex-linear `*`-representation `σ` of `⊕ M_dₖ(ℂ)` with a real `*`-homomorphism `φ : A → ⊕ M_dₖ(ℂ)`, `π = σ ∘ φ` and
  every `σ(x)` a complex combination of the `π(a)`. The order-zero and first-order conditions pass to `σ` (`commJ_span`),
  and `Complexification.exists_unitary` gives the unitary onto the model of the complexified multiplicity matrix,
  intertwining `π` with the model's action of `φ(A)` and `J` with the model's `J`. So each summand type reduces to
  constructing `σ`. `MatrixUnits.lean` builds `σ` from a system of matrix units on `H`, faithful when every block unit is
  nonzero.
* `Mₙ(ℝ)` (`RealSummands.lean`): `σ(x) = π(Re x) + i π(Im x)`, faithful by `E₀α x Eβ₀ = x_αβ E₀₀`;
  `exists_unitary_realSummands` is the classification for `A = ⊕ Mₙᵢ(ℝ)` (proved).
* `Mₙ(ℍ)` (open, next): the units `U_{(αs)(βt)} = ∑ₖ quatCoord(E_st)ₖ π(E_αβ(bₖ))` of `M₂ₙ(ℂ)`. Their relations follow
  from `complexify_mul` in the bimodule form `ρ₁(p) ρ₂(q) = ρ₃(pq)`, and the block unit is `π(1ᵢ) ≠ 0`.
* `Mₙ(ℂ)` (open, next): the units `Q₊ π(E_αβ)` (fundamental) and `Q₋ π(E_αβ)` (conjugate), with
  `φ(a) = (a, ā)`, over the blocks whose unit `Q± π(1ᵢ)` is nonzero.
* §3.3, p. 14, Table 1 (a symmetric integer matrix over the irreducible representations, the signs `μ_{iαj} μ_{iᾱj} ≥ 0`,
  and the factors 2 and 4 relating it to the intersection form): open. It needs `J Q₊ J`, the right-action projection,
  and the exchange by `J` of the fundamental and conjugate blocks of a complex summand.

## FST4: the Dirac operator `D = Δ + J Δ J` (Krajewski §3.4, p. 15)

Read: Krajewski §3.4, p. 14 (first-order operators, `L_L(M) + L_R(M) ⊂ L_1(M)`) and p. 15 (`D = D_L + D_R` with
`[D_L, π(A)] = [D_R, J π(A) J⁻¹] = 0`; unique since `D` anticommutes with `χ`; `D_L = J D_R J⁻¹`; `D = Δ + J Δ J⁻¹` with `Δ`
hermitian, commuting with `J π(A) J⁻¹` and anticommuting with `χ`); Conclusion, p. 17. Paschke-Sitarz Lemma 6, p. 5,
second half.

* `proj_D_proj_rightOp` (`i ≠ k`), `proj_D_proj_pi` (`j ≠ l`): Lemma 6, second half.
* `proj_D_proj_diag`: the diagonal blocks `Eᵢⱼ D Eᵢⱼ` vanish for a chirality that is a scalar on `Hᵢⱼ`.
* `Delta = ∑_{i ≠ k} Eᵢⱼ D Eₖₗ`, `D_eq_Delta_add`, `Delta_rightOp`, `Delta_gamma`, `Delta_symm`, `Delta_unique`.

The chirality is assumed to be a scalar on each vertex (`hγ`). Paschke-Sitarz, Lemma 3, p. 3 (read), second half,
derives this from the axiom that `γ` is the image of a Hochschild cycle: "Γᵢⱼ must be proportional to the identity
matrix, so it leaves only the possibility for +1 or −1". So every triple satisfying the source's axioms satisfies `hγ`.
