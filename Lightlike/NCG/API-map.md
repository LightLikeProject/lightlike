# Noncommutative geometry: finite spectral triples

## Abstract (Alpha)

This API holds finite spectral triples: a finite-dimensional real star-algebra represented faithfully on a
finite-dimensional complex Hilbert space, with a self-adjoint Dirac operator. A real structure adds an antiunitary
involution with the order-zero and first-order conditions, and a grading adds a chirality operator; the signs are those
of KO-dimension zero. The two-point space is worked out as the first example.

## Content (Alpha)

A finite spectral triple is a faithful real-linear star-representation of a finite-dimensional real star-algebra on a
finite-dimensional complex Hilbert space together with a self-adjoint operator `D` {1} {2} [1]. A real structure is an
antiunitary involution `J` such that `J π(b) J` commutes with `π(a)` and with `[D, π(a)]`, and `DJ = JD`; a grading is a
self-adjoint involution commuting with `π` and `J` and anticommuting with `D` {1} {2} [1]. On the two-point space
`ℂ ⊕ ℂ` acting diagonally on `ℂ²` with `J` the complex conjugation, `J π(b) J = π(b̄)` and the first-order condition
holds exactly for diagonal `D`, so `D = σₓ` is rejected {2} [2].

For a family of central self-adjoint orthogonal projections `Pᵢ` of `A` with `∑ Pᵢ = 1` (for `A = ⊕ Mₙᵢ(K)` the units of
the summands), the operators `Eᵢⱼ = π(Pᵢ) J π(Pⱼ) J` are complete orthogonal idempotents, so `H` is the direct sum of the
vertices `Hᵢⱼ = Eᵢⱼ H` {2} [3]; `J` maps `Hᵢⱼ` into `Hⱼᵢ`, so `dim Hᵢⱼ = dim Hⱼᵢ` {2} {1} [3]; a grading maps each `Hᵢⱼ`
into itself {2} [3]; and the first-order condition gives `Eᵢⱼ D Eₖₗ = 0` unless `i = k` or `j = l`, so `D` joins only
vertices in the same row or column of the Krajewski diagram {2} {1} [3]. For `A = ⊕ Mₙᵢ(ℂ)` represented complex-linearly,
`Hᵢⱼ ≅ ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ` with `π(a)` the left multiplication by `aᵢ` and `J π(b*) J` the right multiplication by `bⱼ`,
and `dim Hᵢⱼ = nᵢ nⱼ rᵢⱼ` {2} {1} [4]. On the two-point space the off-diagonal vertex `H₀₁` is zero [5].

The multiplicity matrix `rᵢⱼ = dim Vᵢⱼ` of a real structure is symmetric {1} [6]. Conversely, for `A = ⊕ Mₙᵢ(ℂ)` and
every symmetric `r` with `∀ i, ∃ j, rᵢⱼ > 0`, the space `⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ` with `π(a)` block diagonal with blocks
`1 ⊗ aᵢ ⊗ 1`, `J ψ (i, j, ρ, α, β) = conj ψ (j, i, ρ, β, α)` and `D = 0` is a real finite spectral triple whose
multiplicity matrix is `r`, and symmetric signs `sᵢⱼ = ±1` give a grading {1} [7]. On the two-point data the
multiplicities are `r₀₀ = 1` and `r₀₁ = 0`, a non-symmetric matrix is the multiplicity matrix of no real structure, and
on `ℂ ⊕ ℂ` every first-order `D` has `E₀₀ D E₁₁ = 0` [8].

An antiunitary involution of a finite-dimensional complex inner product space has an orthonormal basis of fixed vectors,
an orthonormal basis of its real form [9]. For `A = ⊕ Mₙᵢ(ℂ)` represented complex-linearly, every real structure is
unitarily equivalent to the model of its multiplicity matrix, by a unitary that intertwines `π` and `J`: the
coordinates `⟪bᵢⱼ ρ, π(Eᵢ,0α) J π(Eⱼ,0β) J x⟫` in orthonormal bases of the multiplicity spaces with `J bᵢⱼ ρ = bⱼᵢ ρ` {1}
[10]. The model is complex-linear, and its two-point instance is an example [11].

For a central partition and a chirality that is a scalar on each vertex `Hᵢⱼ`, the blocks `Eᵢⱼ D Eₖₗ` with `i ≠ k`
commute with the right action and those with `j ≠ l` with the left action, the diagonal blocks vanish, and
`D = Δ + J Δ J` with `Δ = ∑_{i ≠ k} Eᵢⱼ D Eₖₗ` hermitian, commuting with `J π(A) J` and anticommuting with the chirality;
such a `Δ` is unique {2} {1} [12]. With `D = 0`, `Δ = 0` [13].

For real summands: `q ↦ [[a + b i, c + d i], [-c + d i, a - b i]]` is an injective real `*`-homomorphism `ℍ → M₂(ℂ)`
whose complex span contains the matrix units [14], so a real-linear representation of `ℍ` extends to a complex-linear
representation of `M₂(ℂ)` that agrees with it on `ℍ` [15]. For a complex summand acting real-linearly,
`Q± = (1 ∓ i π(i·1))/2` split `H` into the fundamental part, where `π` is complex-linear, and the conjugate part, where
it is antilinear, and `J Q± J = (1 ± i J π(i·1) J)/2` are the corresponding parts for the right action, commuting with
`π(A)` {1} [16].

A complexification of a triple over a real algebra `A` is a faithful complex-linear `*`-representation `σ` of
`⊕ M_dₖ(ℂ)` with a real `*`-homomorphism `φ : A → ⊕ M_dₖ(ℂ)`, `π = σ ∘ φ` and every `σ(x)` a complex combination of
the `π(a)`: then `σ`, `D` and `J` form a complex-linear real finite spectral triple, and `H` is unitarily equivalent to the
model of its multiplicity matrix, by a unitary taking `π(a)` to the model's action of `φ(a)` and `J` to the model's `J`
{1} [17]. A complex-linear triple over `⊕ Mₙᵢ(ℂ)` is its own complexification [18]. For `A = ⊕ Mₙᵢ(ℝ)`,
`σ(x) = π(Re x) + i π(Im x)` is one [19]. A system of matrix units on `H` defines a complex `*`-representation of
`⊕ M_dₖ(ℂ)`, faithful when every block unit is nonzero [20].

## Lean References

1. Lightlike/NCG/FiniteSpectralTriple.lean - `NCG.FiniteSpectralTriple`, `NCG.FiniteSpectralTriple.comm`,
   `NCG.RealStructure`, `NCG.Grading`
2. Lightlike/NCG/TestsTwoPoint.lean - `NCG.TwoPoint.pi2`, `NCG.TwoPoint.conjJ`, `NCG.TwoPoint.conjJ_pi2_conjJ`,
   `NCG.TwoPoint.twoPoint`, `NCG.TwoPoint.firstOrder_iff`, `NCG.TwoPoint.not_firstOrder_sigmaX`
3. Lightlike/NCG/Bimodule.lean - `NCG.CentralPartition`, `NCG.rightOp`, `NCG.leftP`, `NCG.rightP`, `NCG.proj`,
   `NCG.Hsub`, `NCG.completeOrthogonalIdempotents_proj`, `NCG.J_mem_Hsub`, `NCG.finrank_Hsub_symm`,
   `NCG.grading_mem_Hsub`, `NCG.proj_D_proj_eq_zero`
4. Lightlike/NCG/TensorForm.lean - `NCG.MatSum`, `NCG.stdPartition`, `NCG.unit`, `NCG.Vsub`, `NCG.tensorEquiv`,
   `NCG.IsComplexLinear`, `NCG.tensorEquiv_pi`, `NCG.tensorEquiv_rightOp_star`, `NCG.finrank_Hsub_eq`
5. Lightlike/NCG/TestsBimodule.lean - `NCG.TwoPoint.twoPointReal`, `NCG.TwoPoint.twoPointPartition`,
   `NCG.TwoPoint.Hsub_zero_one`
6. Lightlike/NCG/Classification.lean - `NCG.multiplicity`, `NCG.multiplicity_symm`
7. Lightlike/NCG/KrajewskiModel.lean - `NCG.KIdx`, `NCG.HK`, `NCG.blockHom`, `NCG.piK`, `NCG.piK_injective`,
   `NCG.swapIdx`, `NCG.JK`, `NCG.krajewskiTriple`, `NCG.krajewskiReal`, `NCG.gammaK`, `NCG.krajewskiGrading`,
   `NCG.Vsub_krajewski`, `NCG.multiplicity_krajewskiReal`
8. Lightlike/NCG/TestsClassification.lean - `NCG.TestsClassification.twoPointR`,
   `NCG.TestsClassification.krajewski_twoPoint_diag`, `NCG.TestsClassification.krajewski_twoPoint_off`,
   `NCG.TestsClassification.not_multiplicity_eq_of_not_symm`, `NCG.TestsClassification.twoPoint_link_eq_zero`
9. Lightlike/NCG/RealForm.lean - `NCG.fixedSub`, `NCG.inner_re_of_mem_fixedSub`, `NCG.fixed_add_I_mul_fixed`,
   `NCG.fixed_inter_I_fixed`, `NCG.finrank_fixedSub`, `NCG.exists_orthonormalBasis_fixed`
10. Lightlike/NCG/Uniqueness.lean - `NCG.inner_lU_left`, `NCG.inner_rU_left`, `NCG.sum_inner_coord`,
    `NCG.J_mem_Vsub`, `NCG.coordU`, `NCG.coordIso`, `NCG.coordU_pi`, `NCG.coordU_J`, `NCG.exists_compatible_bases`,
    `NCG.coordIso_surjective`, `NCG.exists_unitary_krajewski`
11. Lightlike/NCG/TestsUniqueness.lean - `NCG.TestsUniqueness.isComplexLinear_krajewski`,
    `NCG.TestsUniqueness.twoPoint_unique`
12. Lightlike/NCG/DiracDecomposition.lean - `NCG.proj_D_proj_rightOp`, `NCG.proj_D_proj_pi`, `NCG.proj_D_proj_diag`,
    `NCG.Delta`, `NCG.D_eq_Delta_add`, `NCG.Delta_rightOp`, `NCG.Delta_gamma`, `NCG.Delta_symm`, `NCG.Delta_unique`
13. Lightlike/NCG/TestsDiracDecomposition.lean - `NCG.TestsDiracDecomposition.Delta_of_D_eq_zero`,
    `NCG.TestsDiracDecomposition.twoPoint_Delta`
14. Lightlike/NCG/QuaternionMatrix.lean - `NCG.quatToMat`, `NCG.quatToMat_apply`, `NCG.quatToMat_injective`, `NCG.qI`,
    `NCG.qJ`, `NCG.qK`, `NCG.single_eq_quat`
15. Lightlike/NCG/QuaternionComplexify.lean - `NCG.quatBasis`, `NCG.quatCoord`, `NCG.quat_decomp`,
    `NCG.quatCoord_quatToMat`, `NCG.quat_eq_sum`, `NCG.complexify`, `NCG.complexify_quatToMat`, `NCG.quatCoord_add`,
    `NCG.quatCoord_smul`, `NCG.complexifyL`, `NCG.complexify_mul`, `NCG.complexify_mul_of`, `NCG.complexify_sum`
16. Lightlike/NCG/ComplexSplitting.lean - `NCG.Qp`, `NCG.Qm`, `NCG.Qp_add_Qm`, `NCG.pi_u_sq`, `NCG.pi_u_Qp`, `NCG.pi_u_Qm`,
    `NCG.pi_comm_Qp`, `NCG.pi_comm_Qm`, `NCG.smul_eq_re_add_im`, `NCG.Qp_pi_smul`, `NCG.Qm_pi_smul`, `NCG.QpR`, `NCG.QmR`,
    `NCG.J_Qp_J`, `NCG.J_Qm_J`, `NCG.QpR_add_QmR`, `NCG.pi_comm_QpR`, `NCG.pi_comm_QmR`, `NCG.Qp_comm_QpR`,
    `NCG.Qp_comm_QmR`
17. Lightlike/NCG/Complexification.lean - `NCG.commJ_span`, `NCG.commL`, `NCG.commL_apply`, `NCG.Complexification`,
    `NCG.Complexification.σℝ`, `NCG.Complexification.σℝ_apply`, `NCG.Complexification.triple`,
    `NCG.Complexification.isComplexLinear`, `NCG.Complexification.realStructure`, `NCG.Complexification.exists_unitary`
18. Lightlike/NCG/TestsComplexification.lean - `NCG.TestsComplexification.piC`,
    `NCG.TestsComplexification.selfComplexification`, `NCG.TestsComplexification.exists_unitary_self`
19. Lightlike/NCG/RealSummands.lean - `NCG.MatSumR`, `NCG.reM`, `NCG.imM`, `NCG.ofRealM`, `NCG.reM_mul`, `NCG.imM_mul`,
    `NCG.reM_star`, `NCG.imM_star`, `NCG.phiR`, `NCG.pi_rsmul`, `NCG.sigmaR`, `NCG.sigmaR_apply`, `NCG.sigmaR_phiR`,
    `NCG.unitR`, `NCG.unitC`, `NCG.phiR_unitR`, `NCG.unitC_mul_mul_unitC`, `NCG.sigmaR_injective`,
    `NCG.realComplexification`, `NCG.exists_unitary_realSummands`
20. Lightlike/NCG/MatrixUnits.lean - `NCG.MatrixUnits`, `NCG.MatrixUnits.toFun`, `NCG.MatrixUnits.U_mul_toFun`,
    `NCG.MatrixUnits.toFun_mul_U`, `NCG.MatrixUnits.toFun_mul`, `NCG.MatrixUnits.toFun_star`, `NCG.MatrixUnits.hom`,
    `NCG.MatrixUnits.hom_apply`, `NCG.MatrixUnits.U_mul_hom_mul_U`, `NCG.MatrixUnits.hom_injective`,
    `NCG.MatrixUnits.U_diag_eq`, `NCG.MatrixUnits.U_ne_zero`, `NCG.MatrixUnits.hom_injective_of_block`,
    `NCG.MatrixUnits.hom_mem`

## References

1. T. Krajewski, *Classification of finite spectral triples*, J. Geom. Phys. 28 (1998) 1-30, arXiv:hep-th/9701081,
   Sections 2, 3.1, 3.2, 3.3 and 3.4.
2. M. Paschke and A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029, Section 2,
   Lemmas 1-4 and 6.
