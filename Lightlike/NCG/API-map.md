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

For `A = ⊕ Mₙᵢ(ℍ)`, the operators `U_{(αs)(βt)} = (ρ_αβ)_ℂ(E_st)`, with `ρ_αβ(q) = π(E_αβ(q))`, are a system of matrix
units of `⊕ M₂ₙᵢ(ℂ)` on `H` with block units `π(1ᵢ)`, and with `φ(a)_{(αs)(βt)} = ι(a_αβ)_st` they form a
complexification: a real finite spectral triple over `⊕ Mₙᵢ(ℍ)` is unitarily equivalent to the model
`⊕ ℂ^{2nᵢ} ⊗ ℂ^{rᵢⱼ} ⊗ ℂ^{2nⱼ}` {1} [21].

For `A = ⊕ Mₙᵢ(ℂ)` acting real-linearly, `Q± = (1 ∓ i π(i·1))/2` are complementary orthogonal projections commuting with
`π`, the operators `Q± π(E^i_{αβ})` of the blocks `(i, ±)` with `Q± π(1ᵢ) ≠ 0` are a system of matrix units, and with
`φ(a) = (aᵢ, āᵢ)` they form a complexification: such a triple is unitarily equivalent to the model of the multiplicity
matrix over the fundamental and conjugate representations that occur {1} [22].

Partial systems of matrix units, without `∑ U = 1`, combine over sums of index types [23]. For a mixed algebra
`⊕ Mₙ(ℝ) × ⊕ Mₙ(ℂ) × ⊕ Mₙ(ℍ)` the restrictions `ψ₁, ψ₂, ψ₃` of `π` to the factors give partial systems: `ψ₁(E^i_{αβ})`,
`ψ±(E^i_{αβ})` with the complex-linear and antilinear parts `ψ±(Y) = ½(ψ₂(Y) ∓ i ψ₂(iY))`, and the quaternionic units of
`ψ₃`. They multiply to `0` across factors and their block units add to `1`, so every real finite spectral triple over a
mixed algebra is unitarily equivalent to the model of the multiplicity matrix over the irreducible representations that
occur {1} [24].

For a complex-linear triple over `⊕ Mₙᵢ(ℂ)` and an orientable grading `γ = ∑_p π(x_p) J π(y_p) J`, `γ` acts on each
multiplicity space `Vᵢⱼ` as the scalar `cᵢⱼ = ∑_p (x_p)ᵢ₀₀ conj((y_p)ⱼ₀₀)`, the same at every diagonal corner; on a
nonzero vertex `cᵢⱼ = ±1` and `cⱼᵢ = cᵢⱼ`, and `Tr(γ π(E^i_αα) J π(E^j_ββ) J) = cᵢⱼ rᵢⱼ`, the intersection form of the
complex case {1} [25].

A grading of a real triple is a grading of its complexification, and an orientable one
`γ = ∑_p π(x_p) J π(y_p) J` stays orientable with `X_p = φ(x_p)`, `Y_p = φ(y_p)`. For a mixed algebra the signed
multiplicities `μ_kl = c_kl r_kl` of the complexified model are symmetric, and satisfy the sign conditions of
Krajewski's Table 1: `μ_{iαj} μ_{iᾱj} ≥ 0` for a complex summand `i` against a real or quaternionic `j`, and
`μ_{iαjβ} μ_{iᾱjβ̄} ≥ 0` for two complex summands; the intersection form `Tr(γ π(p) J π(q) J)` of minimal projections
is every entry of Table 1: `μ`, `∑_α μ`, `2μ`, `∑_{αβ} μ`, `2 ∑_α μ` and `4μ` {1} [26].

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
    `NCG.quatCoord_smul`, `NCG.complexifyL`, `NCG.complexify_mul`, `NCG.complexify_mul_of`, `NCG.complexify_sum`,
    `NCG.complexify_zero`, `NCG.complexify_zero_left`, `NCG.star_complexify`
16. Lightlike/NCG/ComplexSplitting.lean - `NCG.Qp`, `NCG.Qm`, `NCG.Qp_add_Qm`, `NCG.pi_u_sq`, `NCG.pi_u_Qp`, `NCG.pi_u_Qm`,
    `NCG.pi_comm_Qp`, `NCG.pi_comm_Qm`, `NCG.smul_eq_re_add_im`, `NCG.Qp_pi_smul`, `NCG.Qm_pi_smul`, `NCG.QpR`, `NCG.QmR`,
    `NCG.J_Qp_J`, `NCG.J_Qm_J`, `NCG.QpR_add_QmR`, `NCG.pi_comm_QpR`, `NCG.pi_comm_QmR`, `NCG.Qp_comm_QpR`,
    `NCG.Qp_comm_QmR`, `NCG.Qp_mul_Qp`, `NCG.Qm_mul_Qm`, `NCG.Qp_mul_Qm`, `NCG.Qm_mul_Qp`, `NCG.star_Qp`, `NCG.star_Qm`
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
21. Lightlike/NCG/QuaternionSummands.lean - `NCG.MatSumH`, `NCG.unitH`, `NCG.unitH_mul_same`, `NCG.unitH_mul_ne`,
    `NCG.star_unitH`, `NCG.unitHL`, `NCG.rhoH`, `NCG.rhoH_apply`, `NCG.idxH`, `NCG.UH`, `NCG.UH_mul_same`, `NCG.UH_mul_ne`,
    `NCG.star_UH`, `NCG.sum_unitH_block`, `NCG.eq_sum_unitH`, `NCG.phiHFun`, `NCG.phiHFun_apply`, `NCG.phiH`,
    `NCG.phiH_apply`, `NCG.complexify_entries`, `NCG.sum_UH`, `NCG.partialH`, `NCG.sum_sum_UH`, `NCG.sum_phiH_UH`,
    `NCG.unitsH`, `NCG.unitsH_hom_phiH`, `NCG.UH_mem_span`,
    `NCG.pi_single_one_ne_zero`, `NCG.quatComplexification`, `NCG.exists_unitary_quatSummands`
22. Lightlike/NCG/ComplexSummands.lean - `NCG.uC`, `NCG.uC_mul`, `NCG.star_uC`, `NCG.uC_comm`, `NCG.unitC_mul_same`,
    `NCG.unitC_mul_ne`, `NCG.star_unitC`, `NCG.sum_unitC_block`, `NCG.Qb`, `NCG.Qb_mul_Qb`, `NCG.Qb_mul_Qb_ne`, `NCG.star_Qb`,
    `NCG.pi_comm_Qb`, `NCG.Qb_true_add_false`, `NCG.Blocks`, `NCG.UC`, `NCG.Qb_pi_mul_Qb_pi`, `NCG.Qb_pi_mem_span`,
    `NCG.blockC`, `NCG.sum_UC`, `NCG.sum_blocks`, `NCG.UC_zero`, `NCG.unitsC`, `NCG.sum_smul_unitC`, `NCG.phiCAll`,
    `NCG.phiCFun`, `NCG.phiC`, `NCG.phiC_apply`, `NCG.Qb_true_pi_smul`, `NCG.Qb_false_pi_smul`, `NCG.GC`, `NCG.GC_zero`,
    `NCG.unitsC_hom_phiC`, `NCG.complexComplexification`, `NCG.exists_unitary_complexSummands`
23. Lightlike/NCG/PartialUnits.lean - `NCG.PartialUnits`, `NCG.PartialUnits.sum`, `NCG.PartialUnits.sum_U_inl`,
    `NCG.PartialUnits.sum_U_inr`, `NCG.PartialUnits.toMatrixUnits`
24. Lightlike/NCG/MixedSummands.lean - `NCG.unitR_mul_same`, `NCG.unitR_mul_ne`, `NCG.star_unitR`, `NCG.partialR`,
    `NCG.sum_unitR_block`, `NCG.sum_partialR`, `NCG.sum_sum_partialR`, `NCG.sum_phiR_partialR`, `NCG.partialR_mem_span`,
    `NCG.sgn`, `NCG.psiPart`, `NCG.psiPart_add`, `NCG.psiPart_mul`, `NCG.star_psiPart`, `NCG.psi_rsmul`,
    `NCG.smul_eq_re_im`, `NCG.I_smul_smul_eq`, `NCG.smul_psiPart_true`, `NCG.smul_psiPart_false`, `NCG.psiPart_zero`,
    `NCG.psiPart_add'`, `NCG.psiPartA`, `NCG.psiPart_mem_span`, `NCG.BlocksP`, `NCG.partialC`, `NCG.sum_subtype_ne_zero`,
    `NCG.psiPart_unitC_zero`, `NCG.sum_partialC`, `NCG.sum_sum_partialC`, `NCG.phiPAll`, `NCG.GP`, `NCG.phiPAll_one`,
    `NCG.phiPAll_mul`, `NCG.phiPAll_zero`, `NCG.phiPAll_add`, `NCG.phiPAll_star`, `NCG.phiPAll_algebraMap`,
    `NCG.sum_phiP_partialC`, `NCG.mul_eq_zero_of_mem_span`, `NCG.MatSumMixed`, `NCG.psi₁`, `NCG.psi₂`, `NCG.psi₃`,
    `NCG.pi_eq_psi`, `NCG.partialCH`, `NCG.partialR_mul_CH`, `NCG.partialCH_mul_R`, `NCG.partialMixed`,
    `NCG.sum_partialMixed`, `NCG.unitsMixed`, `NCG.dMixed`, `NCG.phiMixedFun`, `NCG.phiMixed`,
    `NCG.unitsMixed_hom_phiMixed`, `NCG.pi_ne_zero_of_ne`, `NCG.span_psi_le`, `NCG.mixedComplexification`,
    `NCG.neZero_dMixed`, `NCG.exists_unitary_mixed`
25. Lightlike/NCG/Chirality.lean - `NCG.unit_mul_mul_unit`, `NCG.lU_pi_lU`, `NCG.rU_rightOp_rU`, `NCG.IsOrientable`,
    `NCG.chiScalar`, `NCG.grading_lU`, `NCG.grading_rU`, `NCG.grading_smul_of_mem_Vsub`, `NCG.lU_pi_lU'`,
    `NCG.rU_rightOp_rU'`, `NCG.chiScalarAt`, `NCG.grading_smul_of_corner`, `NCG.chiScalarAt_eq`,
    `NCG.chiScalar_mul_self`, `NCG.conj_chiScalar`, `NCG.chiScalar_eq_one_or`, `NCG.chiScalar_symm`, `NCG.projC`,
    `NCG.corner`, `NCG.corner_comp`, `NCG.projC_idem`, `NCG.trace_grading_projC`, `NCG.trace_grading_sum`
26. Lightlike/NCG/TableOne.lean - `NCG.IsOrientableA`, `NCG.grading_comm_of_mem_span`, `NCG.Complexification.grading`,
    `NCG.Complexification.isOrientable`, `NCG.chiScalarAt_conj`, `NCG.Xm`, `NCG.Rm`, `NCG.muSigned`,
    `NCG.exists_ne_zero_of_multiplicity`, `NCG.muSigned_mul_nonneg_of`, `NCG.idxH_zero`, `NCG.table1_complex_complex`,
    `NCG.table1_complex_real`, `NCG.table1_complex_quat`, `NCG.muSigned_symm`, `NCG.table1_real_complex`,
    `NCG.table1_quat_complex`, `NCG.trace_grading_of_phi`, `NCG.pR`, `NCG.phiMixed_pR`, `NCG.pH`, `NCG.eH`, `NCG.phiH_pH`,
    `NCG.phiMixed_pH`, `NCG.interForm`, `NCG.interForm_real_real`, `NCG.interForm_quat_quat`, `NCG.interForm_real_quat`,
    `NCG.pC`, `NCG.BlocksOf`, `NCG.phiMixed_pC`, `NCG.interForm_complex_real`, `NCG.interForm_complex_complex`,
    `NCG.interForm_complex_quat`, `NCG.interForm_real_complex`, `NCG.interForm_quat_complex`

## References

1. T. Krajewski, *Classification of finite spectral triples*, J. Geom. Phys. 28 (1998) 1-30, arXiv:hep-th/9701081,
   Sections 2, 3.1, 3.2, 3.3 and 3.4.
2. M. Paschke and A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029, Section 2,
   Lemmas 1-4 and 6.
