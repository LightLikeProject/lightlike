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

## References

1. T. Krajewski, *Classification of finite spectral triples*, J. Geom. Phys. 28 (1998) 1-30, arXiv:hep-th/9701081,
   Sections 2, 3.1 and 3.2.
2. M. Paschke and A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029, Section 2,
   Lemmas 1-4 and 6.
