# Representations of SU(2)

## Abstract (Alpha)

This API constructs the unitary spin representations of SU(2) and proves that they are, up to
equivalence, all its continuous irreducible finite-dimensional representations. It connects them
to the standard `sl₂`-modules of Physlib, so that results proven for the Lie algebra transfer to
the group.

## Content (Alpha)

For each natural number `n`, the spin-`n/2` representation of SU(2) acts unitarily on a space of
dimension `n + 1` and is irreducible [1]. Every element of SU(2) is the exponential of an element
of its Lie algebra [2], and the Lie product formula holds for matrices [3]. With these, the
differential of the spin-`n/2` representation acts on the generators `E`, `F`, `H` exactly as
Physlib's standard `sl₂`-module `V(n)` {1} [4].

Every continuous irreducible finite-dimensional representation of SU(2) is equivalent to one of
the spin representations [5], also in the unitary form [13]. This is the SU(2) case of the Peter–Weyl theorem {2}. The general
Peter–Weyl theorem for compact groups is also formalized in `Lightlike/HarmonicAnalysis/`: the matrix
coefficients are dense in `C(G)` and in `L²(G)`, and `L²(G)` is the Hilbert sum of the isotypic
components (`peterWeyl_dense_continuous`, `peterWeyl_dense_L2`, `peterWeyl_isHilbertSum`). For the
normalised Haar measure of the group the Hilbert sum statement needs no hypothesis on a measure [14].

The spin representations are unitary and continuous [1]. The Clebsch–Gordan matrices of Physlib
intertwine the representations of the group (Lightlike/Spin4/CGBridge.lean), and with them the two
ways of coupling three spins to a total spin are equivariant maps whose overlap is Racah's 6j symbol
of Physlib {1}, and the matrix of the overlap is that 6j symbol times the identity [12].

Further results of this area in the results catalogue:
Peter–Weyl (density form): for a compact Hausdorff group, the matrix coefficients of finite-dimensional
unitary representations are dense in C(G) in the sup norm and, for a Haar measure, in L²(G) [6].
Peter–Weyl (Hilbert sum form): L²(G) of a compact group with a Haar measure is the Hilbert direct sum of
the isotypic components of the irreducible unitary representation classes [7]. Schur orthogonality of
the matrix coefficients of irreducible unitary representations of a compact group: zero for inequivalent
representations, δδ/dim for equal ones [8]. The characters e^{inθ} of U(1) form a Hilbert basis of
L²(U(1)), and the irreducible unitary representations of the circle are the characters [9]. Schur
orthogonality of the matrix coefficients and of the characters of the spin-n/2 representations of SU(2)
[10]. The real line has no square-integrable matrix coefficients: its unitary characters are not in
L²(R) [11].

## Lean References

1. Lightlike/SU2/SpinRep.lean - `SU2.spinRep`, `SU2.spinRepresentation_isIrreducible`,
   `SU2.spinMat_mem_unitaryGroup`, `SU2.continuous_spinRep`
2. Lightlike/SU2/Su2Exp.lean - `SU2.exists_exp_eq`
3. Lightlike/SU2/LieProduct.lean - `SU2.lie_product`
4. Lightlike/SU2/LieBridge.lean - `SU2.dSpin_E`, `SU2.dSpin_F`, `SU2.dSpin_H`,
   `SU2.exists_dSpin_equiv`
5. Lightlike/SU2/Completeness.lean - `SU2.spinRep_complete`
6. Lightlike/HarmonicAnalysis/PeterWeyl.lean - `HarmonicAnalysis.peterWeyl_dense_continuous`,
   `HarmonicAnalysis.peterWeyl_dense_L2`
7. Lightlike/HarmonicAnalysis/PeterWeylIsotypic.lean - `HarmonicAnalysis.peterWeyl_isHilbertSum`
8. Lightlike/HarmonicAnalysis/SchurOrthogonality.lean -
   `HarmonicAnalysis.UnitaryMatrixRep.schur_orthogonality_ne`,
   `HarmonicAnalysis.UnitaryMatrixRep.schur_orthogonality_eq`
9. Lightlike/HarmonicAnalysis/PeterWeylCircle.lean - `HarmonicAnalysis.circle_hilbertBasis`,
   `HarmonicAnalysis.orthonormal_circleMonoLp`, `HarmonicAnalysis.circle_irreducible_classification`
10. Lightlike/HarmonicAnalysis/PeterWeylSU2.lean - `HarmonicAnalysis.su2_schur_orthogonality`,
    `HarmonicAnalysis.su2_character_orthogonality`
11. Lightlike/HarmonicAnalysis/PeterWeylReal.lean - `HarmonicAnalysis.real_not_forall_memLp_two`,
    `HarmonicAnalysis.real_character_not_memLp_two`
12. Lightlike/SU2/Recoupling6j.lean - `SU2.coupleLeft_equivariant`, `SU2.coupleRight_equivariant`,
    `SU2.sum_cg_overlap`, `SU2.sum_cg_matrix`
13. Lightlike/HarmonicAnalysis/SU2Complete.lean - `HarmonicAnalysis.su2_irreducible_classification`
14. Lightlike/HarmonicAnalysis/PeterWeylTests.lean - `HarmonicAnalysis.peterWeyl_isHilbertSum_haar`

## References

1. Physlib, the `sl₂` representation theory in `PhyslibAlpha.Sl2`, pinned at commit `cdfa609`.
2. F. Peter, H. Weyl, Die Vollständigkeit der primitiven Darstellungen einer geschlossenen
   kontinuierlichen Gruppe, *Math. Ann.* 97 (1927) 737.
