# SU(2) recoupling theory

## Abstract (Alpha)

This API develops the recoupling theory of SU(2) that spin foam amplitudes are built from: the
orthogonality of the 3j symbols, orthonormal bases of 4-valent intertwiners and the 6j symbols that
relate them, and the 15j symbol of the 4-simplex, which is the vertex amplitude of the
four-dimensional BF spin foam model. The 6j symbol itself is Physlib's.

## Content (Alpha)

The 3j symbols are orthogonal for all spins [1]. The 4-valent intertwiners obtained by coupling
two pairs of spins through an intermediate spin are orthonormal [2], and the change of basis
between the two pairings is given by the 6j symbol of Physlib {1}, whose recoupling matrix is
orthogonal for all spins [2]. The Biedenharn–Elliott identity is part of the Ponzano–Regge API
{2}.

The 15j symbol of the 4-simplex is defined as a sum over intermediate spins [3]. It equals the
contraction of ten 3j symbols over the 4-simplex for all spins [4], and it satisfies an
orthogonality relation [5]. Reference values for small spins are checked in the test files
{3}. The 10j symbol of the Barrett–Crane model is not yet formalized. [TODO]

## Lean References

1. Lightlike/Recoupling/ThreeJ.lean - `Recoupling.sum_threeJ_mul_threeJ`
2. Lightlike/Recoupling/Intertwiner.lean - `Recoupling.sum_fourJ_mul_fourJ`,
   `Recoupling.sixJSym_orth_all`
3. Lightlike/Recoupling/FifteenJ.lean - `Recoupling.fifteenJSimplex`
4. Lightlike/Recoupling/Simplex.lean - `Recoupling.fifteenJSimplex_eq`
5. Lightlike/Recoupling/Orthogonality.lean - `Recoupling.sum_fifteenJ_mul_fifteenJ`

## References

1. Physlib, the 6j symbol `sixJSym`, pinned at commit `cdfa609`.
2. The Ponzano–Regge API map, `Lightlike/PonzanoRegge/API-map.md`.
3. The project's test files, `Lightlike/Tests/`.
