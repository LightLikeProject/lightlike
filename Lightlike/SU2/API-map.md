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
the spin representations [5]. This is the SU(2) case of the Peter–Weyl theorem {2}. The general
Peter–Weyl theorem for compact groups is also formalized in `Lightlike/HarmonicAnalysis/`: the matrix
coefficients are dense in `C(G)` and in `L²(G)`, and `L²(G)` is the Hilbert sum of the isotypic
components (`peterWeyl_dense_continuous`, `peterWeyl_dense_L2`, `peterWeyl_isHilbertSum`).

## Lean References

1. Lightlike/SU2/SpinRep.lean - `SU2.spinRep`, `SU2.spinRepresentation_isIrreducible`
2. Lightlike/SU2/Su2Exp.lean - `SU2.exists_exp_eq`
3. Lightlike/SU2/LieProduct.lean - `SU2.lie_product`
4. Lightlike/SU2/LieBridge.lean - `SU2.dSpin_E`, `SU2.dSpin_F`, `SU2.dSpin_H`
5. Lightlike/SU2/Completeness.lean - `SU2.spinRep_complete`

## References

1. Physlib, the `sl₂` representation theory in `PhyslibAlpha.Sl2`, pinned at commit `cdfa609`.
2. F. Peter, H. Weyl, Die Vollständigkeit der primitiven Darstellungen einer geschlossenen
   kontinuierlichen Gruppe, *Math. Ann.* 97 (1927) 737.
