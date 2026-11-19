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

## Lean References

1. Lightlike/NCG/FiniteSpectralTriple.lean - `NCG.FiniteSpectralTriple`, `NCG.FiniteSpectralTriple.comm`,
   `NCG.RealStructure`, `NCG.Grading`
2. Lightlike/NCG/TestsTwoPoint.lean - `NCG.TwoPoint.pi2`, `NCG.TwoPoint.conjJ`, `NCG.TwoPoint.conjJ_pi2_conjJ`,
   `NCG.TwoPoint.twoPoint`, `NCG.TwoPoint.firstOrder_iff`, `NCG.TwoPoint.not_firstOrder_sigmaX`

## References

1. T. Krajewski, *Classification of finite spectral triples*, J. Geom. Phys. 28 (1998) 1-30, arXiv:hep-th/9701081,
   Section 2.
2. M. Paschke and A. Sitarz, *Discrete spectral triples and their symmetries*, arXiv:q-alg/9612029, Section 2.
