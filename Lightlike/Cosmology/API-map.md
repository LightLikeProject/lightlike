# Cosmology

## Abstract (Alpha)

This API states the FLRW spacetimes for every spatial curvature `k`, filled with a perfect fluid
at rest, and proves that the Einstein equations with a cosmological constant reduce to Friedmann's
two equations. It builds on the coordinate curvature of the spacetime geometry API, and links its
Friedmann equations to Physlib's.

## Content (Alpha)

The FLRW metric `-dt² + a(t)² dx² / (1 + k |x|²/4)²` is written in isotropic coordinates, on the
set where `t ∈ I` and `1 + k |x|²/4 > 0`; for `k < 0` this set is the Poincaré ball, the whole
hyperbolic space, and for `k > 0` it is all of `ℝ³`, the stereographic chart of the 3-sphere
minus one point. For a smooth positive scale factor on an open interval and the perfect fluid
`T = (ρ + p) u u + p g` at rest in the chart, the Einstein equations with cosmological constant
`Λ` hold iff Friedmann's first and second equations hold at every time {1} [1]. Friedmann's two
equations imply the continuity equation `ρ' + 3H(ρ + p) = 0` [1]. De Sitter space, `a = e^{Ht}`
with `k = 0`, solves them iff `H² = 8πGρ/3`; Einstein's static universe with `k = 1` and dust
solves them iff `Λ = 1/a² = 4πGρ`; with `k = -1` there is no static dust solution [1].

The two Friedmann equations agree with Physlib's `FirstOrderFriedmann` and
`SecondOrderFriedmann` at `c = 1`, through the time coordinate of Physlib's `Time`, and the
equivalence holds with Physlib's equations on the right [2]. The statement on a manifold
`I × Σ`, with `Σ` a complete space of constant curvature, is not yet formalized. [TODO]

## Lean References

1. Lightlike/Cosmology/FLRW.lean - `flrwMetric`, `flrwDomain`, `perfectFluid`,
   `IsEinsteinSolution`, `FirstFriedmann`, `SecondFriedmann`, `flrw_einstein_iff_friedmann`,
   `friedmann_continuity`, `deSitter_einstein_iff`, `einsteinStatic_einstein_iff`,
   `not_einsteinStatic_einstein_of_negCurvature`
2. Lightlike/Cosmology/FLRWPhyslib.lean - `onTime`, `timeDeriv_onTime`,
   `firstOrderFriedmann_onTime_iff`, `secondOrderFriedmann_onTime_iff`,
   `flrw_einstein_iff_physlib_friedmann`

## References

1. S. M. Carroll, *Lecture Notes on General Relativity*, 1997, arXiv:gr-qc/9712019, chapter 8.
