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

The big bang: for a positive scale factor on an open interval that satisfies Friedmann's second equation with `Λ = 0` and
the strong energy condition `ρ + 3p ≥ 0`, so that `a'' ≤ 0`, and that is expanding at some time `t₀`, the expansion rate was
larger in the past, the age `t₀ - t₁` of the interval is at most the Hubble time `a(t₀)/a'(t₀)` (the tangent line at `t₀` bounds
`a` from above), and, for `k ≥ 0` and `Λ = 0`, the density diverges as `a → 0` at the left end of the interval [4]. If
moreover `p ≤ ρ`, the singularity is at `a = 0`: either `a → 0` at the left end of the interval, or the expansion rate, its
derivative, the density and the pressure stay bounded there, because `ρ a⁶` is nondecreasing (`(ρ a⁶)' = 3 a⁵ a' (ρ - p)`). The
hypothesis `p ≤ ρ` cannot be dropped: `a = 1 + √t` with `k = 0` has positive density and pressure and an expansion rate that
diverges at `t = 0` while `a → 1` [5]. For the equation of state `p = wρ` with a constant `w > -1/3` the singularity is at `a = 0` without
`p ≤ ρ`, since `(a'² + k) a^{1+3w}` is constant (`ρ ∝ a^{-3(1+w)}`) [6].

The comoving observers of FLRW form a geodesic congruence without shear or rotation whose expansion is `Θ = 3ȧ/a`, and
along it Raychaudhuri's equation `dΘ/dt + Θ²/3 = -R₀₀` holds; in Minkowski space the expansion vanishes, and in de Sitter
space it is the constant `3H` while `R₀₀ = -3H² < 0`, so the convergence condition fails and the congruence does not focus.
If the expansion obeys `Θ' ≤ -Θ²/m` and starts negative, it reaches `-∞` within affine time `m/|Θ(0)|` (focusing; the lemma is in the spacetime geometry API) [3].
Raychaudhuri's equation for a general geodesic congruence on a manifold is not yet formalized. [TODO]

## Lean References

1. Lightlike/Cosmology/FLRW.lean - `Cosmology.flrwMetric`, `Cosmology.flrwDomain`,
   `Cosmology.perfectFluid`, `Cosmology.IsEinsteinSolution`, `Cosmology.FirstFriedmann`,
   `Cosmology.SecondFriedmann`, `Cosmology.flrw_einstein_iff_friedmann`,
   `Cosmology.friedmann_continuity`, `Cosmology.deSitter_einstein_iff`,
   `Cosmology.einsteinStatic_einstein_iff`, `Cosmology.not_einsteinStatic_einstein_of_negCurvature`
2. Lightlike/Cosmology/FLRWPhyslib.lean - `Cosmology.onTime`, `Cosmology.timeDeriv_onTime`,
   `Cosmology.firstOrderFriedmann_onTime_iff`, `Cosmology.secondOrderFriedmann_onTime_iff`,
   `Cosmology.flrw_einstein_iff_physlib_friedmann`
3. Lightlike/Cosmology/Raychaudhuri.lean - `Cosmology.covConst`, `Cosmology.expansionConst`,
   `Cosmology.flrw_comoving_covDeriv`, `Cosmology.flrw_comoving_geodesic`, `Cosmology.flrw_comoving_expansion`,
   `Cosmology.flrw_raychaudhuri`, `Cosmology.minkowski_comoving_expansion`, `Cosmology.deSitter_no_focusing`
4. Lightlike/Cosmology/BigBang.lean - `Cosmology.deriv2_nonpos_of_strong_energy`, `Cosmology.deriv_ge_of_strong_energy`,
   `Cosmology.le_tangent_of_strong_energy`, `Cosmology.bigBang_age_le`, `Cosmology.bigBang_density_tendsto_atTop`,
   `Cosmology.bigBang_age_lt_of_pos_density`, `Cosmology.bigBang_density_tendsto_atTop_of_pos`, `Cosmology.milne_friedmann`
5. Lightlike/Cosmology/BigBangSingularity.lean - `Cosmology.friedmann_834`, `Cosmology.bigBang_singularity`,
   `Cosmology.onePlusSqrt`, `Cosmology.onePlusSqrt_friedmann`, `Cosmology.onePlusSqrt_not_dominant`
6. Lightlike/Cosmology/BigBangEOS.lean - `Cosmology.bigBang_singularity_of_eos`

## References

1. S. M. Carroll, *Lecture Notes on General Relativity*, 1997, arXiv:gr-qc/9712019, chapter 8.
