# Exact solutions of general relativity

## Abstract (Alpha)

This API states the vacuum Einstein equations, with a cosmological constant, for a metric given in
coordinates, and verifies two exact solutions: Minkowski space and the exterior Schwarzschild
metric. It builds on the coordinate curvature of the spacetime geometry API.

## Content (Alpha)

The Einstein tensor is built from the Ricci tensor and the scalar curvature, and the vacuum
Einstein equations with cosmological constant `Λ` say that the Einstein tensor plus `Λ g` vanishes
on an open set {1} [1]. For `Λ = 0` in any dimension other than two, they are equivalent to the
vanishing of the Ricci tensor [1]. Minkowski space solves them [1].

The exterior Schwarzschild metric of mass `M > 0`, in Schwarzschild coordinates on `r > 2M` and
`0 < θ < π`, has Lorentzian signature and solves the vacuum equations with `Λ = 0` {2} [2]. Other
exact solutions, such as Kerr and de Sitter, are not yet formalized. [TODO]

The Kruskal-Szekeres extension of the Schwarzschild metric: its four regions, the horizon `T = ±X`, the
radial null directions and the one-way property of the black hole region {3} [3]; the Kruskal coordinates of
the Schwarzschild exterior, which is region I {3} [4]; its Penrose diagram {3} [5]. The Kretschmann scalar of
the Schwarzschild metric is `48 M²/r⁶` [6] (the value printed in {3}, eq. (7.30), is `12 G²M²/r⁶`), also in
Eddington-Finkelstein and Kruskal coordinates, where it is unbounded near `r = 0` [7]; ingoing radial null
geodesics reach `r = 0` at a finite affine parameter [8], and the energy, the axial angular momentum and the
radial equation hold along all geodesics of the Eddington-Finkelstein chart [13]. In the global chart
of the Kruskal manifold the equations of motion of the geodesics are derived from Noether's formula [14], and
the boost charge, the squared angular momentum and `g(w, w)` are constant along them [15]. The whole Kruskal manifold
`{X² - T² > -1} × S²` is given in one global chart as a Lorentzian manifold [9], of which `(T, X, θ, φ)` is a
chart [10]; it solves the vacuum equations [11], and in every extension of it, in the sense of {4}, a sequence
approaching the singularity has no limit [12]. Maximality of the extension is not yet formalized. [TODO]

## Lean References

1. Lightlike/GR/Einstein.lean - `einsteinTensor`, `IsVacuumSolution`,
   `vacuum_iff_ricci_eq_zero`, `minkowski_isVacuumSolution`
2. Lightlike/GR/Schwarzschild.lean - `sch_isLorentzian`, `sch_isVacuumSolution`
3. Lightlike/GR/KruskalRegions.lean - `kr_eq_two_mul_iff`, `kr_eq_kr_iff`, `kruskalI`, `kruskalII`,
   `kruskalIII`, `kruskalIV`, `kruskalU_eq_union`, `two_mul_lt_kr_iff_mem`, `kr_lt_two_mul_iff_mem`,
   `kruskalQuad_radial_eq_zero_iff`, `IsKruskalFutureCausal`, `kruskalII_of_futureCausal`,
   `kr_lt_of_futureCausal_kruskalII`
4. Lightlike/GR/KruskalExterior.lean - `kruskalChange_exterior`, `kruskalChange_exterior_div`,
   `kruskalChange_exterior_mem`, `exists_exterior_of_mem_kruskalI`
5. Lightlike/GR/KruskalPenrose.lean - `penroseMap`, `penroseU`, `bijOn_penroseMap`,
   `tan_mul_tan_eq_one_of_abs_add`, `penroseMap_horizon_iff`, `pullback_kruskal_penroseInv`,
   `penrose_conformalFactor_pos`
6. Lightlike/GR/SchwarzschildKretschmann.lean - `schRiem`, `riemann_sch`, `kretschmann_sch`
7. Lightlike/GR/KruskalKretschmann.lean - `kretschmann_congr_on`, `kretschmann_ef`, `kretschmann_kruskal`,
   `kretschmann_kruskal_unbounded`, `not_tendsto_of_isometric_chart`
8. Lightlike/GR/EFNullGeodesic.lean - `ef_ingoing_isGeodesicOn`, `ef_ingoing_null`,
   `tendsto_kretschmann_ef_ingoing`
9. Lightlike/GR/KruskalManifold.lean - `kruskalC`, `kruskalCMetric`, `kruskalC_isLorentzian`, `kruskalCOpen`,
   `kruskalManifoldMetric`
10. Lightlike/GR/KruskalSpherical.lean - `kruskalSph`, `jac_kruskalSph`, `pullback_kruskalC_sph`,
    `isChartChange_kruskalSph`
11. Lightlike/GR/KruskalManifoldCurvature.lean - `exists_kruskalSph_eq`, `ricci_kruskalC_eq_zero`,
    `kruskalC_isVacuumSolution`, `kretschmann_kruskalC`
12. Lightlike/GR/KruskalExtension.lean - `kretschmann_kruskalC_unbounded`, `not_tendsto_of_isometric_kruskal`,
    `IsLorentzianExtension.not_tendsto_kruskal`
13. Lightlike/GR/EFConstants.lean - `pd_eq_zero_of_invariant`, `ef_hasDerivAt_energy`, `ef_hasDerivAt_angular`,
    `ef_radial_identity`
14. Lightlike/GR/KruskalGeodesic.lean - `hasDerivAt_kG`, `hasDerivAt_kh`, `kQ`, `contraction_kruskalC`,
    `kruskalC_hasDerivAt_pT`, `kruskalC_hasDerivAt_pX`, `kruskalC_hasDerivAt_angular`
15. Lightlike/GR/KruskalGeodesicBound.lean - `kruskalC_hasDerivAt_r`, `kruskalC_hasDerivAt_boost`,
    `kruskalC_hasDerivAt_L2`, `kruskalC_hasDerivAt_kQ`

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 4.
2. K. Schwarzschild, Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
   Theorie, *Sitzungsber. Preuss. Akad. Wiss.* (1916) 189.
3. S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7.
4. J. Sbierski, The C⁰-inextendibility of the Schwarzschild spacetime and the spacelike diameter in
   Lorentzian geometry, arXiv:1507.00601, Definition 2.15.
