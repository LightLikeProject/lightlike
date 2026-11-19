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

## Lean References

1. Lightlike/GR/Einstein.lean - `einsteinTensor`, `IsVacuumSolution`,
   `vacuum_iff_ricci_eq_zero`, `minkowski_isVacuumSolution`
2. Lightlike/GR/Schwarzschild.lean - `sch_isLorentzian`, `sch_isVacuumSolution`
3. Lightlike/GR/KruskalRegions.lean - `kr_eq_two_mul_iff` (the horizon `r = 2M` is `T = ±X`), `kr_eq_kr_iff`,
   `kruskalI`, `kruskalII`, `kruskalIII`, `kruskalIV`, `kruskalU_eq_union`, `two_mul_lt_kr_iff_mem`,
   `kr_lt_two_mul_iff_mem`, `kruskalQuad_radial_eq_zero_iff` (radial null directions), `IsKruskalFutureCausal`,
   `kruskalII_of_futureCausal` (nothing leaves region II), `kr_lt_of_futureCausal_kruskalII`
4. Lightlike/GR/KruskalExterior.lean - `kruskalChange_exterior` (the Kruskal coordinates of the Schwarzschild
   exterior), `kruskalChange_exterior_div`, `kruskalChange_exterior_mem`, `exists_exterior_of_mem_kruskalI`
5. Lightlike/GR/KruskalPenrose.lean - `penroseMap`, `penroseU`, `bijOn_penroseMap` (the Penrose diagram of the
   Kruskal extension), `tan_mul_tan_eq_one_of_abs_add`, `penroseMap_horizon_iff`,
   `pullback_kruskal_penroseInv`, `penrose_conformalFactor_pos`
6. Lightlike/GR/SchwarzschildKretschmann.lean - `schRiem`, `riemann_sch` (the Riemann tensor of the Schwarzschild
   metric), `kretschmann_sch` (`R_{abcd} R^{abcd} = 48 M²/r⁶`)
7. Lightlike/GR/KruskalKretschmann.lean - `kretschmann_congr_on`, `kretschmann_ef`, `kretschmann_kruskal`
   (`48 M²/r⁶` on the whole Kruskal domain), `kretschmann_kruskal_unbounded`, `not_tendsto_of_isometric_chart`
   (no extension through the singularity `r = 0`)
8. Lightlike/GR/EFNullGeodesic.lean - `IsCoordGeodesic`, `ef_ingoing_isCoordGeodesic`, `ef_ingoing_null`,
   `tendsto_kretschmann_ef_ingoing` (the singularity is reached at finite affine parameter)
9. Lightlike/GR/KruskalManifold.lean - `kruskalC`, `kruskalCMetric` (the Kruskal metric in one global chart of
   `{X² - T² > -1} × S²`), `kruskalC_isLorentzian`, `kruskalCOpen`, `kruskalManifoldMetric` (the
   Kruskal-Szekeres spacetime as a Lorentzian manifold)
10. Lightlike/GR/KruskalSpherical.lean - `kruskalSph`, `jac_kruskalSph`, `pullback_kruskalC_sph` (the metric of
    the global chart pulls back to the Kruskal metric), `isChartChange_kruskalSph`
11. Lightlike/GR/KruskalManifoldCurvature.lean - `exists_kruskalSph_eq`, `ricci_kruskalC_eq_zero`,
    `kruskalC_isVacuumSolution` (vacuum equations on the whole Kruskal manifold), `kretschmann_kruskalC`
12. Lightlike/GR/KruskalExtension.lean - `kretschmann_kruskalC_unbounded`, `not_tendsto_of_isometric_kruskal`,
    `IsLorentzianExtension.not_tendsto_kruskal` (in every extension of the Kruskal manifold a sequence approaching
    the singularity has no limit)

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 4.
2. K. Schwarzschild, Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
   Theorie, *Sitzungsber. Preuss. Akad. Wiss.* (1916) 189.
