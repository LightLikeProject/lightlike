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

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 4.
2. K. Schwarzschild, Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
   Theorie, *Sitzungsber. Preuss. Akad. Wiss.* (1916) 189.
