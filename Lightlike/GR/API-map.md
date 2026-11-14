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

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 4.
2. K. Schwarzschild, Über das Gravitationsfeld eines Massenpunktes nach der Einsteinschen
   Theorie, *Sitzungsber. Preuss. Akad. Wiss.* (1916) 189.
