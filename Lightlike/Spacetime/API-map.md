# Spacetime geometry in coordinates

## Abstract (Alpha)

This API describes spacetime geometry the way general relativity textbooks compute it: a metric is
given by its components in a chart, and the Christoffel symbols, the Riemann and Ricci tensors and
the scalar curvature are the standard coordinate formulas. It also defines Lorentzian metrics on
smooth manifolds and connects them to their coordinate components, so that curvature statements
proven in coordinates apply to the components of a manifold-level metric.

## Content (Alpha)

A coordinate metric on an open set is a smooth, symmetric, invertible matrix-valued function of
the coordinates [1]. From it one computes the Christoffel symbols, the Riemann tensor, the Ricci
tensor and the scalar curvature by the standard formulas {1} [1]. Minkowski space is flat [1].

The lowered Riemann tensor is symmetric under exchange of its index pairs and satisfies the first
Bianchi identity [2]. The second Bianchi identity in coordinates is not yet formalized. [TODO]

Under a smooth change of coordinates the Riemann tensor, the Ricci tensor and the scalar curvature
transform as tensors, and solutions of the vacuum Einstein equations pull back to solutions [3].

A Lorentzian metric on a smooth manifold modelled on `ℝⁿ` is a smooth symmetric bilinear form on
each tangent space with signature (−,+,…,+), in the mostly-plus convention {2} [4]. In every chart
of the atlas its components form a coordinate metric of Lorentzian signature [5]. The curvature of
a manifold-level metric as a tensor field, independent of charts, is not yet formalized. [TODO]

In Minkowski space, an observer who travels out and back along two straight segments ages less
than one who stays at rest [6].

## Lean References

1. Lightlike/Spacetime/Curvature.lean - `IsCoordMetric`, `christoffel`, `riemann`, `ricci`,
   `scalarCurvature`, `minkowski_flat`
2. Lightlike/Spacetime/RiemannSymmetry.lean - `IsCoordMetric.riemannLower_pair_symm`,
   `IsCoordMetric.bianchi_first`
3. Lightlike/Spacetime/ChartChange.lean - `riemann_pullback`, `ricci_pullback`,
   `scalarCurvature_pullback`, `isVacuumSolution_pullback`
4. Lightlike/Spacetime/Lorentzian.lean - `LorentzianMetric`
5. Lightlike/Spacetime/Coordinates.lean - `LorentzianMetric.isLorentzianCoordMetric_coordMetric`
6. Lightlike/Spacetime/Minkowski.lean - `twin_paradox`

## References

1. S. M. Carroll, *Spacetime and Geometry*, Addison-Wesley, 2004, chapter 3.
2. R. M. Wald, *General Relativity*, University of Chicago Press, 1984.
