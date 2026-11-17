# Causal structure of Lorentzian manifolds

## Abstract (Alpha)

This API gives the definitions of the causal theory of a Lorentzian manifold: a time orientation, causal and timelike curves, the chronological and causal futures and pasts, the causal ladder from chronology up to global hyperbolicity, and Cauchy surfaces. It contains definitions, checks on Minkowski space, and the first statements about the futures: they contain each other, are reflexive and transitive, and causality implies chronology. The deeper statements are open proof tasks.

## Content (Alpha)

A time orientation of a Lorentzian manifold is a continuous timelike vector field; a tangent vector is future directed when its inner product with the field is negative [1] {1}. A causal curve is a locally Lipschitz curve, in charts, on an interval whose velocity, which exists almost everywhere, is future-directed causal almost everywhere; timelike curves are the same with timelike velocity [2] {2}. The chronological future I⁺(x) of a point is the set of points reached from it by a future-directed timelike curve, the causal future J⁺(x) the set reached by a causal curve, constant curves included [3] {3}.

The causal ladder is chronology, causality, strong causality, stable causality, causal simplicity and global hyperbolicity [4] {4}; each is defined as a property of the time orientation, and the implications between them are open tasks. A Cauchy surface is a set that every inextendible timelike curve meets exactly once [4] {4}. The domain of dependence of a set is the set of points every inextendible causal curve through which meets the set on the correct side [6] {6}.

The chronological future is contained in the causal future, a point lies in its own causal future, both futures are transitive, and a causal manifold is chronological; the proofs restrict, translate and glue locally Lipschitz curves [7] {3}. In Minkowski space the constant field ∂₀ is a time orientation, and a straight line with a future-directed timelike direction is a timelike curve, so x + v is in the chronological future of x [5] {5}.

## Lean References

1. Lightlike/Spacetime/Causal/TimeOrientation.lean - `Causal.TimeOrientation`
2. Lightlike/Spacetime/Causal/CausalCurve.lean - `Causal.IsCurveWith`, `Causal.IsFutureCausalCurve`, `Causal.IsFutureTimelikeCurve`
3. Lightlike/Spacetime/Causal/Relations.lean - `Causal.chronFuture`, `Causal.causalFuture`
4. Lightlike/Spacetime/Causal/Ladder.lean - `Causal.IsGloballyHyperbolic`, `Causal.IsCauchySurface`
5. Lightlike/Spacetime/Causal/MinkowskiCausal.lean - `Causal.minkowskiOrientation`, `Causal.line_mem_chronFuture`
6. Lightlike/Spacetime/Causal/DomainOfDependence.lean - `Causal.domainDep`
7. Lightlike/Spacetime/Causal/BasicRelations.lean - `Causal.chron_subset_causal`, `Causal.self_mem_causalFuture`, `Causal.causal_trans`, `Causal.chron_trans`, `Causal.chronological_of_causal`

## References

1. S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University Press, 1973, section 6.2.
2. E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), section 2.
3. R. Penrose, *Techniques of Differential Topology in Relativity*, SIAM, 1972, chapter 2.
4. E. Minguzzi and M. Sánchez, *The causal hierarchy of spacetimes*, in *Recent developments in pseudo-Riemannian geometry*, EMS, 2008.
5. R. M. Wald, *General Relativity*, University of Chicago Press, 1984, section 8.1.
6. R. Geroch, *Domain of dependence*, J. Math. Phys. 11 (1970) 437.
