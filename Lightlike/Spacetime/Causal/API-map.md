# Causal structure of Lorentzian manifolds

## Abstract (Alpha)

This API gives the definitions of the causal theory of a Lorentzian manifold: a time orientation, causal and timelike curves, the chronological and causal futures and pasts, the causal ladder from chronology up to global hyperbolicity, and Cauchy surfaces. It contains definitions, checks on Minkowski space, and the first statements about the futures: they contain each other, are reflexive and transitive, and causality implies chronology. In Minkowski space the causal future is the closed light cone and the space is globally hyperbolic. The deeper statements are open proof tasks.

## Content (Alpha)

A time orientation of a Lorentzian manifold is a continuous timelike vector field; a tangent vector is future directed when its inner product with the field is negative [1] {1}. A causal curve is a locally Lipschitz curve, in charts, on an interval whose velocity, which exists almost everywhere, is future-directed causal almost everywhere; timelike curves are the same with timelike velocity and, in addition, a margin: on every compact subinterval the velocity stays in a closed cone strictly inside the future timelike cone, `g(γ', γ') ≤ -ε g(γ', X)²` [2] {2}. The margin is a difference of form from the textbooks (Hawking–Ellis section 6.2, Wald section 8.1), approved by the maintainers on 17 November 2026; every `C¹` curve with timelike velocity everywhere has it, and so does a concatenation of such curves [12] {2}. That the margin does not change the chronological future is open (task T-GE2-P19), not claimed. The chronological future I⁺(x) of a point is the set of points reached from it by a future-directed timelike curve, the causal future J⁺(x) the set reached by a causal curve, constant curves included [3] {3}.

The causal ladder is chronology, causality, strong causality, stable causality, causal simplicity and global hyperbolicity [4] {4}; each is defined as a property of the time orientation, and the implications between them are open tasks. A curve is inextendible if it has no endpoint, that is, no point to which it converges at the end of its parameter interval (Wald section 8.1, Hawking–Ellis section 6.2) [2] {2}. A Cauchy surface is a set that every inextendible timelike curve meets exactly once [4] {4}. The domain of dependence of a set is the set of points every inextendible causal curve through which meets the set on the correct side [6] {6}.

The chronological future is contained in the causal future, a point lies in its own causal future, both futures are transitive, and a causal manifold is chronological; the proofs restrict, translate and glue locally Lipschitz curves [7] {3}. In Minkowski space the causal future of a point is the closed light cone, obtained by integrating the derivative of a Lipschitz causal curve [9] {5}, and the causal diamonds are compact and the open diamonds are causally convex neighbourhoods, so the space is globally hyperbolic [8] {5}. In Minkowski space the slice `t = 0` is a Cauchy surface: the time strictly increases along a timelike curve and the space displacement is bounded by it, so an inextendible curve meets the slice at most once, and at least once because otherwise its time is monotone and bounded, the curve is Cauchy at one end and has an endpoint [13] {5}. An achronal set whose domain of dependence is the whole manifold is a Cauchy surface (the converse direction is open) [14] {2}. On a Hausdorff, second countable manifold without boundary every timelike curve extends to an inextendible one: the integral curves of a smooth future-directed timelike vector field, followed forwards and backwards, have no endpoints (the escape lemma for a field without zeros), and are glued to the curve; so a Cauchy surface is achronal [15] {2} [16] {2}. Through every point there is an inextendible timelike curve, so every point lies in a Cauchy surface or in the chronological future or past of one of its points [17] {2}. A Cauchy surface is closed: the chronological future is open, and so is the chronological past by time reversal [18] {2}. A continuous time orientation can be replaced by a smooth one: smooth partitions of unity glue chart-constant fields, and the future timelike cone of a Lorentzian form is convex [10] {1} [11] {1}. The constant field ∂₀ is a time orientation, and a straight line with a future-directed timelike direction is a timelike curve, so x + v is in the chronological future of x [5] {5}. Given the perturbation step (an inextendible causal curve missing the surface in the past of a point of `S ∪ I⁺(S)` yields an inextendible timelike curve missing it, and the time dual), a Cauchy surface has the whole manifold as domain of dependence [19] {6}; the perturbation step itself is open.

The push-up lemmas (a point of the chronological future of `x` followed by a causal curve stays in it) follow from the openness of the chronological futures and a local push-up property, by connectedness along the causal curve, and the second form by time reversal [20]. In a manifold without boundary the local push-up property follows from the openness of the chronological future: a causal curve in a small chart ball is lifted to a timelike curve with the same end by a displacement along a timelike vector proportional to the increase of the time function of the chart, and the lift starts in the open set that contains the start of the causal curve [21].

Future-inextendible causal curves with a limit point have a future-inextendible causal limit curve through it: near every point a uniform step gives, from any limit point of a subsequence, a unit arc of chart displacement bounded below (a curve that stays in a closed chart box has an endpoint, so inextendible curves leave it, and the one-chart limit-curve theorem applies to the exit arcs); the arcs are glued along a diagonal subsequence into a curve on the half-line of non-negative parameters [23], and a curve of such arcs cannot converge, because only finitely many charts are used near a putative endpoint [24]; together these give the limit curve [22] {1}.

## Lean References

1. Lightlike/Spacetime/Causal/TimeOrientation.lean - `Causal.TimeOrientation`
2. Lightlike/Spacetime/Causal/CausalCurve.lean - `Causal.IsCurveWith`, `Causal.IsFutureCausalCurve`, `Causal.IsFutureTimelikeCurve`, `Causal.IsInextendibleWith`, `Causal.HasFutureEndpoint`
3. Lightlike/Spacetime/Causal/Relations.lean - `Causal.chronFuture`, `Causal.causalFuture`
4. Lightlike/Spacetime/Causal/Ladder.lean - `Causal.IsGloballyHyperbolic`, `Causal.IsCauchySurface`
5. Lightlike/Spacetime/Causal/MinkowskiCausal.lean - `Causal.minkowskiOrientation`, `Causal.line_mem_chronFuture`
6. Lightlike/Spacetime/Causal/DomainOfDependence.lean - `Causal.domainDep`
7. Lightlike/Spacetime/Causal/BasicRelations.lean - `Causal.chron_subset_causal`, `Causal.self_mem_causalFuture`, `Causal.causal_trans`, `Causal.chron_trans`, `Causal.chronological_of_causal`
8. Lightlike/Spacetime/Causal/MinkowskiGH.lean - `Causal.minkowski_globallyHyperbolic`
9. Lightlike/Spacetime/Causal/MinkowskiFuture.lean - `Causal.minkowski_causalFuture_eq`
10. Lightlike/Spacetime/Causal/SmoothOrientation.lean - `Causal.exists_smooth_field`
11. Lightlike/Spacetime/Causal/ConeConvex.lean - `IsLorentzianForm.convex_futureTimelike`
12. Lightlike/Spacetime/Causal/CurveMargin.lean - `Causal.isFutureTimelikeCurve_of_contMDiffOn`, `Causal.isLocallyLipschitzOn_of_contMDiffOn`
13. Lightlike/Spacetime/Causal/MinkowskiCauchy.lean - `Causal.minkowski_slice_isCauchySurface`
14. Lightlike/Spacetime/Causal/CauchyDomain.lean - `Causal.isCauchySurface_of_domainDep_eq_univ`
15. Lightlike/Spacetime/Causal/IntegralCurves.lean - `Causal.curveMax_not_hasFutureEndpoint`, `Causal.isFutureTimelikeCurve_of_integralCurve`
16. Lightlike/Spacetime/Causal/Extension.lean - `Causal.exists_inextendible_of_timelike`, `Causal.IsCauchySurface.isAchronal_of_boundaryless`
17. Lightlike/Spacetime/Causal/CauchyCover.lean - `Causal.exists_inextendible_through`, `Causal.IsCauchySurface.cover`
18. Lightlike/Spacetime/Causal/CauchyClosed.lean - `Causal.IsCauchySurface.isClosed`, `Causal.IsCauchySurface.isClosed_of_isOpen_chronPast`
19. Lightlike/Spacetime/Causal/CauchyAssembly.lean - `Causal.PerturbFuture`, `Causal.IsCauchySurface.domainDep_eq_univ_of_perturb`
20. Lightlike/Spacetime/Causal/PushUp.lean - `Causal.chronFuture_causalFuture_trans_of`, `Causal.causalFuture_chronFuture_trans_of`, `Causal.chronFuture_neg_iff`: the push-up lemmas from the openness of the chronological futures and a local push-up property, and time reversal.
21. Lightlike/Spacetime/CausalLadder/LocalLift.lean - `Causal.localPushUp_of_isOpen`, `Causal.chronFuture_causalFuture_trans_of_isOpen`, `Causal.causalFuture_chronFuture_trans_of_isOpen`: the local push-up property from the openness of the chronological futures, in a manifold without boundary, and the two push-up lemmas from the openness alone.
22. Lightlike/Spacetime/CausalLadder/LimitCurveStep.lean - `Causal.limit_curve_step`, `Causal.exists_inextendible_limit_curve_of_step`: the uniform step and the limit-curve theorem for future-inextendible causal curves.
23. Lightlike/Spacetime/CausalLadder/GluedLimitCurve.lean - `Causal.exists_glued_limit_curve_of_step`: the unit arcs glued along a diagonal subsequence into a limit curve on the non-negative half-line.
24. Lightlike/Spacetime/CausalLadder/UnitArcEndpoint.lean - `Causal.not_tendsto_of_unit_arcs`: a curve on the non-negative half-line made of unit arcs of chart displacement bounded below has no future endpoint.

## References

1. S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University Press, 1973, section 6.2.
2. E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), section 2.
3. R. Penrose, *Techniques of Differential Topology in Relativity*, SIAM, 1972, chapter 2.
4. E. Minguzzi and M. Sánchez, *The causal hierarchy of spacetimes*, in *Recent developments in pseudo-Riemannian geometry*, EMS, 2008.
5. R. M. Wald, *General Relativity*, University of Chicago Press, 1984, section 8.1.
6. R. Geroch, *Domain of dependence*, J. Math. Phys. 11 (1970) 437.
