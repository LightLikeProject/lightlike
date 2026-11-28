# Relationship to other projects

Lightlike formalizes published results and states published open problems, each with its source;
outside the exploratory tier it proposes no new theories. It builds on Mathlib and Physlib: Physlib
covers mainstream physics, Lightlike research-level topics, quantum gravity first. General
mathematics belongs in Mathlib or [Tau Ceti](https://github.com/TauCetiProject/TauCeti); material
that fits Mathlib or Physlib is offered upstream ([the candidates](tasks/README.md#upstream)).

Lean projects that overlap directly: [pachner](https://github.com/not-gary/pachner) (Cunningham,
Zach and Friedl, ITP 2026: simplicial complexes and stellar subdivisions, toward Pachner's theorem);
[OSforGFF](https://github.com/mrdouglasny/OSforGFF) ([Douglas et
al.](https://arxiv.org/abs/2603.15770): the 4D Gaussian free field and the Osterwalder–Schrader
axioms); [OSreconstruction](https://github.com/xiyin137/OSreconstruction) (the Osterwalder–Schrader
reconstruction theorem); [grlab](https://github.com/BrandonMYates/grlab) (curvature in coordinates
and exact solutions of Einstein's equations); and [aqft-lean](https://github.com/Deicyde/aqft-lean)
(algebraic quantum field theory, from pseudo-Riemannian geometry and Minkowski spacetime).

The library's simplicial complexes (`SComplex`, `Lightlike/PL/Complex.lean`) are independent of Mathlib's
simplicial complexes; upstreaming them would need a rework.

In the physics literature, the spin-foam and Regge parts follow two lines of work (IDs from the
[catalog](RESULTS.md)). From covariant loop quantum gravity and its EPRL model ([Engle,
Pereira, Rovelli and Livine](https://arxiv.org/abs/0711.0146); review:
[Perez](https://arxiv.org/abs/1205.2019)): the EPRL map's equivariance, isometry and weak
simplicity (LL-0037), its injectivity on intertwiners (LL-0038), its action on coherent states and
the suppression of non-closing coherent intertwiners (LL-0039, LL-0040), and the finiteness of the
Lorentzian vertex ([Engle and Pereira](https://arxiv.org/abs/0805.4696); LL-0046). From Barrett and
collaborators: the large-spin formula of the Euclidean EPRL vertex ([Barrett, Dowdall, Fairbairn,
Gomes and Hellmann](https://arxiv.org/abs/0902.1170); LL-0047), the Barrett–Crane vertex (LL-0052),
the Ponzano–Regge model under Pachner moves ([Barrett and
Naish-Guzman](https://arxiv.org/abs/0803.3319); LL-0025, LL-0026) and area variables in Regge
calculus ([Barrett, Roček and Williams](https://arxiv.org/abs/gr-qc/9710056); LL-0058). The
large-spin formula of the Lorentzian vertex ([Barrett, Dowdall, Fairbairn, Hellmann and
Pereira](https://arxiv.org/abs/0907.2440)) is a conditional result: the vertex as an
oscillatory integral in fixed charts of SL(2,ℂ), with a stationary-phase expansion under named
hypotheses (LL-0135); the rest is in progress (task T-SF10). No catalog entry concerns an EPRL
amplitude of more than one 4-simplex.
