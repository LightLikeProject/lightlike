# The Ponzano–Regge model

## Abstract (Alpha)

This API defines the Ponzano–Regge spin foam model of three-dimensional Euclidean quantum gravity
on a triangulated 3-complex, as a weighted sum over spin colourings of the edges with 6j symbols
on the tetrahedra. It proves the behaviour of the model under the 3D Pachner moves, including a
gauge-fixed amplitude in the sense of Freidel and Louapre that is invariant along chains of moves,
and it recognises the triangulations on which the model is a manifold invariant: closed
combinatorial 3-manifolds, whose vertex links are triangulated 2-spheres.

## Content (Alpha)

A 3-complex is a finite set of tetrahedra on a vertex set. A spin colouring of its edges has a
weight built from 6j symbols and dimension factors, and the amplitude sums the weight over all
colourings below a spin cutoff {1} [1]. The Biedenharn–Elliott identity holds for all spins [2].

Under the 2-3 move the weight is invariant once the spin of the new edge is summed, and so is the
amplitude [3]. Under the 1-4 move, summing over the spins of three of the four new edges
multiplies the weight by `(2j+1)²`, where `j` is the spin of the fourth [4]. Because of this
factor the plain amplitude diverges with the cutoff, and the model is gauge fixed: the gauge-fixed
amplitude puts spin `0` on a set of gauge edges and uses edge-wise cutoffs {2} [5]. It is unchanged by a single 2-3 move whose new edge `DE` has cutoff at least the sum of the cutoffs of
the edges `AD` and `AE` [5]. It is constant
along chains of 2-3, 3-2, 1-4 and 4-1 moves whose cutoffs satisfy the moves' compatibility
conditions, also when the gauge set is required to be a maximal tree [5]. The 3-2 and 4-1 moves are
recognised on any complex [6]. Changing the maximal tree by an exchange inside a triangle leaves
the gauge-fixed amplitude unchanged, for every cutoff [7], and when the gauge set forces every
edge the gauge-fixed amplitude is `1` [8], for example on the boundary of the 4-simplex with a star tree [13].
For a finite cutoff the amplitude does depend on the maximal tree on a ring of three tetrahedra, which is not
a manifold, and the two trees are not related by exchanges [14].

A closed combinatorial 3-manifold is a complex in which every vertex link is a combinatorial
2-sphere [9]. These 2-spheres are connected closed pseudo-surfaces of Euler characteristic `2`
[10], and they are exactly the intrinsic triangulated 2-spheres [11]. All four moves preserve
closed combinatorial 3-manifolds, in both directions and along chains [9].

The tetrahedron's squared volume, its dihedral angles and its Regge action are defined from the
edge lengths, and the Ponzano–Regge asymptotic formula for the 6j symbol is stated as a
proposition {3} [12]. Its proof is not yet formalized. [TODO]

## Lean References

1. Lightlike/PonzanoRegge/Amplitude.lean - `PR.Complex3`, `PR.weight`, `PR.amplitude`
2. Lightlike/PonzanoRegge/BEZero.lean - `Pentagon.biedenharnElliott`
3. Lightlike/PonzanoRegge/Unconditional.lean - `PR.weight_move23_unconditional`,
   `PR.amplitude_move23_unconditional`
4. Lightlike/PonzanoRegge/Move14.lean - `PR.weight_move14`, `PR.amplitude_move14`
5. Lightlike/PonzanoRegge/GaugeFixed.lean - `PR.amplitudeGF`, `PR.amplitudeGF_eqvGen`,
   `PR.amplitudeGF_eqvGen_tree`, `PR.amplitudeGF_move23`, `PR.amplitudeGF_move23_tree`
6. Lightlike/PonzanoRegge/InverseMoves.lean - `PR.amplitudeGF_move32`, `PR.amplitudeGF_move41`
7. Lightlike/PonzanoRegge/GaugeChange.lean - `PR.amplitudeGF_exchange`,
   `PR.amplitudeGF_eqvGen_exchange`
8. Lightlike/PonzanoRegge/Forcing.lean - `PR.amplitudeGF_of_forcesAll`
9. Lightlike/PonzanoRegge/Manifold.lean - `PR.IsCombManifold`, `PR.isCombManifold_move23_iff`,
   `PR.isCombManifold_move14_iff`, `PR.isCombManifold_iff_of_eqvGen`
10. Lightlike/PonzanoRegge/SphereInvariants.lean - `PR.IsSphere2.invariants`
11. Lightlike/PonzanoRegge/SphereRecognition.lean - `PR.isSphere2_iff_isSurfaceSphere`
12. Lightlike/PonzanoRegge/Asymptotics.lean - `PR.vol2`, `PR.dihedral`, `PR.reggeAction`,
    `PR.PonzanoReggeFormula`
13. Lightlike/Tests/Forcing.lean - `PR.Test.Manifold.amplitudeGF_S3_star`
14. Lightlike/Tests/TreeDependence.lean - `PR.Test.Ring.amplitudeGF_tree_dependent`,
    `PR.Test.Ring.not_eqvGen_exchange_T1_T2`

## References

1. G. Ponzano, T. Regge, Semiclassical limit of Racah coefficients, in *Spectroscopic and Group
   Theoretical Methods in Physics*, North-Holland, 1968.
2. L. Freidel, D. Louapre, Ponzano–Regge model revisited I: gauge fixing, observables and
   interacting spinning particles, *Class. Quantum Grav.* 21 (2004) 5685.
3. J. Roberts, Classical 6j-symbols and the tetrahedron, *Geom. Topol.* 3 (1999) 21.
