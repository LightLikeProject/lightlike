# PL topology of simplicial complexes

## Abstract (Alpha)

This API develops piecewise-linear topology for finite abstract simplicial complexes in every
dimension, in the stellar setting of Lickorish: links, stars, joins and cones, stellar
subdivisions and welds, bistellar moves, PL spheres and balls, and combinatorial manifolds. Its
main result is Pachner's theorem in stellar form, which is what makes state sums that are
invariant under bistellar moves into invariants of combinatorial manifolds.

## Content (Alpha)

A simplicial complex is a finite family of finite vertex sets closed under taking subsets [1]. The link of a face is defined as usual, and the star of a face is the join of the face
with its link [1]. A stellar subdivision inserts a new vertex in a face, a weld is its inverse, and
stellar equivalence is the equivalence relation they generate {1} [2]. A bistellar move
replaces the star `A * ∂B` of a face `A` by `∂A * B`, and every bistellar move is a stellar
equivalence [3].

A PL sphere is a complex stellar equivalent to the boundary of a simplex, a PL ball is one stellar
equivalent to a simplex, and a combinatorial manifold is a complex whose vertex links are PL
spheres or balls [4]. The boundary of a simplex is a PL sphere and a simplex is a PL ball [4].

Pachner's theorem, stellar version: two closed combinatorial manifolds are stellar equivalent
exactly when they are related by bistellar moves {2} [5]. This is the formulation of Friedl and
Hannes, who state the theorem as "closed combinatorial n-manifolds are bistellar equivalent if and
only if they are stellar equivalent" and prove it without topology {3}. The version with PL homeomorphism in
place of stellar equivalence needs Newman's theorem, which is not yet formalized. [TODO]

The 3-complexes of the Ponzano–Regge API generate simplicial complexes, and its closed
combinatorial 3-manifolds are closed combinatorial 3-manifolds in this sense [6]. The same
construction applies to the 4-complexes of the four-dimensional API, with closed combinatorial
4-manifolds defined by their vertex links [7].

## Lean References

1. Lightlike/PL/Complex.lean - `PL.SComplex`, `PL.SComplex.link`, `PL.SComplex.star_eq_join`
2. Lightlike/PL/Stellar.lean - `PL.SComplex.starAt`, `PL.SComplex.weld`,
   `PL.SComplex.StellarEquiv`
3. Lightlike/PL/Bistellar.lean - `PL.SComplex.bistellar`, `PL.SComplex.StellarEquiv.bistellar`
4. Lightlike/PL/Manifold.lean - `PL.SComplex.IsPLSphere`, `PL.SComplex.IsPLBall`,
   `PL.SComplex.IsCombManifold`, `PL.SComplex.isPLSphere_boundary`, `PL.SComplex.isPLBall_simplex`
5. Lightlike/PL/PachnerMain.lean - `PL.SComplex.pachner`
6. Lightlike/PL/Complex3.lean - `PL.ofComplex3`, `PL.isClosedCombManifold_ofComplex3`
7. Lightlike/PL/Complex4.lean - `PL.ofComplex4`, `PL.IsCombManifold4`

## References

1. W. B. R. Lickorish, Simplicial moves on complexes and manifolds, *Geom. Topol. Monogr.* 2 (1999)
   299.
2. U. Pachner, P.L. homeomorphic manifolds are equivalent by elementary shellings,
   *European J. Combin.* 12 (1991) 129.
3. S. Friedl and J. Hannes, Pachner's theorem, in *MATRIX Annals 2021–22*, MATRIX Book Series,
   Springer (2024).
