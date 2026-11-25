# Four-dimensional simplicial complexes and Pachner moves

## Abstract (Alpha)

This API provides the combinatorial four-dimensional triangulations on which four-dimensional
spin foam models are defined: pure 4-complexes given by their 4-simplices, with faces of every
dimension, Euler characteristic, boundary, pseudo-manifolds and orientations, and the five 4D
Pachner moves as a single operation that preserves all of these.

## Content (Alpha)

A 4-complex is a finite pure 4-dimensional simplicial complex given by its 4-simplices, and its
Euler characteristic is computed from its faces of every dimension [1]. A 4-simplex has face
counts `(5, 10, 10, 5, 1)` and Euler characteristic `1`, and the boundary of a 5-simplex has face
counts `(6, 15, 20, 15, 6)` and Euler characteristic `2` [1]. A complex is closed exactly when it
is a pseudo-manifold without boundary tetrahedra, the boundary tetrahedra through a triangle are
even in number, and the boundary of a 5-simplex is closed [4]. It is coherently oriented [3].

The five Pachner moves of dimension four {1} are one operation, given by a pair of complementary
faces of a 5-simplex [2]. Applying it twice gives back the complex [2], and it preserves the Euler
characteristic [2] and the property of being a pseudo-manifold [2]. It also preserves orientability,
in both directions [3]. The Ooguri state sum on these complexes and its invariance under the moves
are not yet formalized. [TODO]

## Lean References

1. Lightlike/FourD/Complex.lean - `FourD.Complex4`, `FourD.Complex4.euler4_sphere`,
   `FourD.Complex4.euler4_simplex`, `FourD.Complex4.card_faces_simplex`,
   `FourD.Complex4.card_faces_sphere`
2. Lightlike/FourD/Pachner.lean - `FourD.Complex4.move`, `FourD.Complex4.move_move`,
   `FourD.Complex4.euler4_move`, `FourD.Complex4.isPseudo4_move_iff`,
   `FourD.Complex4.isClosed4_move_iff`, `FourD.Complex4.bdryTets_move`
3. Lightlike/FourD/Orientation.lean - `FourD.Complex4.isOrientable_move_iff`,
   `FourD.Complex4.isOrientation_sphere`
4. Lightlike/FourD/Boundary.lean - `FourD.Complex4.isClosed4_iff`,
   `FourD.Complex4.even_card_bdryTets`, `FourD.Complex4.boundary_simplex_closed`,
   `FourD.Complex4.isClosed4_sphere`

## References

1. U. Pachner, P.L. homeomorphic manifolds are equivalent by elementary shellings,
   *European J. Combin.* 12 (1991) 129.
