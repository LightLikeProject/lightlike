# Four-dimensional simplicial complexes and Pachner moves

## Abstract (Alpha)

This API provides the combinatorial four-dimensional triangulations on which four-dimensional
spin foam models are defined: pure 4-complexes given by their 4-simplices, with faces of every
dimension, Euler characteristic, boundary, pseudo-manifolds and orientations, and the five 4D
Pachner moves as a single operation that preserves all of these.

## Content (Alpha)

A 4-complex is a finite pure 4-dimensional simplicial complex given by its 4-simplices, and its
Euler characteristic is computed from its faces of every dimension [1]. The boundary of a
5-simplex has Euler characteristic `2` [1].

The five Pachner moves of dimension four {1} are one operation, given by a pair of complementary
faces of a 5-simplex [2]. Applying it twice gives back the complex [2], and it preserves the Euler
characteristic [2] and the property of being a pseudo-manifold [2]. It also preserves orientability,
in both directions [3]. The Ooguri state sum on these complexes and its invariance under the moves
are not yet formalized. [TODO]

## Lean References

1. Lightlike/FourD/Complex.lean - `FourD.Complex4`, `FourD.Complex4.euler4_sphere`
2. Lightlike/FourD/Pachner.lean - `FourD.Complex4.move`, `FourD.Complex4.move_move`,
   `FourD.Complex4.euler4_move`, `FourD.Complex4.isPseudo4_move_iff`
3. Lightlike/FourD/Orientation.lean - `FourD.Complex4.isOrientable_move_iff`

## References

1. U. Pachner, P.L. homeomorphic manifolds are equivalent by elementary shellings,
   *European J. Combin.* 12 (1991) 129.
