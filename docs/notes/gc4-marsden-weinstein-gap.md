# GC4: what is missing for the Marsden-Weinstein theorem (G3-132 stays partial)

Main has the linear/affine reduction: `reducedForm` (nondegenerate and alternating on `D^⊥/D`, Cannas da Silva Lemma 23.3), `finrank_reducedTangent` (`dim E - 2 dim D`), the isotropy of the orbit at a zero of the moment map, and the circle and second-class-count tests.
The missing piece is Theorem 23.1 of the same source: for a free proper action of a Lie group on a symplectic manifold and a regular value of the moment map, the quotient `μ⁻¹(c)/G` is a manifold and carries a symplectic form.
It needs a manifold structure on the quotient of a free proper smooth action (quotient manifold theorem); neither Mathlib nor Lightlike has it.
Until it exists only the tangent-space statement above is provable, so the row's done-when ("reduction for a free proper action at a regular value") is not met.
Status (24 Nov 2026): leave G3-132 partial, linear/affine only; no torus brick.
