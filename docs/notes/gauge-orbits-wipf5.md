# Wipf's Theorem 5 (gauge orbits): source read, and how the library compares

File: `Lightlike/Gauge/Orbits/GaugeOrbits.lean` (and `Tests.lean` next to it).

## Source (read at the locations given)

A. Wipf, *Hamilton's Formalism for Systems with Constraints*, arXiv:hep-th/9312078, read in the
arXiv PDF.
- Section 3.1, page 12: the regularity conditions (the constraints can locally be taken as the
  first coordinates of a regular coordinate system; equivalently their gradients are linearly
  independent on the constraint surface). Section 3.3, page 17: the same is assumed for all
  constraints.
- Section 5.2, page 28, equation (5.22): first-class constraints, `{γ_a, γ_b} = t_ab^c γ_c`.
- Section 5.2, page 30, Theorem 5: "On `Γ_c` the vectors `X_a` generate `M`-dimensional
  manifolds." Proof by the Frobenius integrability condition and (5.27),
  `[X_a, X_b] = -X_{{γ_a, γ_b}} = -t_ab^c X_c + γ_c ω^{μν} ∂_ν t_ab^c ≈ -t_ab^c X_c`; "for
  (q,p)-dependent structure constant ... the null vector fields are integrable only on the
  constraint surface."

## What the library proves

`Lightlike.Gauge.exists_gauge_orbit`: for `C²` constraints `γ_a`, `a : Fin m`, on `X × X` (`X` a
finite-dimensional real inner product space) that are first class with `C¹` structure functions
(`IsFirstClassWith`, Wipf's (5.22)) and whose gradients are linearly independent at `x₀`, there
are `ε > 0` and a map `f` of `(t, x)`, `t ∈ ℝ^m`, with `f (0, x) = x`, such that for every `x` on
the constraint surface within `ε` of `x₀` and every `‖t‖ < ε`: `f (t, x)` is on the constraint
surface, `f` is differentiable at `(t, x)`, and its derivative in `t` is injective with range
the span of the Hamiltonian vector fields `X_a (f (t, x))` (`hamSpan`). So `t ↦ f (t, x)` is an
`m`-dimensional surface in the constraint surface through `x`, tangent to the `X_a`.

Steps: `lieBracket_hamField` (`[X_g, X_h] = hamVec (d{g, h})`, the first equality of (5.27),
from the symmetry of second derivatives as in `PoissonJacobi`),
`lieBracket_constraintField_mem_span` (the weak equality of (5.27) on the surface),
`constraintSet_invariant` (the surface is invariant under fields in the span of the `X_a`, by
Grönwall), and `Lightlike.ODE.exists_integral_manifold_of_involutive_on` (Frobenius for a family
that is involutive on an invariant set).

## Differences from the source (none accepted)

- representation: the phase space is the flat `X × X` with Physlib's Poisson bracket; the source
  has a `2N`-dimensional phase space with a symplectic form `ω`.
- representation: `C²` constraints and `C¹` structure functions; the source says smooth.
- representation: the statement is local, near a point `x₀` where the gradients are independent
  (`x₀` need not lie on the surface); the source assumes regularity on all of `Γ_c` and states the
  result on `Γ_c`. Applying the theorem at each point of `Γ_c` gives the source's statement.
- representation: "generate `M`-dimensional manifolds" is stated as: through each point of the
  surface near `x₀` there is a parametrised surface `t ↦ f (t, x)` in `Γ_c` whose derivative is
  injective with range the span of the `X_a`. The source does not define the term further.
  Why this is representation and not weaker: the source's own reading of the statement is local.
  The proof on page 30 says the Frobenius condition means that the fields "are integrable
  (through each point in Γc there is a surface, the gauge orbit, to wich the Xa are tangent)".
  That is a surface through each point to which the `X_a` are tangent, which is what
  `exists_gauge_orbit` gives; neither the theorem nor its proof states that the orbit is a
  maximal leaf or an immersed submanifold globally.

The library's `IsFirstClass` (brackets vanish on the surface) is not used: Wipf's (5.22) with
structure functions is the hypothesis, as in the source.
