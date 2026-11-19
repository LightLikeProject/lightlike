# GE15: the divergence theorem on a domain with regular boundary (source, status, differences)

## Source read (19 November 2026)

L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6 "The divergence
theorem".

* Definition, p. 419: `D ⊆ M` is a domain with regular boundary if every `x ∈ M` has a chart `(U, α)` with
  (i) `U ∩ D = ∅`, or (ii) `U ⊆ D`, or (iii) `α(U ∩ D) = α(U) ∩ {v : vⁿ ≥ 0}`.
* (6.2), p. 421: in a chart of type (iii), `(ρ_X)_α = |Xⁿ| ρ_α` on `α(U ∩ ∂D)`.
* Theorem 6.1, p. 421: for a domain `D` with regular boundary, a density `ρ` and a smooth vector field `X`,
  `∫_D div⟨X, ρ⟩ = ∫_{∂D} ε_X ρ_X` (6.3), where `ε_X = 1, 0, −1` as `X` points out of `D`, is tangent, or
  points into `D`; (6.4): in a chart of type (iii), `ε_X = −sgn Xⁿ`.
* Proof, pp. 422–423: a partition of unity reduces to three cases: the support is in a chart of type (i)
  (Case I), of type (ii) (Case II), of type (iii) (Case III, by Fubini and the fundamental theorem of
  calculus in the last coordinate).

So in a chart of type (iii) the integrand on the boundary is `ε_X ρ_X = −Xⁿ ρ_α`.

## Status (files in `Lightlike/Spacetime/EHManifold/`)

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `integral_divergence_halfSpace` (`HalfSpaceDivergence.lean`): `∫_{x_i ≥ 0} ∑_j ∂_j F_j = −∫_{ℝⁿ} F_i(y, 0) dy` for `F ∈ C¹` with compact support | Case III of the proof, with (6.2) and (6.4) | same, for `ρ = 1` on `ℝⁿ⁺¹` |
| `measurePreserving_shearFwd` (`ShearMap.lean`), `pd_comp_shearFwd_same`, `pd_comp_shearFwd_succAbove` (`ShearCalculus.lean`) | not in the source | supporting |
| `integral_divergence_graph` (`GraphDivergence.lean`), `integral_divergence_graph_below` (`DomainDivergence.lean`): `∫_{x_i ≥ γ(x')} ∑_j ∂_j F_j = −∫_{ℝⁿ} (F_i − ∑_k ∂_kγ F_{k'})(y, γ(y)) dy`, and with the opposite sign below the graph | Case III in the chart `(y, u) = (x', x_i − γ(x'))`, in which `X^u = F_i − ∑_k ∂_kγ F_{k'}` | same, for a chart of this form |
| `integral_divergence_patch`, `integral_divergence_of_graph_cover` (`DomainDivergence.lean`): localisation with finitely many cut-off functions; Cases I and II are `graphRegion` with `σ = 0` and pieces that do not meet `D` | the reduction by a partition of unity, Cases I and II | same |
| **`exists_graph_atlas_integral_divergence`** (`RegularDomainDivergence.lean`): if every point of the closure of `D` has a neighbourhood in which `D` is the region above or below a `C²` graph or the whole neighbourhood, then for some finite graph atlas and smooth partition of unity `ρ_a`, `∫_D ∑_j ∂_j F_j = −∑_a σ_a ∫_{ℝⁿ} ρ_a (F_{i_a} − ∑_k ∂_kγ_a F_{k'})(y, γ_a(y)) dy` | Theorem 6.1, (6.3) | see the differences below |
| `exists_graph_of_pos`, `exists_graphRegion_of_defining_function` (`DefiningFunction.lean`): if `u ∈ C²` near `x₀`, `u(x₀) = 0`, `du(x₀) ≠ 0`, then `{u ≥ 0}` is near `x₀` the region above or below a `C²` graph (Mathlib's `ContDiffAt.implicitFunction`, strict monotonicity in `x_i`, cut-off by a bump function) | not in the source (a chart of type (iii) is given there) | supporting: the bridge from flattening charts to graph charts |
| **`exists_graph_atlas_integral_divergence_of_defining_function`** (`DefiningFunction.lean`): the same conclusion for `D` that is, near every point `x` of its closure, `{u ≥ 0}` with `u ∈ C²` at `x` and `du(x) ≠ 0` if `u(x) = 0` | Theorem 6.1, (6.3) | see the differences below |

Tests (`TestsDefiningFunction.lean`): `obliqueHalfSpace_regular`,
`exists_graph_atlas_integral_divergence_obliqueHalfSpace` (a half-space bounded by any hyperplane, with the
linear functional as defining function).

Tests (`TestsDivergence.lean`): `graphFlux_zero`, `integral_divergence_halfSpace_of_graphRegion` (the half-space
case is recovered), `slab_locally_graph` and `exists_graph_atlas_integral_divergence_slab` (the hypothesis
holds for the slab `0 ≤ x_i ≤ 1`, with two charts of opposite orientation).

## Differences between `exists_graph_atlas_integral_divergence_of_defining_function` and Theorem 6.1

* weaker: the ambient space is `ℝⁿ⁺¹` with Lebesgue measure, not a manifold with a density. (A density
  `ρ` on `ℝⁿ⁺¹` is covered by applying the theorem to `ρ X`.)
* representation (attempt 2, 19 November 2026; attempt 1 had graph charts as the hypothesis): the domain is
  given near each point of its closure by a defining function, `D = {u ≥ 0}` with `u ∈ C²` and `du ≠ 0`
  where `u = 0`. A chart `(U, α)` of type (iii) of the source gives one: `u = αⁿ`, the last coordinate
  (`x ∈ D ⇔ αⁿ(x) ≥ 0` on `U`, and `dαⁿ ≠ 0` because `α` is a diffeomorphism); a chart of type (ii) gives
  `u = 1`; type (i) does not occur at points of the closure. Conversely a defining function gives a chart of
  type (iii) by the inverse function theorem. The step from a chart to its last coordinate is not written in
  Lean (the statement takes the defining functions as its hypothesis). The reduction of defining functions
  to graph charts is `exists_graphRegion_of_defining_function`.
* representation: the boundary integral `∫_{∂D} ε_X ρ_X` is written out in the graph charts with a partition
  of unity, which is how the source defines the integral of a density over the manifold `∂D`. No surface
  measure and no unit normal appear. Its value does not depend on the atlas and the partition:
  `integral_divergence_of_graph_cover` gives the same left side for every admissible choice.
* representation: the three cases of the source are encoded by a sign `σ_a ∈ {1, −1, 0}` (above the graph,
  below the graph, interior); pieces outside `D` are absorbed in the proof.
* stronger: `F` is `C¹` with compact support, the graphs are `C²`; `D` need not be bounded.

## Use for the boundary term of the Einstein–Hilbert action

Planned next (`ge15-manifold-boundary.md`): the Gibbons–Hawking–York cancellation on the region above a
graph, with the conormal `du = dx_i − dγ`, then on a domain with regular boundary by the same partition.
