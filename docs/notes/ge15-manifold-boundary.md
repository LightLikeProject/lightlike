# GE15: the boundary term of the Einstein–Hilbert variation (plan and source)

## Source read (19 November 2026)

E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
arXiv:0809.4033, section 4 "Review of the Gibbons-Hawking-York term", eqs. (4.1) to (4.4), p. 20.

* (4.1): `16πG S = 16πG (S_EH + S_GHY) = ∫_V dⁿx √−g R + 2 ∮_{∂V} dⁿ⁻¹x √|h| K`.
* (4.2): "Upon varying the action, we arrive at"
  `16πG δS = ∫_V dⁿx √−g (R_{μν} − ½ R g_{μν}) δg^{μν} − ∮_{∂V} dⁿ⁻¹x √|h| h^{αβ} n^μ ∂_μ δg_{αβ}
  + 2 ∮_{∂V} dⁿ⁻¹x √|h| δK`,
  "Here we have used the assumption `δg^{μν} = 0` on `∂V`, which also implies that the tangential derivative
  vanishes on `∂V`".
* (4.3): `δK = ½ h^{αβ} n^μ ∂_μ δg_{αβ}`.
* (4.4): so `16πG δS = ∫_V dⁿx √−g (R_{μν} − ½ R g_{μν}) δg^{μν}`.

So the statement to formalise first is the middle term of (4.2): for a perturbation that vanishes on the
boundary of the region but whose normal derivative does not, the variation of the Einstein–Hilbert action is
the bulk term plus `−∮ √|h| h^{αβ} n^μ ∂_μ δg_{αβ}`.

## What is already proved

`eh_variation_piece` (`PieceVariation.lean`): for a coordinate metric and ANY smooth symmetric perturbation
(no condition on its support), over a compact set `T` (and a measurable set `A`),
`d/dt ∫ √|g_t| (R(g_t) − 2Λ) = ∫ (−√|g| (R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}) h_{αβ} + ∂_ρ (√|g| W^ρ))`,
with `W^ρ = g^{σν} δΓ^ρ_{σν} − g^{ρσ} δΓ^κ_{κσ}` (`Wvec`, regge). The boundary term is the integral of the
divergence `ehFluxDiv`.

## Plan

1. A box in coordinates: Mathlib's divergence theorem is for rectangular boxes
   (`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` and relatives). For `T = [a, b]`:
   `∫_T ∂_ρ (√|g| W^ρ) = ∑_ρ (∫_{face x^ρ = b_ρ} √|g| W^ρ − ∫_{face x^ρ = a_ρ} √|g| W^ρ)`.
   Difference to name: weaker/representation, the region is a coordinate box (piecewise smooth boundary), not
   a region with smooth boundary in a manifold.
2. On a face where `h = 0` (so tangential derivatives of `h` vanish), `√|g| W^ρ n_ρ` reduces to the
   integrand of (4.2), `−√|h| h^{αβ} n^μ ∂_μ δg_{αβ}` up to the conventions (`h` here is the induced metric
   in the source; the perturbation is `δg`).
3. Then the manifold: a region that is a box in one chart.

## Status (19 November 2026)

| Formal statement (Lean) | Source (Dyer–Hinterbichler, arXiv:0809.4033, §4, p. 20) | Match |
| --- | --- | --- |
| `eh_variation_box` (`BoxVariation.lean`): any smooth symmetric `h`, box `[a, b] ⊂ ℝⁿ⁺¹`: `d/dt ∫ √|g_t|(R_t − 2Λ) = −∫ √|g| (R^{αβ} − ½ R g^{αβ} + Λ g^{αβ}) h_{αβ} + ∑_i (∫_{x^i=b_i} − ∫_{x^i=a_i}) √|g| W^i` | (4.2) without the last term (no assumption on `δg` at the boundary is used here) | weaker/representation: coordinate box, boundary term as the flux of `√|g| W` |
| `eh_variation_box_dirichlet` (`BoxDirichlet.lean`): `h = 0` on the boundary hyperplanes ⇒ the boundary term is `∑_i (∫_{x^i=b_i} − ∫_{x^i=a_i}) √|g| (g^{iσ} g^{iν} − g^{ii} g^{σν}) ∂_i h_{σν}` | (4.2), middle term `−∮ √|h| h^{αβ} n^μ ∂_μ δg_{αβ}` | weaker: coordinate box; `h` vanishes on the whole hyperplanes. Representation: integrand in the inverse metric of the coordinates (`−√|h| h^{αβ} n^μ ∂_μ δg_{αβ}` with `n^μ = g^{μi}/√|g^{ii}|`, `h^{αβ} = g^{αβ} − g^{αi}g^{βi}/g^{ii}`, `√|h| = √|g| √|g^{ii}|`; this rewriting is not formalised) |
| `hasDerivAt_ghyDensity`, `ghySlope_eq_neg_ehFlux` (`GibbonsHawkingYork.lean`, `GHYBox.lean`) | (4.3): `δK = ½ h^{αβ} n^μ ∂_μ δg_{αβ}` | match on a coordinate hyperplane: `ghyDensity = 2√|det h| K` for the induced metric and the mean curvature (`ghyDensity_eq_induced`); the statement is `d/dt (2√|h| K) = −√|g| W^i` |
| `eh_ghy_variation_box` (`GHYBoxVariation.lean`): with the Gibbons–Hawking–York term on every face, only the bulk variation remains | (4.4) | weaker: coordinate box; `h` vanishes on the whole hyperplanes; `g^{ii} ≠ 0` everywhere. Representation as above |

## The two attempts (20 November 2026)

**Attempt 1** (coordinate expressions). `eh_variation_box`, `eh_variation_box_dirichlet`,
`eh_ghy_variation_box`, with `K` and `√|h|` given by the coordinate formulas `faceK` and `ghyDensity`.

**Attempt 2** (induced geometry of the boundary; `InducedFace.lean`). The quantities of (4.1), (4.3) are now
derived from the induced metric of the hyperplane `x^i = const`:

* `inducedMetric g i x`: the submatrix of `g x` without the `i`-th row and column;
  `det_faceSub`: `det h = det g · g^{ii}`; `inv_faceSub`: `h^{ab} = g^{ab} − g^{ai} g^{bi} / g^{ii}`;
* `conormal`, `covDerivConormal`, `secondFF`: the unit conormal `n_β = δ^i_β / √|g^{ii}|`, its covariant
  derivative `∇_α n_β = ∂_α n_β − Γ^μ_{αβ} n_μ`, and the second fundamental form `K_{ab} = ∇_a n_b` on
  tangential indices (`secondFF_eq`: `= −Γ^i_{ab} / √|g^{ii}|`);
* `meanCurv`: `K = h^{ab} K_{ab}`; `meanCurv_eq_faceK`; `ghyDensity_eq_induced`:
  `ghyDensity = 2 √|det h| K`.

So the boundary term of `eh_ghy_variation_box` is the Gibbons–Hawking–York term `2 ∮ √|h| K` of (4.1) for the
induced metric and the mean curvature of each face.

**What attempt 2 could not reach, and why.** A region with smooth boundary in a manifold needs a divergence
(Stokes) theorem on that region. The pinned Mathlib has the divergence theorem only for rectangular boxes
(`MeasureTheory/Integral/DivergenceTheorem.lean`: `integral_divergence_of_hasFDerivAt_off_countable` and
variants); there is no divergence or Stokes theorem for domains with smooth boundary or for manifolds with
boundary (searched `Mathlib/MeasureTheory/Integral` and `Mathlib/Geometry/Manifold`). That is the missing
piece.

Current Mathlib: one search on Loogle (`loogle.lean-lang.org`, the search service over a recent Mathlib),
19 November 2026: names containing "stokes": 0 declarations; names containing "divergence": 8 declarations,
all for boxes (`BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` and the
`MeasureTheory.integral_divergence_…` / `integral2_divergence_…` family of
`Mathlib.MeasureTheory.Integral.DivergenceTheorem`). So current Mathlib has no such theorem either, as far
as a search by name shows. Open pull requests of Mathlib were NOT searched (no GitHub
calls).

Differences that remain against Dyer–Hinterbichler (4.2) to (4.4): the region is a coordinate box; the
perturbation vanishes on the whole coordinate hyperplanes carrying the faces; `g^{ii} ≠ 0` (no null faces).

## Next step: a divergence theorem for a domain with regular boundary (source read, 19 November 2026)

L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition; the PDF on S. Sternberg's page at
Harvard), chapter 10 "The integral calculus on manifolds", section 6 "The divergence theorem".

* Definition, p. 419: "`D` is a domain with regular boundary if for every `x ∈ M` there is a chart `(U, α)`
  about `x` … such that one of the following three possibilities holds: (i) `U ∩ D = ∅`; (ii) `U ⊂ D`;
  (iii) `α(U ∩ D) = α(U) ∩ {v ∈ ℝⁿ : vⁿ ≥ 0}`."
* Theorem 6.1 (The divergence theorem), p. 421: for a domain `D` with regular boundary, a density `ρ` (of
  the class `P` of the chapter) and a smooth vector field `X`, `∫_D div⟨X, ρ⟩ = ∫_{∂D} ε_X ρ_X` (6.3), where
  `ε_X = ±1, 0` according to whether `X` points out of `D`, is tangent, or points into `D`.
* Proof, pp. 422 to 423: a partition of unity subordinate to an atlas of charts of the three types reduces
  to `supp ρ ⊂ U` for one chart; case (i) is trivial; case (ii) is an iterated integral over a large box
  (the function vanishes outside `α(U)`); case (iii) is the same on a half-space, with one boundary term.

This is the route planned for the Lean statement on `ℝⁿ`: charts flattening the boundary, a partition of
unity, and Mathlib's divergence theorem for boxes in cases (ii) and (iii). Nothing of it is formalised yet.

## Attempt 3 (19 November 2026): a general conormal and the region bounded by a graph

Files `ConormalAlg.lean`, `ConormalGHY.lean`, `GHYGraph.lean`, tests `TestsGHYGraph.lean`.

| Formal statement (Lean) | Source (Dyer–Hinterbichler, section 4, p. 20) | Match |
| --- | --- | --- |
| `ghyDensityOf g ν ∂ν x = 2 √|g| h^{αβ} (∂_α ν_β − Γ^μ_{αβ} ν_μ)`, `h^{αβ} = g^{αβ} − N^α N^β / N²`, `N^α = g^{αβ} ν_β`, for a boundary `{u = 0}` with `ν = du` | the density `2 √|h| K` of (4.1) | representation: written with the conormal `du` of a defining function and the coordinate volume of adapted coordinates with unit Jacobian (`√|h| = √|g| |N|`, `K = h^{αβ} ∇_α ν_β / |N|`); no unit normal, no induced metric on the boundary manifold |
| `ghyDensityOf_single` (test): for `ν = e_i`, `∂ν = 0` it is `ghyDensity` of attempt 1 | — | consistency |
| `conormal_flux`, `conormal_hup` (`ConormalAlg.lean`), `ghySlopeOf_eq_neg_flux`: at a boundary point where `h = 0` and `∂_τ h_{ab} = ν_τ k_{ab}`, the slope of the density of `g + t h` is `−√|g| W^ρ ν_ρ` | (4.2) to (4.4): the variation of the boundary term cancels the normal-derivative term of the bulk variation | same, pointwise, for any conormal |
| `pd_of_vanishing_on_graph` (`GHYGraph.lean`): a function vanishing on a `C²` graph has `∂_τ H = ν_τ ∂_i H` there | "`δg_{μν} = 0` on the boundary" is used in this way | supporting |
| **`eh_ghy_variation_graph`**: for `h` smooth with support in a compact `T`, vanishing on the graph of `γ ∈ C²`, on the region `E` above (`σ = 1`) or below (`σ = −1`) the graph, `d/dt|₀ [∫_{E∩T} √|g_t| (R_t − 2Λ) − σ ∫_S 2√|h_t| K_t dy] = −∫_{E∩T} √|g| h_{ab} E^{ab}` | (4.1) with (4.4) | see below |

Differences of `eh_ghy_variation_graph` from the source:

* weaker: the region is bounded by one global `C²` graph in `ℝⁿ⁺¹` (a coordinate patch), not a general region
  of a manifold with smooth boundary. With `exists_graphRegion_of_defining_function` and the partition of
  unity of `ge15-divergence.md` the step to a domain with regular boundary remains to be written.
* hypothesis: the boundary is nowhere null (`N² ≠ 0`), as in the source (space-like or time-like boundary).
* representation: the boundary integral is over a compact set `S ⊆ ℝⁿ` of graph parameters that contains
  the projection of the support of `h`; outside it the integrand does not depend on `t`.
* convention: the sign `−σ` is the orientation (`du` is the inward conormal of the region above the graph);
  no factor `1/16πG`.
* stronger: no coordinate box, no coordinate hyperplane (the restrictions of attempts 1 and 2 are removed).

### A domain covered by graph charts (`GHYDomain.lean`)

**`eh_ghy_variation_cover`**: for a measurable `D ⊆ ℝⁿ⁺¹` with a finite atlas of graph charts and cut-off
functions `ρ_a` (as in `integral_divergence_of_graph_cover`), `∑_a ρ_a = 1` near the points of `D ∩ T`, and
`h` vanishing on each graph near the support of `ρ_a`:
`d/dt|₀ [∫_{D∩T} √|g_t| (R_t − 2Λ) − ∑_a σ_a ∫_{S_a} ρ_a 2√|h_t| K_t dy] = −∫_{D∩T} √|g| h_{ab} E^{ab}`.
The sum is the boundary term `∫_{∂D} 2√|h| K` of (4.1) in the graph charts with the partition of unity.
Supporting: `pd_of_eventually_vanishing_on_graph`, `ghyGraph_add_smul`, `eh_variation_region`.

**`eh_ghy_variation_regular`** (`GHYRegular.lean`, with `exists_graph_atlas` of `GraphAtlas.lean`): if every
point of the closure of `D` has a neighbourhood `U` in which `D` is the region above or below a `C²` graph or
all of `U`, and in the first two cases the graph is nowhere null in `U` and `h` vanishes on it in `U`, then
such an atlas and partition exist and the same formula holds. The hypotheses of `eh_ghy_variation_cover` on
`h` and on the graphs are needed only for the boundary charts (`σ_a ≠ 0`) and on the supports of the `ρ_a`.

Differences from the source: weaker: `ℝⁿ⁺¹`, not a manifold. representation: the boundary is given locally by
graphs (from defining functions by `exists_graphRegion_of_defining_function`), the boundary term is the sum
over the graph charts with a partition of unity; no unit normal and no surface measure. hypothesis: the
boundary is nowhere null, as in the source. convention: sign of the outward orientation, no `1/16πG`.
