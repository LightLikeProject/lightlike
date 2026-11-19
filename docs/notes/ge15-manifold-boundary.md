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
