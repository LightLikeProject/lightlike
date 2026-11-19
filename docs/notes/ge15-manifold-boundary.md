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
