# The 3D jet-level star identity when the first derivatives of the metric do not vanish

Status: analysis, not a result. The statement `JetStarCore g m` is proved for a Riemannian metric
`g` at a point `m` where all first partial derivatives vanish (`Lightlike/Regge/Conv3/FlatStarJet.lean`).
The convergence of the 3D Regge action needs it at every hinge, in the chart of the grid, where
`∂g(m) ≠ 0`. This note records why the direct proof is out of reach and a route that avoids it.

## Numerical and exact evidence that the statement is true

For random jets `(g, ∂g, ∂∂g)` with `∂g ≠ 0` the angle sum of every class is `2π`, the first-order
coefficient is `0`, and `Σ_k |e_k| c₂(k) = -(R/2) √det g` to 1e-10 (`scripts/regge/regge3d_jet.py`).
In exact rational arithmetic the identity holds for every one of the 36 basis directions of `∂∂g`
(about 8 s each) and for the monomial `(∂₀ g₀₀)²` of the quadratic form in `∂g`.

## Why brute force is out of reach (MEASURED)

The part quadratic in `∂g` has 171 coefficients, rational functions of the 6 entries of `g(m)`.
For the single monomial `(∂₀ g₀₀)²`:

* sympy over `Q(g₀₀, …, g₂₂)`: 701 s;
* as a polynomial in `g`, the six inverse face polynomials `P_α⁻¹`, the seven inverse hinge lengths
  `a_k⁻¹` and `det⁻¹` (sympy `ring`): 0.5 s and 36 952 terms;
* clearing all denominators of that coefficient: 5 842 s (about 97 minutes), with maximal exponents
  `2` for each `P_α⁻¹`, `4` or `5` for each `a_k⁻¹` and `1` for `det⁻¹`.

A polynomial identity of that size for each of 171 coefficients is not a feasible `ring1` target.

## A route that avoids clearing the denominators

A vertex `k` of the star (a lattice vector relative to the hinge midpoint) displaced to
`ε k + ε² Γ(k, k)/2`, with `Γ = Γ(m)` the Christoffel symbols of `g` at `m`, gives in the *flat* metric
`G = g(m)` the squared length of the edge with midpoint offset `s` and vector `Δ`
`ε² (Δ·GΔ + ε ∂_s g(Δ, Δ) + ε² |Γ(s, Δ)|²_G)`, because `2 Δ·G Γ(s, Δ) = ∂_s g(Δ, Δ)`. This is exactly
the `ε³` coefficient `c` of the edge polynomial; the `ε⁴` coefficient `r` of the edge polynomial is the
sum of `|Γ(s, Δ)|²_G` and a term `ρ` that is linear in the second derivatives, `ρ = r_flat(dd')`
with `dd' = ∂∂g` minus an explicit quadratic expression in `(G, ∂g)` (the second derivatives in the
chart `x ↦ x + Γ(x, x)/2`, in which the first derivatives vanish).

1. **Edge level (A1).** The identity `c = 2 Δ·GΓ(s,Δ)` is exact. For the `ε⁴` coefficient, a cubic
   term in the displacement is not needed: in exact rational arithmetic, for random jets, there is a
   unique symmetric `S` (symmetric in `(k,l)` and in `(i,j)`, 36 unknowns) with
   `r(s,Δ) = |Γ(s,Δ)|²_G + ½ Δ·S(s,s)·Δ + (1/24) Δ·S(Δ,Δ)·Δ` as polynomials in `(s, Δ)`; the naive
   mismatch of the chord term `-(1/12)|Γ(Δ,Δ)|²` against `|Γ(Δ,Δ)|²` is absorbed by `S`. `S` is `∂∂g` plus
   an explicit combination of 18 terms of the form `g^{ab} ∂_p g_{qa} ∂_r g_{sb}`,
   `g^{ab} ∂_a g_{pq} ∂_r g_{sb}`, `g^{ab} ∂_a g_{pq} ∂_b g_{rs}` over index permutations of `(k, l, i, j)`
   (`scripts/regge/` does not carry this fit yet; it matched the unique solution on four independent
   random jets). Moreover `2 Rnum(G, S)/det²` equals the scalar curvature of the jet (checked exactly on
   one jet). The remaining work is to prove these two identities for all jets: polynomial identities of
   degree at most 4 (A1) and a rational identity with `det` as the only denominator (A4), in the
   variables `(G, ∂g, ∂∂g)` and, for A1, `(s, Δ)`; estimated size a few 10⁴ terms each, one `ring1`
   each (minutes).
2. **Displaced flat star (A2).** For any positions of the vertices of the star in a flat metric, the
   dihedral angles of each class add up to `2π` as long as the orientation stays positive. The proof of
   `StarAngle.lean` (a fan around the hinge axis, complex coordinate in the plane quotient) gives
   `Σ ∈ 2πℤ ∩ (0, nπ)`; continuity in `ε` from the lattice configuration fixes the value `2π`. Hence
   `Σ Dsq(L'(ε)) = 2π` for small `ε`, and differentiating twice gives
   `Σ Dh(q, c) = 0` and `Σ (Dh(q, |Γ|²) + ½ D²Dsq(q)(c, c)) = 0` for every class. No algebra in `∂g`.
   Estimated size: 300 to 500 lines of Lean, no heavy `ring1`.
3. **Perturbation (A3).** `Dh` is linear in its direction, so
   `angC₂(g, ∂g, ∂∂g) = angC₂(displaced flat) + Dh(q, ρ) = Dh(q, ρ)`: the second-order coefficient is
   that of the flat case of `FlatStarJet.lean` with `dd'` in place of `dd`. `first_order` follows
   from A2. Estimated size: 100 lines.
4. **Curvature (A4).** The flat identity `flat_star_identity` is stated for arbitrary symmetric
   `dd`, so it applies to `S`. It remains to show that `2 Rnum(G, dd') / det²` is the scalar curvature
   of the jet `(G, ∂g, ∂∂g)`: `scalarCurvature_jet` gives the right side explicitly and the identity is a
   rational identity in `(G, ∂g, ∂∂g)` with `det` as the only denominator after using `G⁻¹ = adj/det`.
   Estimated size: some 10⁴ terms, one `ring1` (minutes); this is the transformation of the scalar
   curvature at a point under `x ↦ x + Γ(x,x)/2`.

Total: no step needs more than one polynomial identity of moderate size, in contrast to 171 identities of
10⁶ terms. The expected cost is dominated by A2 (new geometry in Lean).

## Fallback: one hinge at a time with the inverses kept as atoms

Prove for each of the seven edge classes separately, with `P_α⁻¹`, `a_k⁻¹`, `det⁻¹` as atoms and the
relations `P_α P_α⁻¹ = 1` used through `linear_combination`. The 36 952-term polynomial of one
coefficient is spread over the classes (at most about 10⁴ terms per class and monomial), but there are
171 monomials and the certificate (the quotient by the relations) is as large as the clearing of
denominators. Estimated total: 7 × 171 identities of 10³ to 10⁴ terms; not recommended.
