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

1. **Edge level (A1), proved.** `Lightlike/Regge/Conv3/ChartChange.lean` proves
   `edgeC_eq_chr` (`c = 2 Δ·g Γ(s,Δ)`) and `edgeR_eq_displaced`
   (`r = |Γ(s,Δ)|²_g + rf (Sdd g m) s Δ`) with
   `Sdd_{kl,ij} = ∂_l ∂_k g_ij - Σ_{ab} g_ab (Γ^a_{ki} Γ^b_{lj} + Γ^a_{kj} Γ^b_{li})`. The chord term
   `-(1/12)|Γ(Δ,Δ)|²` is absorbed by `Sdd`, no cubic displacement is needed, and no hypothesis on `g` is
   used for `r`. The formula for `Sdd` was found by exact solving: the symmetric `S` with
   `r = |Γ(s,Δ)|² + ½ΔS(s,s)Δ + (1/24)ΔS(Δ,Δ)Δ` is unique, and in terms of `g⁻¹ ∂g ∂g` it is `∂∂g` plus
   an 18-term combination, checked in exact rational arithmetic on 29 independent random jets
   (4 for the fit and the first check, 25 fresh ones: no mismatch in any of the 36 entries).
2. **Displaced flat star (A2).** Vertices of the star displaced consistently (the same vertex has the
   same position in every tetrahedron) form a closed fan around each hinge axis. The proof of
   `StarAngle.lean` then gives `Σ ∈ 2πℤ ∩ (0, nπ)` for the dihedral angles of a class, without the
   antipodal trick (that only fixed the multiple for the lattice); continuity in the displacement
   parameter `ε` (the angle sum is continuous where the tetrahedra stay nondegenerate and positively
   oriented, and takes values in a discrete set) fixes it to `2π` for small `ε`. With the uniform
   expansion `dihSq_curve_expansion` of `JetCore.lean`, `Σ_class Dsq(q + εc + ε²r') = 2π` for small `ε`
   and `Σ Dsq q = 2π` give `Σ Dh(q, c) = 0` and `Σ (Dh(q, r') + ½ D²Dsq(q)(c, c)) = 0` (a polynomial in
   `ε` that is `O(ε³)` has zero coefficients), with no algebra in `∂g`. Estimated size: 400 to 600
   lines of Lean (a closed-fan lemma, orientation positivity for small `ε`, the seven classes by the
   generator), no heavy `ring1`.
3. **Perturbation (A3).** `Dh` is linear in its direction, so
   `angC₂(g, ∂g, ∂∂g) = angC₂(displaced flat) + Dh(q, ρ) = Dh(q, ρ)`: the second-order coefficient is
   that of the flat case of `FlatStarJet.lean` with `dd'` in place of `dd`. `first_order` follows
   from A2. Estimated size: 100 lines.
4. **Curvature (A4).** Exact check: `2 Rnum(G, S)/det²` equals the scalar curvature of the jet on 12 independent random jets (no failure). The flat identity `flat_star_identity` is stated for arbitrary symmetric
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

## Statements for the displaced-star step (A2), as they will be written in Lean

All three are elementary and need no literature source beyond the standard facts they use; the
catalogue label is `structural`.

* `closed_fan_sum` (compiles): for `n > 0`, nonzero `z 0, …, z n`, positive orientation
  `Im (conj z_i · z_{i+1}) > 0` and `z n = z 0`, the arguments `arg (conj z_i z_{i+1})` add up to
  `2π k` with `0 < k` and `2 k < n`. Used: `Complex.arg_mul_coe_angle` (Mathlib, `Complex/Arg`) for the
  mod `2π` statement, `Complex.arg_lt_pi_iff` and `arg_nonneg_iff` for the bounds `0 < arg < π`.
* `eventually_eq_of_int_mul` (compiles): a function continuous at `0`, equal to `2π` at `0`, and
  eventually in `2πℤ`, is eventually `2π`. This pins the multiple `k = 1`.
* `coeffs_zero_of_expansion` (compiles): if `F ε = 2π` for small `ε > 0` and
  `|F ε - 2π - a ε - b ε²| ≤ M ε³`, then `a = b = 0`. It is applied to
  `F ε = Σ_class Dsq (q + ε c + ε² r')` with the uniform expansion `dihSq_curve_expansion`
  (`JetCore.lean`, compact set `K = {q}` for each incidence, directions `c` and `r'`): the constant term
  is `Σ Dsq q = 2π` (`jet_angle_sum`), so `a = Σ Dh(q, c)` and `b = Σ (Dh(q, r') + ½ D²Dsq(q)(c, c))`.

Remaining for A2 (not written): the displaced lengths of an incidence are
`qf G (Δ + ε Γ(s, Δ))` (`edgeC_eq_chr`, `edgeR_eq_displaced` give the coefficients), so
`Dsq` of them is `fanAng G w_ε x_ε y_ε` for the displaced vectors (`cosSq_bf` is already stated for
arbitrary vectors); the seven classes are closed fans in the displaced vertex positions
(`V_n = V_0`), and orientation positivity for small `ε` follows from continuity of the triple
product, which is `1` at `ε = 0`.
