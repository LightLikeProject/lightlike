# GE5: the Dirac spectrum of the unit 2-sphere, multiplicities `2(k+1)` (measured, not proved)

Status: **MEASURED** by exact linear algebra for `k = 0, 1, 2, 3`; **not proved in Lean**. The milestone GE5 stays partial.

## What is in the library

`Lightlike/Dirac/RadialEigen.lean`, `EigenGeneralK.lean` and `ConformalDirac.lean` prove, for every `k`, that radial spinors
`h^{-1/2}(P(1/h) v + Q(1/h) y·v)` (`h = (1+‖y‖²)/2`, `v` a constant spinor, `P`, `Q` real polynomials) satisfy
`D f = ±(k+1) f` for the Dirac operator `D` of the unit 2-sphere in the stereographic chart. For each sign and `k` this gives
a 2-dimensional family (the choice of `v`). The expected multiplicity of `±(k+1)` is `2(k+1)`, so the library covers only
the radial part.

## The computation

Convention (that of the library, `e_i² = -1`): after the conformal reduction of `ConformalDirac.lean`, `f = h^{1/2} g` is an
eigenspinor with eigenvalue `λ` iff `h · D₀ g = λ g`, with `D₀` the flat Dirac operator. In complex coordinates `z = y₁ + i y₂`,
with the Clifford generators acting on `ℂ²` as `i σ₁, i σ₂`, and `w = 1 + z z̄`, the equations are, for `g = w^{-s}(P₁, P₂)`:

`w ∂_z P₂ − s z̄ P₂ = μ P₁`, `w ∂_{z̄} P₁ − s z P₁ = μ P₂`, with `μ = ±i (k+1)`.

Exact kernel dimension over `ℂ`, for `s = k+1` and `P₁, P₂` polynomials in `z, z̄` of total degree at most `d`
(sympy, rank of the coefficient matrix over `ℚ(i)`):

| `k` | `d = k+1` | `d = k+2` | `d = k+3` | `d = k+4` | `d = k+5` | `d = k+6` | `d = k+7` | `d = 2k+3` | expected `2(k+1)` |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 2 | 2 | 4 | | | | | 4 | 2 |
| 1 | 2 | 4 | 4 | 4 | | | | 4 | 4 |
| 2 | 2 | 4 | 6 | 6 | 6 | | | 6 | 6 |
| 3 | 2 | 4 | 6 | 8 | 8 | 8 | | 8 | 8 |

(The rows for `k ≥ 1` are exactly the dimension `2(k+1)` from degree `d = 2k+1` on, and then stay constant up to the degrees
tested. `μ` and `−μ` give the same dimensions.) Other exponents `s` and degrees `d ≤ k + 2` were also searched for `k ≤ 3`;
the only nonzero kernels are those at `s = k + 1`.

## The regularity cut

For `k = 0` and `d = 3` the kernel has dimension 4, more than `2(k+1) = 2`. The extra solutions are expected (ASSUMPTION, not
checked in Lean or by a decay computation) to be singular at the point at infinity of the sphere (the north pole of the
stereographic chart): `w^{-(k+1)} P` with `deg P > 2k + 1` should grow or fail to extend to a smooth spinor there. The eigenspace should be the part regular at infinity; for `k ≤ 3` the solutions with `deg P ≤ 2k + 1` have dimension
exactly `2(k+1)`, which matches the expected multiplicity.

The library states the Dirac operator in the chart only, with no notion of regularity at infinity, so a Lean theorem on the
multiplicity needs that cut stated by hand, for instance as the decay `‖g(y)‖ = O(‖y‖^{-1})` of the spinor `f`, or as the
degree bound above.

## What a Lean statement would need

1. A closed form for the `2(k+1)` independent solutions for every `k`: a two-index analogue of the recurrence `eigA` of
   `EigenGeneralK.lean` for the angular modes `z^a z̄^b`, together with the check that `D f = ±(k+1) f` and linear independence.
   Not found in closed form here; only the kernel dimensions above were computed.
2. The regularity condition at infinity, stated for the chart.
3. For the full spectrum on `S²`: that these are all the eigenvalues and eigenspinors (completeness). This is a separate
   argument (separation of variables or representation theory of `SU(2)`) that is not touched here. Mathlib has no spinor
   bundle on the sphere, so completeness is not available as a library statement.

Estimate for item 1 alone (a lower bound `dim ≥ 2(k+1)` for every `k`): well above the budget of a single row. A finite
statement for `k ≤ 2` with explicit polynomials is possible and would be example-level.

## Provenance

The numbers come from a throw-away sympy script (exact `ℚ(i)` arithmetic) that is not part of the repository. The reference
for the spectrum is Boldt, arXiv:1504.03121, Theorem 3.1 (eigenvalues `±(n/2 + k)`, multiplicity `2^{[n/2]} C(n+k−1, k)`,
which for `n = 2` is `±(k+1)` with multiplicity `2(k+1)`), cited in LL-0293; the table above is a numerical check of the
multiplicity in the chart, not a derivation.
