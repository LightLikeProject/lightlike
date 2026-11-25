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

## Update 25 Nov 2026: route to completeness for smooth sections (milestones)

Chart equations for an arbitrary smooth spinor `g = (g₁, g₂)`: `(1+|z|²) i ∂_z g₂ = λ g₁`, `(1+|z|²) i ∂_{z̄} g₁ = λ g₂`.
In polar form `∂_{z̄} = (e^{iθ}/2)(∂_r + (i/r)∂_θ)`, so the angular modes `g₁ ~ a_m(r) e^{imθ}`, `g₂ ~ b_{m+1}(r) e^{i(m+1)θ}` satisfy
`(1+r²)(i/2)(b' + (m+1) b/r) = λ a` and `(1+r²)(i/2)(a' − m a/r) = λ b`.
Milestones: (M1, Lean, `Dirac/AngularFourier.lean`) the coefficient of the angular derivative of a periodic function is `i m`
times the coefficient (`fcoef_dtheta`), and the radial derivative commutes with taking coefficients (`hasDerivAt_fcoef`);
(M2) chain rule from the chart to polar coordinates and the two mode ODEs for a smooth chart spinor;
(M3) classification of the solutions of the mode ODE that are regular at `r = 0` and decay at `∞` (the polynomial class of
`EigenGeneralK`/`ge5-complete`), which needs a uniqueness statement for the singular linear ODE;
(M4, Lean, done) a continuous spinor component is determined by its Fourier modes (`eq_zero_of_fcoef_polar`: all modes zero ⇒ zero, via Mathlib's Fourier basis on `AddCircle`); M2 is also Lean (`mode_eq_bar`, `mode_eq` in `Dirac/AngularModes.lean`).

### M3 plan (25 Nov 2026): the mode ODE and two candidate routes

With `ν = -2iλ`, `K = 1 + r²`, the mode pair `(a, b) = (c₁_m, c₂_{m+1})` solves `a' = (m/r) a + (ν/K) b`,
`b' = -((m+1)/r) b + (ν/K) a`. Writing `A = r^{-m} a`, `B = r^{m+1} b` gives `K r^{2m+1} A' = ν B` and
`K B' ... = ν r^{2m+1} A`, i.e. the spin-weighted Legendre equation `(K σ A')' = (ν² σ / K) A`, `σ = r^{2m+1}`.
Route 1 (ODE): Frobenius series at `r = 0` (the regular solution is unique up to a scalar, `a ~ r^{|m|}`), then show
that it decays at infinity iff the hypergeometric series terminates, i.e. `λ = ±(k+1)`; the non-terminating case needs the
asymptotics at `t = r² → ∞` (connection formula or a Sturm/Wronskian comparison argument). Route 2 (functional
analytic): the explicit eigenspinors of the lower bound span a dense subspace of `L²`, `D` is symmetric on smooth sections
(integration by parts in the chart with the sphere measure), so an eigenspinor with another eigenvalue is orthogonal to a
dense set, hence zero. Route 2 needs the `L²`/symmetry statement and a Stone–Weierstrass density argument, but no ODE
asymptotics. Both are well above one session; first deliverable for either: regularity of the modes of a smooth spinor at
the origin (`c_m(r) = O(r^{|m|})`).

### M3 route 1, worked out (25 Nov 2026)

For `m ≥ 0` put `a = r^m F(t)`, `b = r^{m+1} H(t)`, `t = r²`, `μ = ν/2`. The mode system becomes
`(1+t) F' = μ H`, `(1+t)(t H' + (m+1) H) = μ F`; the Taylor coefficients satisfy
`(n+1) f_{n+1} + n f_n = μ h_n`, `(n+m+1) h_n + (n+m) h_{n-1} = μ f_n`, so the regular solution is unique up to the scalar `f_0`
(this is the Wronskian statement of `ModeODE.lean`, now with an explicit series; the other Frobenius solution has `a ~ r^{-m}`).
At `t → ∞` the solutions behave as `F, H → const` (non-decaying: `a ~ r^m`) or `F, H ~ t^{-(m+1)}` (decaying: `a ~ r^{-m-2}`).
The regular solution decays iff the coefficient of the first behaviour vanishes; that coefficient is a Gauss-type
connection constant `Γ(c)Γ(c-a-b)/(Γ(c-a)Γ(c-b))` of the hypergeometric function in `x = t/(1+t)`, and it vanishes iff
the series terminates, i.e. `μ = ±(k+1)/2 · …` (the quantisation `λ = ±(k+1)`). Stages for Lean: (S1) the series solution
and its uniqueness (coefficient recurrences above, radius of convergence 1); (S2) the change of variable `x = t/(1+t)` and
the closed hypergeometric parameters; (S3) the value at `x = 1` (Gauss) via the Euler integral and Mathlib's Beta
integral, or via the contiguous relation; (S4) non-vanishing off the quantised set; (S5) assembly with M2, M4 and the
decay at the pole. S3 is the hard part (no hypergeometric function theory in Mathlib).

### M3 route 1, closed form found (25 Nov 2026, S2 and S3 mapped, not yet in Lean)

Eliminating `H` from the series system gives `t(1+t)² F'' + (1+t)((m+2)t + m + 1) F' − μ² F = 0`; its exponents are
`0, −m` at `t = 0`, `±iμ = ±λ` at `t = −1`, `0, −(m+1)` at `t = ∞`, so (Pfaff) the regular solution is
**`F(t) = ₂F₁(λ, −λ; m+1; x)`, `x = t/(1+t) = r²/(1+r²)`**, with `λ = iμ`. Its Taylor coefficients in `x` are
`γ_n = (λ)_n (−λ)_n / ((m+1)_n n!)`, `γ_n ~ n^{-m-2}`, so the series converges at `x = 1` and `F(r → ∞) = S(m+1)` with
`S(c) = Σ_n (λ)_n(−λ)_n/((c)_n n!)`. The solution decays at infinity iff `S(m+1) = 0` (the other behaviour `a ~ r^m` is
non-decaying).
*Elementary evaluation of `S`* (no Gauss theorem needed):
(a) telescoping: with `T_n(c)` the terms, `(c² − λ²) T_n(c+1) − c² T_n(c) = R_{n+1} − R_n`, `R_n = c n T_n(c)`; since
`(N+1) T_{N+1}(c) → 0` for `c > 0`, `(c² − λ²) S(c+1) = c² S(c)`;
(b) base case: `T_n(1) = P_n − P_{n−1}` with `P_n = ∏_{j ≤ n}(1 − λ²/j²)`, so `S(1) = lim P_N = sin(πλ)/(πλ)`
(Mathlib: `Complex.tendsto_euler_sin_prod`);
(c) hence `S(m+1) = S(1) ∏_{j=1}^m j²/(j² − λ²)`, which vanishes iff `λ ∈ ℤ`, `|λ| ≥ m+1`. The integers `1 ≤ |λ| ≤ m`
need one more argument (the series terminates; Chu–Vandermonde gives `S(m+1) = (m+1−j)_j/(m+1)_j ≠ 0`).
This is exactly the quantisation `λ = ±(k+1)`, `k ≥ m`. Remaining Lean work: identify `F` with the `x`-series (ODE for the
`x`-series plus uniqueness from `ModeODE.lean`), Abel's theorem at `x = 1`, the dichotomy decaying / non-decaying at infinity,
and the integer case.
