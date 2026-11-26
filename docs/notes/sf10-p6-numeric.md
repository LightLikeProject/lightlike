# SF10, T-SF10-P6: numerical test of the gap `Re S ≤ -δ` outside a compact set

**Question.** Is `Re S` of the Lorentzian vertex action bounded away from 0 outside a compact set of
`SL(2,ℂ)^4 × (ℂ²)^10`? If not, the non-compact tail of `lorVertex_farRemainder_tail` has no exponential
suppression from `Re S` alone.

**Script.** Not committed (a new file under `scripts/` fails the tooling self-test); numpy and scipy, seed 0, about 100 lines. Parameters are listed below.
`Re S = Σ_e k_e log triReal_e` (`Lightlike/Asymptotics/Lorentzian/Action.lean`) depends only on the boundary spinors, not on `p`.

**Data (ASSUMPTION: generic, not geometric).** Random reference configuration `(X*, z*)`, with `X_4 = 1` as the gauge;
`ξ_src = X*_src^H z / |·|` and `ξ_tgt = -J(X*_tgt^H z / |·|)`. So `max Re S = 0` is attained at the reference, but the
data are not those of a 4-simplex and `dS ≠ 0` there.

**Method.** For rapidity `R` and node `a ∈ {0,1,2,3}`, `X_a = K1 diag(e^{R/2}, e^{-R/2}) K2` with `K1, K2 ∈ SU(2)`.
All other `X_b` (exp of `sl(2,ℂ)`) and all ten `z_e ∈ ℂ²` are free. Maximise `Re S` by L-BFGS-B (numerical
gradient, 3 random restarts, 150 iterations). The `z_e` live on all of `CP¹`, so `w → ∞` is covered.

**Result (MEASURED, sup Re S found per node a = 0..3).**

| R | a=0 | a=1 | a=2 | a=3 | max |
|---|---|---|---|---|---|
| 0 | -0.0117 | -0.0183 | -0.0025 | -0.0001 | -0.0001 |
| 2 | -0.0098 | -0.0001 | -0.0528 | -0.0004 | -0.0001 |
| 4 | -0.0484 | -0.5595 | -0.2682 | -0.0285 | -0.0285 |
| 8 | -0.4225 | -1.3836 | -0.9520 | -0.4153 | -0.4153 |
| 16 | -0.4235 | -1.8052 | -1.0295 | -0.4145 | -0.4145 |

For R ≤ 2 the values sit near 0 (the reference lies in or near that region). For R ≥ 8 the supremum found is about -0.41,
and it is flat between R = 8 and 16: a gap `δ ≈ 0.4` for a single node going to infinity on this data.

**Limits (do not read this as a proof).**
- PROXY: the optimiser gives lower bounds on the true supremum. Local search with 3 restarts could miss a
  higher branch; at R = 0 it reaches only -0.0001, not 0.
- Only one node at a time goes to infinity. Joint degeneration of two or more nodes and degeneration of the
  `z_e` alone are untested (the latter is partly covered, since `z` is free).
- ASSUMPTION: generic data. The interesting case is geometric (4-simplex) boundary data, where degenerate
  sequences might satisfy all `Re S = 0` links; not tested. Analytically, a node going to infinity needs the four
  `Jξ_ba` to be of the form `X_b^† u` for one common `u`, which is overdetermined for generic data but may hold
  for special data.
- The test says nothing about the amplitude or about `Re S = 0, dS ≠ 0` regions, which are inside compact sets here.

## Second test: geometric Lorentzian 4-simplex data and joint degeneration of two nodes

**Data (MEASURED validity).** A random Lorentzian 4-simplex in `ℝ^{3,1}` (five points, time offsets `0.15 N(0,1)`,
spatial parts `N(0,1)³`; all five tetrahedra spacelike, unit future normals `N_a`). Boundary spinor `ξ_ab` is the
coherent spinor of the outward unit normal `n̂_ab` of the face `(a,b)` in the rest frame of the tetrahedron `a`
(`g_a = sqrt(N_a)`, Hermitian matrix model of the Lorentz group); the sign of `n̂_ba` is fixed per link so that
the selfdual bivectors match, `Ad_{g_a}(n̂_ab·σ) = -Ad_{g_b}(n̂_ba·σ)` (checked to 1e-15). With `X_a = (g_4^{-1} g_a^{-†})`, the
gauge `X_4 = 1`, and `z_e = X_src^{-†} ξ`, `Re S = 0` to 1e-15 (seeds 0-3). So the data have a genuine
`Re S = 0` configuration of geometric origin. `dS = 0` was not checked (it needs the areas as spins; `Re S` does not depend on them).

**Method.** As in the first test, but a set of nodes (one, or two of the four free nodes) is sent to rapidity `R` at
the same time; 5 random restarts of L-BFGS-B (150 iterations) per entry; seed 0.

**Result (MEASURED, sup Re S found).**

| R | single node 0 / 1 / 2 / 3 | node pairs 01 / 02 / 03 / 12 / 13 / 23 |
|---|---|---|
| 0 | 0.0000 for all | 0.0000, -0.0001, 0.0000, 0.0000, 0.0000, 0.0000 |
| 4 | -0.626 / -0.188 / -0.212 / -0.026 | -0.911 / -1.252 / -0.786 / -1.086 / -0.625 / -0.424 |
| 8 | -1.736 / -0.497 / -0.770 / -0.580 | -3.009 / -3.646 / -1.761 / -1.891 / -1.300 / -0.957 |
| 16 | -2.688 / -1.489 / -2.365 / -0.603 | -4.176 / -5.053 / -3.290 / -3.853 / -2.091 / -3.100 |

At `R = 0` the search recovers `Re S = 0`, so the optimiser finds the maximum when it exists. For `R ≥ 8` every entry is below -0.57,
and the supremum decreases with `R` (for node 3 alone it has levelled off near -0.6). Some starts overflowed at large `R` and
were discarded by the maximum (`RuntimeWarning` in the log only).

**Limits.**
- PROXY: lower bounds on the supremum (local search, 5 restarts, one simplex, one seed). Two nodes was the largest set tried;
  three or four nodes and the degeneration of the spinors alone are untested.
- `dS = 0`, the second critical point (parity partner) and the amplitude were not examined.
- The script is not committed (tooling self-test); it is the first script plus the simplex construction above.

## Verdict

No `Re S = 0` direction was found at infinity, on generic data (one node) and on geometric 4-simplex data (one and
two nodes). **P6 plausible; proof route:** compactify each `X_a = K1 A(ρ) K2` by its KAK limit, so the boundary at infinity is a compact
set of limit configurations on which `Re S` is upper semicontinuous; show it has no maximiser (a node at infinity forces the four
`Jξ_ba` into one pencil `X_b†u`, which fails for non-degenerate boundary data), then `Re S ≤ -δ` outside a compact set by compactness;
this is where the hypothesis of non-degenerate boundary data enters. Then use `nonstationary_phase` where `Re S = 0, dS ≠ 0`.

## Statement correction (25 Nov 2026)

The integrability clause of `lorVertex_farRemainder_tail` is now for `λ ≥ 1` only (at `λ = 0` the factor `e^{λ S}` is `1` and `A` need not be integrable outside `U`).
Details and the list of changed declarations: `docs/notes/sf10-p3-assessment.md`, last section.
