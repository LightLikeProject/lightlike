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

**Verdict: no counterexample; the gap holds on generic data, inconclusive for geometric data.** Next test, if P6 is
pursued: Lorentzian 4-simplex boundary data (check that `max Re S = 0` and `dS = 0` are reached), joint
degeneration of two nodes, more restarts.
