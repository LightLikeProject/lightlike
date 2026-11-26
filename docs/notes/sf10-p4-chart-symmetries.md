# T-SF10-P4: does `fixVertexChart` remove the continuous symmetries?

Question: is finiteness of the critical set in the 44 real chart coordinates plausible, or would a residual continuous symmetry make it a manifold (statement false)?

MEASURED (read from the code): `fixVertexChart e x = (gauge (fun a => fixChart 0 ((e x).1 a)), fun k => lorSpinor ((e x).2 k))`
(`Lightlike/Asymptotics/Lorentzian/VertexHaarChart.lean:219`).
- Lorentz gauge: `gauge` sets `X_4 = 1` (`Lightlike/Lorentz/StarBound.lean:80`): the global `SL(2,ℂ)` is fixed.
- `fixChart 0 y` is a chart of `SL(2,ℂ)` by `y ∈ ℂ³` with `y 2 ≠ 0` (`fixDomain`): 4 × 3 complex = 24 real coordinates, no redundancy.
- `z_k = (w_k, 1)` fixes the `ℂ^×` rescaling of each spinor, giving 10 complex = 20 real coordinates. Total 44, as in the paper's gauge-fixed Hessian (BDFHP App. A, 44 × 44).
So the continuous symmetries of the action (global Lorentz, `z_k → c z_k`) are all fixed; the remaining symmetries are discrete (the spin lifts `X_a → -X_a`, 2⁴ of them, and parity).

PROXY: finiteness then follows from the paper's classification (two geometric critical points up to symmetries for Lorentzian 4-simplex data, §5.4.3) only if each critical point is isolated, i.e. the Hessian is nondegenerate (P2) or isolatedness is shown otherwise. The classification in the paper is up to symmetries and does not state isolatedness.
ASSUMPTION: for general nondegenerate closed data (not Regge-like), finiteness is not shown by the paper ("one SU(2) critical point or none"; these are also isolated only up to the Hessian condition).

Verdict: the chart does not make P4 false for symmetry reasons; P4 remains a research statement that the source does not state. Locking is an owner decision.
