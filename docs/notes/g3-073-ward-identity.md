# The Ward identity of the colour-ordered Feynman amplitudes for every number of gluons (W1)

Lean: `Lightlike/GR/FeynmanWard.lean` (on `FeynmanRecursion.lean`).

## Sources read

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: p. 17, the Ward identity `p_μ A^μ_n = 0` (stated as known);
  p. 22, the colour-ordered vertex rules (Gervais-Neveu gauge, (2.64), p. 21).
* L. Dixon, *Calculating scattering amplitudes efficiently*, hep-ph/9601359, §3.2: p. 21, the recursion (52) of the off-shell
  current with the Feynman-gauge vertices (53) and `P_{i,j}` (54); p. 22, current conservation (57) `P^μ_{1,n} J_μ(1, 2, …, n) = 0`.

## The result

The currents of the Gervais-Neveu rules are not conserved off shell (MEASURED: `|P·J| ~ 1` at random kinematics,
`.agent/zrm-gen/bg_check.py`). Instead, for null momenta, transverse polarizations and nonvanishing propagators,

  `P_{a,b} · J(a, …, b) = −(1/√2) Σ_c J(a, …, c) · J(c+1, …, b)`   (`mdot_momRange_bgCurrent`).

This identity is derived here (no source read prints it; Dixon's (57) is the Feynman-gauge analogue). MEASURED first: the ratio
`P·J / Σ J·J` is `−1/√2` to 1e−15 for n = 2, …, 6 at random complex kinematics and reference spinors. The result is the Lean proof:
strong induction on the recursion. The induction step (`mdot_momRange_bgVertexSum_step`): `P · V₃ = −√2[(J_L·J_R)(P·P_L) −
(P_L·J_L)(J_R·P)]` (`mdot_vertex3_add`), `P·P_L = (P² + P_L² − P_R²)/2`, the induction hypothesis for `P_L·J_L`, and
`P_L² J_L = (vertices of L)` (`smul_bgCurrent`); the terms over the splittings into three consecutive intervals cancel pointwise
(`split3_cancel`) and those into four cancel pairwise (`split4_cancel`), after reindexing the nested sums (`Finset.sum_comm'`).

Multiplied by `P²` it is a polynomial identity (`mdot_momRange_bgVertexSum`), so at `P² = 0`, with `p_n = −P_{1,n−1}`, it is the
on-shell Ward identity at the last gluon for every `n` (`ward_last : WardIdentity m (m + 2)`).

## Differences

None from the sources at the locations read; the off-shell identity is derived, not quoted. Ward at the other legs needs the
cyclic invariance of the planar sum (next piece, W2).
