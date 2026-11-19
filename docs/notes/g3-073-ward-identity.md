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

## W2: cyclic invariance and the Ward identity at every gluon

`mdot_bgVertexSum_rotate`: for `p_0 + ⋯ + p_N = 0` and nonvanishing channel propagators, `ε_N · V(0, …, N−1) = ε_0 · V(1, …, N)`
(arbitrary momenta and polarizations otherwise). Derived here: both sides of `Σ_c J(0..c) · V(c+1..N) = Σ_d V(0..d) · J(d+1..N)`
count the vertices on the path from gluon `0` to gluon `N` of the planar trees (by the line on the left, by the line on the right;
`mdot_vertex3_cyc`, `mdot_vertex4_cyc`: the three- and four-gluon vertices are cyclic, using momentum conservation at the vertex);
the terms with a composite line are `P² J·J` on both sides, the remaining terms are the two amplitudes. MEASURED first: the ratio of
the two amplitudes is `1` to 1e−15 for n = 3, …, 7 at random off-shell conserved momenta and random polarization vectors.

`bgAmplitude_rotLabels`: the amplitude is invariant under rotating the labels by one (Elvang-Huang p. 25, property 1, "Cyclic").
`wardIdentity_of_rotPos`, `ward_all`: the Ward identity at every gluon for every number of gluons, from `ward_last` by rotation.
`residue_factorization'`, `bgAmplitude_eq_sum_channels'`: (3.5) on the pole and (3.7) without the Ward hypotheses ((3.7) keeps
the falloff (3.6) as input, as the source states it).

## Differences

None from the sources at the locations read; the off-shell identity and the cyclic invariance are derived, not quoted.
