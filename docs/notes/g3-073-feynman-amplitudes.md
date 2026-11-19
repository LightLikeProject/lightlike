# G3-073 (all helicity sectors): colour-ordered tree amplitudes from the Feynman rules, analytic structure, factorization (3.5)

Lean: `Lightlike/GR/ColourOrderedFeynman.lean` (the definition, `A₃`, the Ward identity for three gluons),
`Lightlike/GR/FeynmanFactorization.lean` (the planar split, the residue on a channel pole, the analytic structure, (3.5)), on
`Lightlike/GR/Polarization.lean` (note `g3-073-polarization.md`).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*:
* p. 17 (after (2.50)): "This does not change the on-shell amplitude A_n, as encoded in the familiar Ward identity p_μ A^μ_n = 0 …
  When summing over all diagrams, the final answer for the amplitude is independent of the choices of q_i."
* p. 21: the Gervais-Neveu gauge Lagrangian (2.64), "The Feynman rules then give a gluon propagator δ^{ab} η_{μν}/p²".
* p. 22: "Feynman vertex rules for calculating the color-ordered amplitudes directly are • 3-gluon vertex
  V^{μ1μ2μ3}(p1, p2, p3) = −√2 (η^{μ1μ2} p1^{μ3} + η^{μ2μ3} p2^{μ1} + η^{μ3μ1} p3^{μ2}), • 4-gluon vertex
  V^{μ1μ2μ3μ4}(p1, p2, p3, p4) = η^{μ1μ3} η^{μ2μ4}. The color-ordered amplitude A_n(12 . . . n) is calculated in terms of diagrams
  with no lines crossing and the ordering of the external lines fixed as given 1, 2, 3, . . . , n. The polarization vectors are given
  in (2.49)-(2.50)."
* p. 23: (2.72) `A₃[123] = −√2[(ε₁ε₂)(ε₃p₁) + (ε₂ε₃)(ε₁p₂) + (ε₃ε₁)(ε₂p₃)]`.
* p. 35: the analytic structure ("it does not have any branch cuts … it can have only simple poles … the only places we can get poles
  is from the shifted propagators 1/P̂_I²"), (3.2) `P̂_I² = P_I² + z 2P_I·R_I`, (3.3) `P̂_I² = −(P_I²/z_I)(z − z_I)`, (3.4), and (3.5)
  `Res_{z=z_I} Â_n(z)/z = −Â_L(z_I) (1/P_I²) Â_R(z_I)`, "at a z_I-pole the propagator 1/P̂_I² goes on-shell. In that limit, the
  shifted amplitude factorizes into two on-shell parts".
* p. 38: (3.15) "the following convention for analytic continuation: |−p⟩ = −|p⟩, |−p] = +|p]".

Checked numerically before the Lean statements (random complex spinors with momentum conservation, script
`.agent/zrm-gen/bg_check.py`): the recursion with the propagator `+η/P²` and these vertices gives `A_n[1⁻2⁻3⁺⋯n⁺]/(Parke-Taylor) = 1`
to 1e−13 for n = 4, 5, 6.

## How each Lean statement matches

* `vertex3`, `vertex4`: the p. 22 vertex rules contracted with the currents of the legs, one leg left open. `momRange`: `P = p_a + ⋯ + p_b`.
* `bgVertexSum`, `bgTable`, `bgCurrent`, `bgCurrent_of_lt`: the planar sum with one off-shell leg, organized as the recursion over
  intervals of consecutive gluons: the current of `a, …, b` is `1/P²` times the sum over the splittings `[a,c][c+1,b]` (three-gluon
  vertex) and `[a,c][c+1,d][d+1,b]` (four-gluon vertex). `bgAmplitude m`: `A_{m+3}[1 ⋯ n]`, the last polarization dotted into the
  amputated current of the others.
* `bgAmplitude_three`: (2.72). `WardIdentity m j`: "p_μ A^μ_n = 0" at the leg `j`, for null momenta with `Σ p = 0` and transverse
  polarizations of the other legs. `ward_three`: proved for three gluons at each leg.
* `bgAmplitude_split` (`FeynmanFactorization.lean`): `A_n = A_n^{(no I)} + (1/P²) A_R(V_I)` for every planar channel `I = {i, …, j}`
  with the last gluon outside (every planar channel or its complement is of this form): `bgCurrentO` replaces the current of `I`,
  `bgCurrentO_collapse` (strong induction on the recursion, via `bgVertexSum_collapse`) shows that the diagrams through `I` are the
  diagrams of the merged labels (`collapse`), `bgAmplitude_lin` gives linearity in the merged polarization.
* `residue_factorization`: at `P = −|P]⟨P|` null, `A_R(V_I) = A_L(−P⁻) A_R(P⁺) + A_L(−P⁺) A_R(P⁻)`; `bgAmplitude_left`
  (`A_L(ε) = ε · V_I`), `completeness_vec`, `epsPlus_neg_right`/`epsMinus_neg_right` ((3.15)), and the two Ward identities.
* `differentiableAt_bgCurrent`, `differentiableAt_bgAmplitude` (holomorphic where no propagator vanishes), `continuousAt_*`;
  `tendsto_residue_channel` (simple pole: `(z − z₀) Â(z) → A_R(V_I)(z₀)/s` when `P̂_I² = s(z − z₀)` and the other propagators are
  nonzero at `z₀`).
* `residue_shift_factorization`: (3.5), for every shift with (3.2)–(3.3) and the other propagators nonzero at `z_I`.

## Differences

1. Representation: the Ward identity `p_μ A^μ_n = 0` is a hypothesis (`WardIdentity`, for the left amplitude at its gluon `−P` and for
   the merged amplitude at the merged gluon). The source states it as an input (p. 17, "as encoded in the familiar Ward identity").
   It is proved for n = 3 at each leg (`ward_three`).
2. Representation: the planar diagram sum of p. 22 is represented by the recursion of the currents over intervals of consecutive gluons;
   the library has no enumeration of planar tree diagrams to compare it with.
3. Convention: `bgAmplitude` does not read the momentum of the last gluon; its open vertex leg carries `−(p_1 + ⋯ + p_{n−1})`, which
   is `p_n` under momentum conservation (assumed wherever it is used).

## Not done (follow-ups)

* The Ward identity for n ≥ 4 (for every n it is the conservation of the off-shell current of the recursion; Berends-Giele 1988, not
  read here).
* That `Â_n(z)` is a rational function of `z` (needed to feed `BCFWFactorization.recursion_of_factorization`, whose input is
  `Â = P/Q` with `deg P < deg Q`); here the analytic structure is holomorphy away from the propagator zeros and simple poles.
