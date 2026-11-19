# G3-073 (factorization on poles): the BCFW shift and the residue formula

Lean: `Lightlike/GR/BCFWFactorization.lean` (on `ColourOrdered.lean`).

## Mathlib check

Partial fractions for simple poles are Lagrange interpolation: `Lagrange.eq_interpolate`, `Lagrange.eval_interpolate_not_at_node`
(`P(x)/Π(x − z_I) = Σ_I w_I P(z_I)/(x − z_I)` with the nodal weights `w_I = Π_{J≠I}(z_I − z_J)⁻¹`), `Lagrange.nodal`,
`Lagrange.nodalWeight_eq_eval_nodal_erase_inv`; `Filter.tendsto_inv₀_cobounded`, `Metric.cobounded_eq_cocompact`. Mathlib has no
general residue theorem; none is needed for rational functions.

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*, §3.1–3.2:
* p. 34: the shift vectors with (i) `Σ rᵢ = 0`, (ii) `rᵢ · rⱼ = 0`, (iii) `pᵢ · rᵢ = 0`, and `p̂ᵢ = pᵢ + z rᵢ` (3.1); "(A) By property (i),
  momentum conservation holds for the shifted momenta".
* p. 35: "(B) By (ii) and (iii), we have p̂ᵢ² = 0, so the shifted momenta are on-shell. (C) … P̂_I² is linear in z: P̂_I² = P_I² + 2z P_I·R_I"
  (3.2), `P̂_I² = −(P_I²/z_I)(z − z_I)`, `z_I = −P_I²/(2P_I·R_I)` (3.3); "We specialize to the case where A_n is a tree-level
  amplitude. In that case, the analytic structure of Â_n(z) is very simple. For example, it does not have any branch cuts … it can have
  only simple poles. To see this, consider the Feynman diagrams: the only places we can get poles is from the shifted propagators
  1/P̂_I²"; Cauchy's theorem `A_n = −Σ Res_{z=z_I} Â_n(z)/z + B_n` (3.4); "at a z_I-pole the propagator 1/P̂_I² goes on-shell. In that
  limit, the shifted amplitude factorizes into two on-shell parts, Â_L and Â_R" (3.5).
* p. 23: the anti-MHV three-point amplitude `A₃[1⁺2⁺3⁻] = [12]³/([23][31])` (2.78) (rendered page checked).
* p. 37: Exercise 3.2 (the large-`z` falloff of (3.9) under a `[−,−⟩` shift), Exercise 3.3 ("Consider the action of a [1, 2⟩-shift of
  (3.9). Identify the simple pole. Calculate the residue of Â_n(z)/z at this pole"); pp. 38–39: the single surviving diagram (3.13), (3.18),
  the three-point amplitude with analytic continuation `|−p⟩ = −|p⟩`, `|−p] = +|p]` (3.14)–(3.15), and the product (3.19)–(3.21).
* p. 36: "Thus, in most applications, one assumes — or, much preferably, proves — that B_n = 0. This is most often justified by
  demonstrating that Â_n(z) → 0 for z → ∞ (3.6). If (3.6) holds, we say that the shift (3.1) is valid (or good)"; the recursion
  (3.7); the BCFW shift `|î] = |i] + z|j]`, `|ĵ⟩ = |j⟩ − z|i⟩` (3.8).

## How each Lean statement matches

* `bcfwSquare`, `bcfwAngle`: (3.8). `conserved_bcfw`: (A). Every shifted momentum is `nullMom` of spinors, hence null (`mdot_nullMom_self`):
  (B). `momSum`, `momSum_bcfw`: `P̂_I = P_I + z r`, `r = −|j]⟨i|`, for `i ∈ I`, `j ∉ I`; `mdot_momSum_bcfw`: (C), (3.2);
  `mdot_momSum_bcfw_eq`: (3.3).
* `residue`, `eval_div_nodal` (partial fractions), `tendsto_residue` (the residue is `lim (z − z_I) Â(z)`), `tendsto_cocompact_zero`
  (`Â → 0` at infinity: (3.6)), `eval_zero_eq_neg_sum_residues`: (3.4) with `B_n = 0`, `Â(0) = −Σ_I Res_{z_I} Â(z)/z`.
* `recursion_of_factorization`: (3.7), given the factorization (3.5) of the residues as a hypothesis.
* The MHV sector (Exercises 3.2–3.3, (3.13)–(3.21)): `ptShift` (the `[1,2⟩`-shifted Parke-Taylor amplitude), `ptShift_eq`
  (`Â(z) = ⟨12⟩⁴/(⟨12⟩⟨2̂3⟩⟨34⟩⋯⟨n1⟩)`, only `⟨2̂3⟩ = ⟨23⟩ − z⟨13⟩` shifted), `ptShift_rational`, `degree_ptShift_numerator` (`P/Q` with one
  simple pole, `deg P < deg Q`), `ptShift_channel` (`P̂₂₃² = ⟨2̂3⟩[23]`: the pole is where `P̂₂₃` goes on shell), `ptShift_onshell`
  (`|2̂⟩ ∝ |3⟩` at the pole), `antiMHV3` ((2.78)), `ptShift_factorization` (the residue of `Â(z)/z` is
  `−Â_{n−1}(1̂⁻,P̂⁻,4⁺,…,n⁺) Â₃(−P̂⁺,2̂⁻,3⁺)/P₂₃²` for every choice of spinors `|P̂]`, `⟨P̂|` of the on-shell `P̂₂₃`, (3.5)). Index
  lemmas: `cycDen_four`, `cycDen_three`, `finRotate_succ_succ_succ`, `finRotate_small`, `finRotate_succ_succ_succ_ne_one`.

## Differences

1. Representation: `Â` is a rational function `P/Q`, `Q = Π (z − z_I)` with distinct `z_I` (simple poles), `deg P < deg Q`; this
   encodes `B_n = 0`, i.e. (3.6), which the source states as an input (p. 36: "one assumes — or, much preferably, proves — that
   B_n = 0"); `tendsto_cocompact_zero` proves (3.6) from it.
2. Weaker (general helicity sectors): the source argues the tree-level analytic structure (rational, simple poles, p. 35: "To see
   this, consider the Feynman diagrams") and the factorization (3.5) from the Yang-Mills Feynman diagrams. Attempts recorded:
   (a) a Feynman-diagram derivation: stopped, the library has no Yang-Mills Feynman rules; (b) the MHV sector: done, for the
   Parke-Taylor amplitude the shifted `Â(z)` is shown to be `P/Q` with a single simple pole where `P̂₂₃` is on shell, and its residue
   factorizes as (3.5) (`ptShift_*`). Colour-ordered tree amplitudes of other helicity sectors are not defined in the library (no
   definition of a non-MHV tree amplitude), so for them the analytic structure and (3.5) remain hypotheses of
   `recursion_of_factorization`.

## Update: the general helicity sectors (`FeynmanRecursion.lean`)

Line 2 above is closed for the colour-ordered amplitudes defined from the Feynman rules (`ColourOrderedFeynman.lean`, note
`g3-073-feynman-amplitudes.md`): their analytic structure (holomorphic off the propagator zeros, simple poles), the factorization
(3.5) of every residue (`residue_shift_factorization`), and the recursion (3.7) for every shift with (3.2)–(3.3) under (3.6)
(`bgAmplitude_eq_sum_channels`) are proved, the latter by partial fractions from Liouville's theorem
(`eq_sum_div_sub_of_residues`), without the rational form `P/Q` of `recursion_of_factorization`.

