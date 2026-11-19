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

## Differences

1. Representation: `Â` is a rational function `P/Q`, `Q = Π (z − z_I)` with distinct `z_I` (simple poles), `deg P < deg Q`; this
   encodes the analytic structure of p. 35 and `B_n = 0`, i.e. (3.6), which the source states as an input ("one assumes — or, much
   preferably, proves"); `tendsto_cocompact_zero` proves (3.6) from it.
2. Hypotheses where the source argues from Feynman diagrams: the tree-level analytic structure (rational, simple poles, p. 35, "To see
   this, consider the Feynman diagrams") and the factorization (3.5) of the residues are stated, not derived; the library has no
   Yang-Mills Feynman rules. For the MHV sector the shifted Parke-Taylor amplitude can be checked directly (Elvang-Huang Exercise 3.2–3.3,
   p. 37), which is the Parke-Taylor-by-BCFW item.
