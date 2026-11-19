# G3-074: the Parke-Taylor formula by BCFW recursion

Lean: `Lightlike/GR/ParkeTaylorBCFW.lean` (on G3-073's `BCFWFactorization.lean`, which has the shifted Parke-Taylor amplitude
`ptShift`, its single simple pole and the factorization of its residue).

## Source read (pdftotext and rendered pages of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*:
* p. 23: `A₃[1⁻2⁻3⁺] = ⟨12⟩³/(⟨23⟩⟨31⟩)` (2.77) and the anti-MHV `A₃[1⁺2⁺3⁻] = [12]³/([23][31])` (2.78) (rendered page checked).
* p. 37: the Parke-Taylor amplitude (3.9); "We are now going to use the BCFW recursion relations to construct an inductive proof of the
  Parke-Taylor formula (3.9). The formula (3.9) is certainly true for n = 3 … For given n, suppose that (3.9) is true for amplitudes
  with less than n gluons. Then write down the recursion relation for A_n[1⁻2⁻3⁺…n⁺] based on the valid [1, 2⟩-shift" (3.12).
* pp. 38–39: the single non-vanishing diagram (3.13), (3.18) (the other three-point subamplitude vanishes by special kinematics,
  (3.14)–(3.17)); (3.19) with the inductive hypothesis and (2.78); (3.20)–(3.22) "This completes the inductive step … we have then
  proven the Parke-Taylor formula for all n".

## How each Lean statement matches

* `parkeTaylor_bcfw`: (3.18)–(3.22), the Parke-Taylor amplitude equals `Â_{n−1}(1̂, P̂, 4, …, n) Â₃(−P̂, 2̂, 3)/P₂₃²` with the
  Parke-Taylor `(n−1)`-point amplitude, for every choice of spinors of the on-shell `P̂₂₃`; proof: `Â(0) = −Res Â(z)/z` (3.4) and
  `ptShift_factorization` ((3.5) for MHV).
* `antiMHV3_div_channel`: the three-point factor with the propagator for `|P̂] = c|2] + |3]`, `⟨P̂| = ⟨3|`: `c³/⟨23⟩`.
  `cons_eq_comp_succAbove`: the angle spinors of the `(n−1)`-point amplitude are those of `1, 3, 4, …, n`.
* `IsBCFWFamily` (a family of colour-ordered MHV amplitudes with the seed (2.77) and the single-diagram recursion (3.18)),
  `GenericAngles`, `parkeTaylor_three`, `bcfw_step`, `eq_parkeTaylor_of_bcfw`: the induction of p. 37–39: such a family is the
  Parke-Taylor family for nonvanishing brackets.

## Differences

1. Representation: gluons `1, 2, 3, …, n` of the source are `0, 1, …, n − 1`; a family of MHV amplitudes is a function of the
   angle spinors in colour order; the recursion (3.18) is stated for the spinor choice `⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]` of the
   on-shell `P̂₂₃` (`parkeTaylor_bcfw` holds for every choice); the seed (2.77) is a hypothesis of the family (EH: "With the 3-point
   gluon amplitude A₃[1⁻2⁻3⁺] fixed completely by little group scaling and locality", p. 39; G3-073's `three_point_selection`).
2. Scope: the adjacent case `1⁻2⁻3⁺⋯n⁺` (EH p. 39: "we have only derived the Parke-Taylor formula recursively for the case where the
   negative helicity gluons are adjacent").
