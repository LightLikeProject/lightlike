# G3-074 (all positions): the Parke-Taylor formula for non-adjacent negative-helicity gluons, by BCFW recursion

Lean: `Lightlike/GR/ParkeTaylorAll.lean` (on `ParkeTaylorBCFW.lean`, note `g3-074-parke-taylor-bcfw.md`).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*:
* p. 39: "You may at this point complain that we have only derived the Parke-Taylor formula recursively for the case where the
  negative helicity gluons are adjacent. Try your own hands on the proof for the non-adjacent case." (The source leaves the case to
  the reader; its Section 4 derives all MHV amplitudes by supersymmetry, not read here.)
* p. 37: (3.11), the large-z behaviour of colour-ordered gluon tree amplitudes under a BCFW shift of adjacent lines,
  `[−,−⟩, [−,+⟩, [+,+⟩: 1/z`, `[+,−⟩: z³`, quoted from [17] ("an argument [17] based on the background field method establishes").
* pp. 24–25: (2.80); "1) Cyclic: It follows from the trace-structure that A_n[12 . . . n] = A_n[2 . . . n 1] etc".
* p. 23: (2.77) `A₃[1⁻2⁻3⁺] = ⟨12⟩³/(⟨23⟩⟨31⟩)`.

## The proof

For `A_n[1⁻ ⋯ j⁻ ⋯]` (gluons `0`, `j` here) with `j ≥ 3`, shift the negative gluon `1` and its positive neighbour `2`
(`|1̂] = |1] + z|2]`, `|2̂⟩ = |2⟩ − z|1⟩`; adjacent `[−,+⟩`). In the Parke-Taylor expression only `⟨2̂3⟩` depends on `z`, so a single
channel `{2̂, 3}` contributes; at its pole `|2̂⟩ ∝ |3⟩`, the three-point amplitude is anti-MHV:
`Â₃(−P̂⁻, 2̂⁺, 3⁺)` if `3` is positive (the left amplitude then has its negative gluons at `1̂` and `j`, one position closer), and
`Â₃(−P̂⁺, 2̂⁺, 3⁻)` if `3` is the second negative gluon (the left amplitude is then adjacent, `1̂⁻ P̂⁻`). For the choice
`⟨P̂| = ⟨3|`, `|P̂] = c|2] + |3]`, `c = ⟨12⟩/⟨13⟩`, both factors are `[23]/c` (`antiMHV3_far`, `antiMHV3_two`). The induction on `n`
runs over every position of the second negative gluon (`eq_parkeTaylor_of_bcfw_mhv`), with the adjacent family of
`ParkeTaylorBCFW.lean` as the case `j = 2` (gluon `1` here); any positions `i ≠ j` reduce to this by cyclic relabelling
(`eq_parkeTaylor_of_bcfw_mhv'`, `cycDen_add_right`).

## How each Lean statement matches

* `parkeTaylor_bcfw_far`: the Parke-Taylor amplitudes satisfy the non-adjacent recursion, from `parkeTaylor_bcfw` (the adjacent one)
  and the ratio of the numerators `⟨1j⟩⁴/⟨12⟩⁴` (`parkeTaylor_mul_angleBr`).
* `IsBCFWFamilyMHV`: the three-point amplitudes (2.77) (`three_one`; `three_two` is (2.77) cyclically relabelled), the adjacent
  recursion (3.18) (`rec_one`), and the non-adjacent ones (`rec_two`, `rec_far`).
* `eq_parkeTaylor_of_bcfw_mhv`: `A_n = ⟨1j⟩⁴/(⟨12⟩⋯⟨n1⟩)` for every `j`. `eq_parkeTaylor_of_bcfw_mhv'`: for any `i ≠ j`.

## Differences

1. Representation (as for the adjacent case of `ParkeTaylorBCFW.lean`): a family of MHV amplitudes is a function of the angle spinors in
   colour order, with the three-point seeds and the single-diagram recursions as hypotheses. The recursions encode the validity of
   the shifts (`B_n = 0`): `[−,−⟩` for the adjacent case, the adjacent `[−,+⟩` here, both `1/z` in (3.11), which the source quotes
   from [17] and does not derive (p. 37). The theorem is conditional on that falloff in the same way as the adjacent one.
2. Representation: the negative gluons are at `0` and `j`; other positions by cyclic relabelling of the labels (p. 25, property 1).
