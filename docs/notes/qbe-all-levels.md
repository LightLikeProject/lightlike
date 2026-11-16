# q-Biedenharn–Elliott at every level: source, conventions and a proof outline

Task T-QU1-P6 (`qBiedenharnElliott_all`). This note records where the identity is stated, how its
conventions map onto `qSixJ` and `Model.BE`, the numerical evidence, and an outline of a proof with the
lemmas it would need. Nothing here is a proof.

## The statement in the library

`Lightlike/TuraevViro/Model.lean`, `Model.BE`, instantiated by `qBiedenharnElliott hr := (tvModel r hr).BE`
(`Lightlike/TuraevViro/TuraevViro.lean`): for all `a b c d e f p q r' : ℕ`

    ∑_{x < r-1} (-1)^((a+b+c+d+e+f+p+q+r'+x)/2) · [x+1] · f a b x c d p · f c d x e f q · f e f x b a r'
        = f p q r' e a d · f p q r' f b c,

with `f = qSixJ r` (doubled spins, `q = e^{iπ/r}`, `[n] = sin(nπ/r)/sin(π/r)`).

## Source

Y. U. Taylor and C. T. Woodward, *6j symbols for U_q(sl₂) and non-Euclidean tetrahedra*,
arXiv:math/0305113, §2.2, equation (5), "the pentagon or Biedenharn–Elliot relation" (VERIFIED by reading the
paper's text): with `z = j12 + j13 + j14 + j15 + j23 + j24 + j25 + j34 + j35 + j45`,

    {j23 j34 j24; j14 j12 j13} · {j23 j34 j24; j45 j25 j35}
        = ∑_{j15} (-1)^z [2 j15 + 1] {j13 j34 j14; j45 j15 j35} · {j12 j24 j14; j45 j15 j25} · {j12 j23 j13; j35 j15 j25},

the sum over the admissible `j15`; it is obtained from the pentagon of Figure 4 of that paper. Their symbols are
the tetrahedron-symmetric 6j symbols with `q = exp(πi/r)`, spins `j` (half-integers) and a sign convention chosen to
agree with the classical symbols (the paper notes the difference of `(-1)^{∑ j_ab}` from the convention without
absolute values of the theta values). The paper attributes the 6j symbols to Kirillov–Reshetikhin and the formulas to
Carter–Flath–Saito; no equation number of those two is read here (UNVERIFIED), so they are not cited.

## Dictionary to `qSixJ` and `Model.BE` (derived by hand, checked below)

Lightlike's `qSixJ r j1 j2 j3 j4 j5 j6` has triads `(j1 j2 j3), (j1 j5 j6), (j4 j2 j6), (j4 j5 j3)`, which is the
arrangement of the paper's `{j12 j23 j13; j34 j14 j24}` (faces 123, 124, 134, 234). With doubled spins
`J = 2 j`: `[2 j15 + 1] = qnum (x + 1)` and `(-1)^z = (-1)^((sum of the ten doubled spins)/2)`. The variables of
`Model.BE` correspond to the paper's as

    a = j12, b = j25, c = j35, d = j13, e = j14, f = j45, p = j23, q = j34, r' = j24, x = j15.

Under it the two symbols of the right side of `Model.BE` are exactly the two symbols of the left side of (5), and
the three symbols under the sum agree with those of (5) after exchanging the upper and lower entries of two
columns, a symmetry of the 6j symbol. A random check of the three pairs (45000 comparisons, 37 nonzero) found no
mismatch; the zero cases agree because the admissibility conditions coincide.

## Numerical evidence

`scripts/tv_check.py` evaluates `Model.BE` as stated for `r = 4` to `8` with all labels, and compares `qSixJ` with an
independent Temperley–Lieb evaluation. A separate sampler (structured so that the right side is admissible; 4000
tuples per level) gives, for `r = 4` to `10`, `max |LHS − RHS| ≤ 9e-16` with 3961 to 4000 nonzero tuples per level,
and a wrong-sign control differs by `2.0` at every level. Uniform sampling of all nine colours finds an
admissible tuple too rarely to be useful. These are numerical checks of the statement, not proofs.

## Outline of a proof for every `r ≥ 2`

1. Reduce to a statement about the terminating `₈φ₇`: with the q-Racah formula `qRacahSum` each 6j symbol is a
   terminating very-well-poised series; the left side times the weight is a double sum over the middle colour and
   the summation index of one 6j symbol.
2. Route A (hypergeometric): collapse the double sum with a transformation of terminating very-well-poised `₈φ₇`
   series (Watson's transformation) followed by a `₆φ₅` evaluation. The library has Jackson's `₆φ₅` sum
   (`jackson_sumT`, and `tDeg_sum` for the degenerate case) and the level-truncation device (`Q^r = 1`, `b ↔ 1/x`,
   `qfact_mul_qfact_reflect`); it has no `₈φ₇` transformation. A statement of Watson's transformation and a proof by the
   same telescoping certificates would be the main new lemma (UNVERIFIED: the equation number of the
   transformation in the standard references is not read here).
3. Route B (orthogonality): the sum rule `Σ_x (-1)^{..}[x+1] {a b x; c d p}{c d x; e f q} = ...` from the proved
   orthogonality (`qOrthogonality_proved`) and the three-term recurrence in `Lightlike/TuraevViro/Reflect`, then the pentagon
   from the sum rule as in the classical derivation. This needs one new two-parameter identity.
4. Finite levels `r = 4` and `r = 5` are already proved (tasks T-QU1-P2 and P4) by exact arithmetic; they are
   consistency checks for any general proof, not part of it.
5. Stop triggers: the recurrence or the transformation needs a certificate of degree above 8; the boundary value
   does not reduce to a quantum-factorial product in a bounded effort; the numerical check fails at some `r ≤ 10`
   (it does not); or a level-truncation case needs a new idea beyond `b ↔ 1/x`.

Consequence: with `qBiedenharnElliott_all`, `turaevViro_move23_of_BE` and `turaevViro_move14_of_BE`
(`Lightlike/TuraevViro/TuraevViroMoves.lean`) become hypothesis-free statements for every `r ≥ 2`.
