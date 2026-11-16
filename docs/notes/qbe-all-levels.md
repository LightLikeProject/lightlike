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
   same telescoping certificates would be the main new lemma. Source (read on the DLMF page): Watson's q-analogue
   of Whipple's transformation, DLMF §17.9(iii), equation (17.9.15), for `n` a nonnegative integer:
   `(aq, aq/(de); q)_n / (aq/d, aq/e; q)_n · ₄φ₃(aq/(bc), d, e, q^{-n}; aq/b, aq/c, d e q^{-n}/a; q, q)
   = ₈φ₇(a, q a^{1/2}, -q a^{1/2}, b, c, d, e, q^{-n}; a^{1/2}, -a^{1/2}, aq/b, aq/c, aq/d, aq/e, a q^{n+1}; q, a² q^{2+n}/(b c d e))`
   (the page does not call the `₄φ₃` balanced; its parameters satisfy the balance condition). The related sum of a
   terminating balanced very-well-poised `₈φ₇`, Jackson's q-analogue of Dougall's `₇F₆(1)` sum, is DLMF equation
   (17.7.14): the series with parameters `a, q a^{1/2}, -q a^{1/2}, b, c, d, e, q^{-n}` and argument `q`, balanced by
   `a² q = b c d e q^{-n}`, equals `(aq, aq/(bc), aq/(bd), aq/(cd); q)_n / (aq/b, aq/c, aq/d, aq/(bcd); q)_n`
   (its subsection letter is not recorded here). Bailey's `₈φ₇` transformation is (17.9.16). The page text was read
   through a summariser; the statements agree with the `₆φ₅` limit (17.7.16) that the library already uses, but an
   independent reading of the printed formulas is still advisable before a Lean statement is fixed.
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

## Second reading of DLMF (17.9.15), term by term, with a numerical check

Notation: `(x; q)_k = ∏_{i<k} (1 - x q^i)`, `(x_1, …, x_m; q)_k = ∏ (x_i; q)_k`, `n ≥ 0` an integer, `q` generic.
The very-well-poised factor of the `₈φ₇` is `(q a^{1/2}, -q a^{1/2}; q)_k / (a^{1/2}, -a^{1/2}; q)_k = (1 - a q^{2k}) / (1 - a)`,
which is the factor in the library's summand `Tj`. Then, term by term, (17.9.15) reads

    ((aq, aq/(de); q)_n / (aq/d, aq/e; q)_n) · ∑_{k=0}^{n}  (aq/(bc), d, e, q^{-n}; q)_k / ((q, aq/b, aq/c, d e q^{-n}/a; q)_k) · q^k

    =  ∑_{k=0}^{n} ((1 - a q^{2k})/(1 - a)) · (a, b, c, d, e, q^{-n}; q)_k / ((q, aq/b, aq/c, aq/d, aq/e, a q^{n+1}; q)_k)
                    · ( a² q^{n+2} / (b c d e) )^k.

Parameters on the left: upper `aq/(bc), d, e, q^{-n}`, lower `aq/b, aq/c, de q^{-n}/a`, argument `q`: the `₄φ₃` is balanced
(product of lower = `q` times product of upper: `aq/b · aq/c · de q^{-n}/a = a q² d e q^{-n} /(bc)` and `q · aq/(bc) · d e q^{-n}`
agree). Parameters on the right: the argument is `a² q^{n+2}/(bcde)` and the upper parameter `q^{-n}` terminates both series.
Jackson's sum (17.7.14) is the case where the right side is balanced, `a² q = b c d e q^{-n}`, i.e. argument `q`.

Independent check (MEASURED, not a reading): both identities were evaluated numerically in 40-digit arithmetic at 20 random complex
parameter sets with `n = 1` to `4`: (17.9.15) as written above, maximum relative error `2e-40`; Jackson's (17.7.14) with `e` fixed
by the balance condition, `1.7e-40`; a control with the argument `q` of the `₄φ₃` replaced by `q²` fails by `1.4` (relative). So the
formulas as written here are correct, whatever the page rendering.

## Kirillov–Reshetikhin and Carter–Flath–Saito: status

UNVERIFIED, and not resolvable from open sources. Kirillov–Reshetikhin (1989) and the book of Carter, Flath and Saito (Princeton,
Mathematical Notes 43) have no free full text; a search finds only bibliographic records and secondary citations. Their equation numbers
stay unread and uncited. The ebook of Carter–Flath–Saito or a library copy is the way to settle it; until then the identity is cited
from Taylor–Woodward, eq. (5), which is read.

## Draft Lean statements (text only; no `.lean` file yet)

```lean
/-- **Watson's q-analogue of Whipple's transformation** (DLMF 17.9.15): a terminating very-well-poised `₈φ₇` series
equals a prefactor times a terminating balanced `₄φ₃` series. `pk x q k = (x; q)_k`. -/
theorem watson_q_whipple {q a b c d e : ℂ} (n : ℕ) (hq : q ≠ 0) (ha : 1 - a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hden : <nonvanishing of the denominators pk q q k, pk (a*q/b) q k, ..., k ≤ n>) :
    ∑ k ∈ range (n + 1), (1 - a * q ^ (2 * k)) / (1 - a) *
        (pk a q k * pk b q k * pk c q k * pk d q k * pk e q k * pk (q ^ n)⁻¹ q k) /
        (pk q q k * pk (a * q / b) q k * pk (a * q / c) q k * pk (a * q / d) q k * pk (a * q / e) q k *
          pk (a * q ^ (n + 1)) q k) * (a ^ 2 * q ^ (n + 2) / (b * c * d * e)) ^ k =
      pk (a * q) q n * pk (a * q / (d * e)) q n / (pk (a * q / d) q n * pk (a * q / e) q n) *
        ∑ k ∈ range (n + 1), (pk (a * q / (b * c)) q k * pk d q k * pk e q k * pk (q ^ n)⁻¹ q k) /
          (pk q q k * pk (a * q / b) q k * pk (a * q / c) q k * pk (d * e * (q ^ n)⁻¹ / a) q k) * q ^ k
```
Proof plan for it: the same telescoping (Wilf–Zeilberger style) certificate method as `jackson_sumT` (`Lightlike/TuraevViro/Reflect/JacksonWZ.lean`),
in the parameter `n` or `e`; stop trigger: a certificate of degree above 8 in `q^n`, or an effort above 4 hours of build time.

```lean
/-- **q-Biedenharn–Elliott for every `r ≥ 2`** (Taylor–Woodward eq. (5); in the library `Model.BE` of `tvModel r hr`): the sum over the middle
colour of three quantum 6j symbols, with the sign `(-1)^((a+b+c+d+e+f+p+q+r'+x)/2)` and the weight `[x+1]`, equals a product of two. -/
theorem qBiedenharnElliott_all {r : ℕ} (hr : 2 ≤ r) : qBiedenharnElliott hr
```
Supporting statements the proof would need, in order: (1) `watson_q_whipple` above; (2) its specialisation at `Q = u²`, `u = e^{iπ/r}`, with the level
truncation device (`Q^r = 1`, `qfact_mul_qfact_reflect`); (3) the q-Racah sum `qRacahSum` as a terminating `₄φ₃` (a rewriting lemma of the
same kind as `Sj_val`, with free third and sixth colours); (4) the sum rule for two q-6j symbols summed over a common colour, obtained from
(1) to (3); (5) the pentagon from the sum rule. Nothing from (3) on is stated precisely yet.

## Steps 3 to 5, stated precisely (conventions, hypotheses, sources, and what is measured)

Conventions. `u = e^{iπ/r}`, `Q = u²`, `[m] = (u^m - u^{-m})/(u - u^{-1})`, `[m]! = ∏_{i=1}^m [i]`, `(x; Q)_k = ∏_{i<k} (1 - x Q^i)`,
doubled spins as in the library, `f = qSixJ r`. For `qSixJ r j1 j2 j3 j4 j5 j6` put the triad sums
`A = ((j1+j2+j3)/2, (j1+j5+j6)/2, (j4+j2+j6)/2, (j4+j5+j3)/2)` and the quadrilateral sums
`B = ((j1+j2+j4+j5)/2, (j2+j3+j5+j6)/2, (j3+j1+j6+j4)/2)` (these are `qRacahSum`'s arguments, `QSixJ.lean:64-70`),
`z0 = max A`, `n = min B - z0`, and let `a'` be the other three entries of `A` after removing one copy of `z0`.

**Step 3 (MEASURED, 4phi3 form of the Racah sum).** The term `t(z) = (-1)^z [z+1]! / (∏_{a ∈ A} [z-a]! ∏_{b ∈ B} [b-z]!)` of `qRacahSum`
satisfies, when `n ≥ 1` and `Q^{z0+2} ≠ 1`,

    qRacahSum r j1 … j6 = t(z0) · ₄φ₃( Q^{z0+2}, Q^{-(b_1 - z0)}, Q^{-(b_2 - z0)}, Q^{-(b_3 - z0)} ;  Q^{1+z0-a'_1}, Q^{1+z0-a'_2}, Q^{1+z0-a'_3} ; Q, Q ),

the argument being exactly `Q` (balanced: the product of the lower parameters equals `Q` times the product of the upper ones). Numerical check: every case with `n ≥ 1` at `r = 7` (8 cases), `r = 9` (120) and `r = 11` (400 sampled): the fitted
argument is `Q` in every case (a single distinct value) and the relative error of the formula is at most `2.2e-15`. When `Q^{z0+2} = 1` (that is
`z0 = r - 2`) the second term vanishes and the sum is `t(z0)`, which the formula also gives (an upper parameter equal to `1`). Source: this
is the standard q-Racah ₄φ₃ in Askey–Wilson form (argument `q`); the library's `Sj_val` is the case `n = 0`. Lean statement: a rewriting lemma
`qRacahSum_eq_phi43` for the data above, proved by `Finset.sum` reindexing `z = z0 + k` and the ratio `t(z0+k+1)/t(z0+k)` expressed with `one_sub_Q_qZ`
(the same device as `rhoT_eq`); hypotheses `2 ≤ r`, the four triads admissible, `n ≥ 1`, `z0 + 2 < r`.

**Step 4 (the Racah sum rule): classical form read, quantum form NOT yet pinned.** The classical sum rule is DLMF §34.5(vi), eq. (34.5.15)
(read on the page, through a summariser): `Σ_j (-1)^{j+j'+j''} (2j+1) {j1 j2 j; j3 j4 j'} {j1 j2 j; j4 j3 j''} = {j1 j4 j'; j2 j3 j''}`; the
Biedenharn–Elliott identity there is (34.5.16), the orthogonality relation (34.5.14). A direct transcription to the library's `qSixJ` (weight
`qnum (x+1)`, sign `(-1)^((x+p+q)/2)`, second symbol `f a b x d c q`, right side `f a d p b c q`) FAILS numerically: on 120 admissible tuples at `r = 7`
the magnitudes agree in only 50, and no exponent `(αa+βb+γc+δd+πp+κq+ξx)/2` with coefficients in `{0,1}` repairs it (MEASURED). So either the
page rendering of the arrangement is wrong or the quantum sum rule needs another arrangement; the precise quantum statement must be found by a
search over the 720 arrangements of the second symbol before any Lean statement is written (script outline: for each arrangement and sign vector,
compare the sum with each of the 720 arrangements of the right side, over tuples with the right side nonzero). This step is OPEN. It is not needed
if the proof goes through the pentagon directly (route A below), and its absence is the reason this note does not claim a complete chain.

**Step 5 (pentagon).** The pentagon is Taylor–Woodward eq. (5) (read), equivalently DLMF (34.5.16) classically; its dictionary to `Model.BE` is in
the section above. Lean statement (the target): `qBiedenharnElliott_all {r : ℕ} (hr : 2 ≤ r) : qBiedenharnElliott hr`. The derivation from step 4 and
orthogonality (the classical argument of Biedenharn and of Edmonds; location UNVERIFIED) is not written down here: it needs the quantum step 4 first.

Status of the chain: step 1 (Watson, stated, checked at 40 digits), step 3 (stated, checked), steps 2, 4 and 5 not yet stated precisely. The chain
cannot be compiled in one go yet. The order of work once a build slot is open: (1) `watson_q_whipple`; (2) `qRacahSum_eq_phi43`; (3) find and check the quantum Racah
sum rule numerically (no build); (4) the derivation of the pentagon; stop if the pentagon derivation needs a second new identity.
