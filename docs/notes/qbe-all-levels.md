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

## Step 4 resolved numerically: the quantum Racah sum rule carries a twist phase (MEASURED; no Lean yet)

Search (Python only). (1) The library's `qSixJ` has the 24 tetrahedral symmetries (column permutations and the exchange of upper and lower
entries in two columns): 400 admissible tuples at each of `r = 7` and `r = 9`, 24 images each, no mismatch. So symbols are searched
up to these symmetries: 30 classes of arrangement of six labels instead of 720 permutations. (2) Searched space: second symbol over the 30
classes of `{a, b, c, d, x, q}`, right-hand side over the 30 classes of `{a, b, c, d, p, q}`, weight `[x+1]` or `1`, alternation of the sign
between consecutive `x` (on or off), and a twist phase `exp(iπ s c_x / r)` with `c_x = x(x+2)/4` (doubled spin `x`, `c = j(j+1)`) for
`s ∈ {0, ±1/4, ±1/2, ±1, ±2}`, requiring equal magnitudes on 40 to 150 admissible tuples. Result at `r = 5` to `9`: a single class
survives, the DLMF arrangement `{a b x; d c q}` with weight `[x+1]`, alternating sign and twist `s = ±1`; no combination without the twist survives.
(3) The overall phase was then fitted over coefficient vectors in `{-1, -1/2, 0, 1/2, 1}` for the `c_j` of `a, b, c, d, p, q`: exactly one fits,
`(1, 1, 1, 1, -1, -1)`.

The identity (with `u = e^{iπ/r}`, `c_J = J(J+2)/4` for a doubled spin `J`, `f = qSixJ r`):

    ∑_{x < r-1}  (-1)^((x+p+q)/2) · [x+1] · u^{c_x} · f a b x c d p · f a b x d c q
        =  u^{c_a + c_b + c_c + c_d - c_p - c_q} · f a c q b d p        (terms with x+p+q odd omitted: they vanish).

Check: unrestricted random tuples (no admissibility assumed; both sides vanish when a triad is inadmissible), 60000 per level at `r = 4, 5, 7, 9`:
maximum `|LHS - RHS|` is `4.6e-16`, `3.4e-16`, `2.8e-16`, `5.9e-16`, with 121, 52, 19, 29 tuples having a nonzero right side; the same identity with
`u^{-c}` in place of `u^{c}` also holds (complex conjugation); the control without any twist differs by `1.1` at `r = 7`. A tuple-sampler that restricts
to admissible tuples gives hundreds of nonzero cases per level at `r = 5` to `10` with errors at most `1.5e-15` (see the fit script outline above).
The twist exponents `c_j` are those of the twist/braiding of `U_q(sl₂)`: ASSUMPTION about their origin, unverified against a source; the identity itself is
measured. The classical limit `r → ∞` is DLMF (34.5.15) (read on the page): the phases `u^{c}` tend to `1`.

Consequence for the chain. Step 4 is now a precise statement, to be proved (not assumed). Its Lean form needs a complex-valued weight (`Complex.exp` of
`I * π * c_x / r`, or `uC r ^ c` with the half-integer `c` written as `uC r ^ (J (J+2))` over `4`: use `u^{c_x} = (u^{1/4})^{J(J+2)}`; a fourth root of `u` is `e^{iπ/(4r)}`, so state it with
`Complex.exp`). It is a Racah-type sum of two q-6j symbols that Watson's transformation (step 1) with the `₄φ₃` form (step 3) should evaluate; the twist
phase is the factor that makes the arguments of the two series combine. The derivation of the pentagon from it (step 5) is still not written; the classical derivation
uses this identity and orthogonality, and the twist phases must cancel in the pentagon; stop trigger: if they do not cancel by a one-line computation, report.

## Step 5 check: the chain does NOT close from Racah plus orthogonality (stop trigger reached; no derivation written)

Question: does the pentagon (`Model.BE`, Taylor–Woodward eq. (5)) follow from the twisted Racah rule (step 4), orthogonality and the 24 symmetries?

What was tried (Python only). (i) The pair of symbols that Racah's rule handles must share a triad and have bottoms that are a permutation of each other,
`{a b x; c d p} · {a b x; d c q}`. In the pentagon sum the three symbols `{a b x; c d p}`, `{c d x; e f q}`, `{e f x; b a r'}` pair up as follows: the first two share the triad
`(c d x)` but their other entries `(a b p)` and `(e f q)` are unrelated; the first and the third share `(a b x)` but their bottoms `(c d p)` and `(f e r')` are unrelated; the last
two share `(e f x)` with unrelated remaining entries. So the rule cannot be applied to any pair of the three symbols as it stands. (ii) The rule can be inverted with
orthogonality (the matrix `√([x+1][p+1]) {a b x; c d p}` is orthogonal in `x, p`; the sign `(-1)^((x+p+q)/2)` splits into factors depending on `x`, `p`, `q` once the
parities, which are fixed by the tuple, are fixed): this expresses one 6j symbol as a sum over a new colour of two others, the Racah expansion. Substituting it into
one factor of the pentagon makes a double sum whose `x`-sum still contains three symbols, so the reduction is circular. A quick numerical test of the inverted expansion with a
naive sign gave no match (differences up to `1.1`); the sign bookkeeping above was not carried through, so that test is inconclusive and is not evidence either way.

Structural reason (ASSUMPTION, not checked against a source): in the categorical reading the twisted Racah rule is the relation between the 6j symbols (the F-matrices) and the braiding
(hexagon type), and orthogonality is unitarity of F, while the pentagon is an independent axiom of the fusion category. Relations of the first kind do not imply the
second in general. The known derivations of the Biedenharn–Elliott identity in the classical case go through recoupling of four angular momenta (DLMF §34.5(vi) lists the Racah sum rule (34.5.15)
and the Biedenharn–Elliott identity (34.5.16) as separate "sum rules"; the page was read through a summariser), not from the Racah sum rule alone. The Racah rule is plausibly the case of the pentagon with
one spin zero, i.e. the implication goes from the pentagon to the Racah rule, not back (not checked numerically here).

Consequence. The recorded trigger applies: step 5 as "pentagon from step 4 plus orthogonality" is not a viable plan. Steps 1 (Watson), 3 (`₄φ₃` form) and 4 (twisted Racah) remain true and useful
tools for a different route:
 - Route A', direct: write both sides of `Model.BE` with step 3 as terminating balanced `₄φ₃` series, so the left side is a double sum (over `x` and over the summation index of one 6j symbol) and the right side
   a product of two `₄φ₃`; collapse the sum over `x` by a transformation of very-well-poised `₈φ₇` type (Watson, step 1, or Bailey (17.9.16)) and a `₆φ₅` or `₈φ₇` summation (Jackson (17.7.14), (17.7.16)).
   The structure is that of the classical proofs of the Biedenharn–Elliott identity by hypergeometric transformations (UNVERIFIED reference). Next numerical step, Python only: check that the
   double sum collapses as described for a few small cases.
 - Route B', representation-theoretic: U_q(sl₂) at a root of unity and the fusion category (Turaev's book, Chapter VI; the pentagon is a coherence axiom there); too large for the library today.
Not widened: the search for further Racah-type rules was stopped as agreed.

## Route A' count test: one transformation plus one summation is not enough (stop trigger; no derivation written)

Question: does the x-sum of the pentagon, with each 6j symbol written as a balanced `₄φ₃` (step 3), collapse under one transformation of DLMF §17.9
(Watson (17.9.15) or Bailey (17.9.16)) plus one summation (Jackson (17.7.14) or a `₆φ₅`)?

Count (MEASURED, Python only; structured sampler as above; 3000 admissible tuples at each of `r = 5, 7, 9, 11`). A term of the left side of `Model.BE` is a sum
over `x` of a product of three 6j symbols, each itself a terminating series (length `n_i = min B - max A`, `n_i ≥ 1` for a nontrivial series). The maximum number
of nontrivial nested sums on the left is `4` at every level (`x` plus the three symbol series), seen in 1, 9, 40, 81 of the tuples at `r = 5, 7, 9, 11`;
the right side, a product of two 6j symbols, has at most `2` (two series). A transformation of Watson or Bailey type exchanges one single series for another
(it removes no sum), and one summation removes one. So at least two sums must be removed beyond what one transformation and one summation can do, in any
tuple with all three left series nontrivial. The collapse therefore needs a second summation or a second identity (for example a summation of a double
series, or an identity of Bailey-transform type), which is outside the list allowed for this test.

Second observation: as a function of `x` the summand is a product of three `₄φ₃` series in `x` (three different q-Racah polynomials), not a q-hypergeometric term, so
no single series transformation acts on the `x`-sum directly.

Recorded: Route A' is not a one-transformation-plus-one-summation argument. What it would need is not determined here. No further identity was searched, as agreed.
The classical proofs known to the author of this note go through recoupling (UNVERIFIED), not through a single hypergeometric collapse.

## Rosengren, arXiv:math/0312310: what it proves, and whether it is a route (read from the PDF text; no build, no derivation)

The ID is right: H. Rosengren, "An elementary approach to 6j-symbols (classical, quantum, rational, trigonometric, and elliptic)", arXiv:math/0312310 (v1, Dec 2003),
open access. It was read from the PDF text (`pdftotext`), not through a summariser.

(1) The Biedenharn–Elliott identity is NOT in the paper: a text search for "Biedenharn", "Elliott", "pentagon", "sum rule" and "Racah identity" finds only a bibliography entry. The
paper builds the 6j-symbols as connection coefficients `R_kl(a, b, c, d; N; q)` between two bases of products `h_k(x; a) h_{N-k}(x; b)` and `h_l(x; c) h_{N-l}(x; d)` (eq. (3.6)),
with `h_k(x; a) = (a x, a/x; q)_k` in the basic case. What it states and proves, with the equation numbers of the paper:
 - orthogonality of the coefficients, (4.1), in the q-Racah case (2.18) (an inversion of (2.16)), (2.7) in the rational case;
 - Theorem 3.4: existence, uniqueness and the explicit formula for `R_kl` as a `₁₀W₉` series (very-well-poised `₁₀φ₉`); in the basic case it reduces to the q-Racah polynomials (4 phi 3);
 - Corollary 4.4, eq. (4.8): **convolution formulas**
   `R^{k+j}_{l}(a,b,c,d; M+N) = Σ_{m+n=l} R^{k}_{m}(a q^{αj}, b q^{β(N-j)}, c, d; M) · R^{j}_{n}(a q^{(1-α)k}, b q^{(1-β)(M-k)}, c q^m, d q^{M-m}; N)`
   for `α, β ∈ {0, 1}`, proved by comparing coefficients after splitting `h_{m+n}(x; c) = h_m(x; c) h_n(x; c q^m)` (eq. (3.4));
   its n-fold form (4.10) and the case `M_i = 1` (4.11), the "combinatorial formulas".
 The convolution (4.8) is an addition formula for the connection coefficients and may be the pentagon in disguise, but the paper does not say so and it is NOT checked here whether (4.8) is equivalent to `Model.BE`.

(2) Chain of identities the paper's proofs use: (a) the splitting (3.4), elementary; (b) the expansion (3.6) and its uniqueness for generic parameters (a dimension count in the space of
symmetric Laurent polynomials); (c) the "generalized binomial theorem" (3.9), which the paper says is solved by Jackson's `₈W₇` summation ([GR1] = Gasper–Rahman, and Jackson's paper; equation numbers not
read here); (d) Theorem 3.4, whose proof applies (3.9) twice; (e) Corollary 4.4 by coefficient comparison. Jackson's `₈W₇` summation is DLMF (17.7.14), read and numerically checked above.

(3) Status in the library: steps 1 (Watson), 3 (`₄φ₃` form) and 4 (twisted Racah) are not used by this proof at all. New: (i) the basis and connection-coefficient framework `h_k(x; a)`, with
the uniqueness statement; (ii) Jackson's terminating `₈φ₇` summation (the library has only the `₆φ₅` case); (iii) the identification of `R_kl` with `qSixJ` at `Q = e^{2πi/r}` including the
truncation at the level `r` (the paper's parameters are generic); (iv) the derivation of `Model.BE` from (4.8), which the paper does not give. That is at least three new identities or
constructions, so by the rule agreed for this note the route is recorded and stopped.

Recorded options (no commitment): the second paper to read for a direct proof of the pentagon is the one Rosengren cites for the connection-coefficient view of the Biedenharn–Elliott identity if any
(none found in this text); and the relation of (4.8) to the pentagon could be tested numerically first, in the basic case at generic `q`, before any Lean statement.

## Watson's transformation: the certificate search (Python only, exact rational arithmetic; no Lean)

Setting. `L_n` is the terminating very-well-poised `₈φ₇` side of DLMF (17.9.15) and `R_n` the prefactor times the balanced `₄φ₃` side, both with the terminating parameter `q^{-n}`,
generic rational `q, a, b, c, d, e` (`q = 3/2`, the others random fractions with numerators and denominators in `11..97`), exact `Fraction` arithmetic.

Findings.
 - Exactness: `L_n = R_n` exactly (equality of rationals, not floats) for `n = 0, …, 6`.
 - Recurrences (linear algebra over ℚ, unknown polynomial coefficients in `x = q^n`, nullspace dimension 1): `L_n` and `R_n` each satisfy a recurrence of order 2 with coefficients of degree 4 in `x`
   (nothing of order 1 or 2 with degree below 4; orders up to 3 and degrees up to 8 were searched). They are the same recurrence, as they must be.
 - Dependence of the normalised recurrence coefficients on one parameter at a time (rational-function reconstruction from 26 to 34 exact points): degree at most `(1, 1)` (numerator, denominator) in each of `b, c, d, e`,
   and a polynomial of degree 4 in `a`.
Both are inside the stop rules (order at most 3, degree at most 8). What was NOT done: the Zeilberger certificate `R(n, k)` of each sum, which is what a Lean proof by induction on `n` needs (the
method of `jackson_sumT`: a telescoping identity in `k`, then `L_{n+2}, L_{n+1}, L_n` combined by the recurrence, then the base cases `n = 0, 1`). The certificate has to be found symbolically in the five parameters and `q`,
and then verified by `field_simp; ring` in Lean; the coefficient degrees above suggest it is not out of reach in principle, but the symbolic size (several variables, order 2) is the real cost and was not measured.

Priority. Watson's transformation is a tool for route A' of the pentagon, which stopped at the count of nested sums (above). Without a derivation of the pentagon from steps 1, 3 and 4, proving step 1 does not
yet advance q-Biedenharn–Elliott; it is worth doing only together with a route that uses it. Recorded, not continued.

### Watson certificate: result of run 2 (22 Nov 2026)

 - MEASURED (a local script `watson_gosper.py` (not in the repo), exact Fractions, n = 30): numeric Gosper on `F_k = p0 t_k(n) + p1 t_k(n+1) + p2 t_k(n+2)` (p_i from the order-2 recurrence, degree 4 in x) gives partial sums `G_k` with `sum F = 0`; `R_k = G_k / t_k` is a rational function of `y = q^k` of degree (5, 5). Denominator factors over Q: `(1 - y/(qx)) (1 - y/(q^2 x)) (1 - a q x y) (1 - a y^2)`. The factor `(1 - a y^2)` was missing from the earlier guesses, which is why they found nothing.
 - MEASURED (a local script `watson_cert.py L 4 6` (not in the repo), `DSUB=0,1,2,7`): with that denominator the Zeilberger ansatz (N of degree <= 6 in x, <= 6 in y) has nullspace dimension 1 on 104 random exact points with 64 unknowns, i.e. a certificate exists for the sampled (q, a, b, c, d, e).
 - NOT done: the certificate as a closed form in the five parameters and q (what `field_simp; ring` in Lean needs), the R side, and the route from Watson to the pentagon. The "Route A' count test" above still says Watson alone does not close the pentagon.

## Route C: Temperley–Lieb recoupling (dictionary measured; the development already exists beyond `main`)

Plan (layers, risky one first): (1) the 6j symbol as the evaluation of a tetrahedral network of Jones–Wenzl projectors and trivalent vertices, equal to `qSixJ`; (2) the pentagon from associativity of the fusion of projectors; (3) level truncation at `r` (the projector `p_n` is undefined from `n = r - 1`, where `d_{r-1} = 0`); (4) the move theorems from `turaevViro_move23_of_BE`, `turaevViro_move14_of_BE`.

MEASURED (Python, `qSixJ` re-implemented from `QSixJ.lean`, Kauffman–Lins tetrahedron formula with `theta` and `[n]` conventions): for the faces `(j1 j2 j3), (j1 j5 j6), (j4 j2 j6), (j4 j5 j3)` of `qSixJ r j1 … j6`, with the Kauffman–Lins labels `A = j1, B = j2, C = j3, D = j5, E = j6, F = j4` (faces `(A D E), (B E F), (C D F), (A B C)`),

    | qSixJ r j1 … j6 | = | Tet(A, B, C, D, E, F) | / sqrt(| θ(j1,j2,j3) θ(j1,j5,j6) θ(j4,j2,j6) θ(j4,j5,j3) |),

where `Tet = (I!/E!) Σ_{max a_i ≤ z ≤ min b_j} (-1)^z [z+1]! / (Π [z - a_i]! Π [b_j - z]!)`, `a_i` the four face half-perimeters, `b_j` the three sums of the four edges omitting a pair of opposite edges (`B+C+D+E`, `A+C+E+F`, `A+B+D+F`, halved), `I! = Π_{i,j} [b_j - a_i]!`, `E! = Π [edge]!`, and `θ(a,b,c) = (-1)^{m+n+p} [m+n+p+1]! [m]! [n]! [p]! / ([m+n]! [n+p]! [m+p]!)`. Maximum deviation of the magnitudes: `6.7e-16` (r = 4, 191 nonzero tuples), `3.3e-16` (r = 5, 102), `3.3e-16` (r = 7, 75). The sign convention of `qSixJ` against the net evaluation is not fixed by this check. A first version of the script put the wrong quadrilateral sums in `b_j` (the pairs omitted must be opposite edges) and failed by `1.0`: the faces and the opposite-edge pairs are what fix the dictionary.

State of the Temperley–Lieb development (corrected). On `main`, `Lightlike/TemperleyLieb` ends at `vertex_norm` (existence of `κ`). The development of the same route in `docs/notes/g3-196-route-f.md` is further: its modules `Kappa.lean` (`vertex_norm_value`: `p_c (nestCap Q nestCup) p_c = kapRec a b i · p_c`, with `kapRec a b (i+1) = lamRec a b (i+1) · kapRec (a-1) (b-1) i`), `FusionIdentity.lean` (the fusion identity `Q(a,b) = Σ_i E_i`), `Recoupling.lean` (the recoupling coefficients of the two bracketings of three blocks, with row sums `1`) and `Pentagon.lean` (the five bracketings of four blocks and the relations between them), are not yet on `main`, about 8.7k lines. What none of them contains is the identification of these recoupling coefficients with `qSixJ` (the Racah sum, including the twist phase) and the truncation at level `r`: that is milestone F4 of that note, and then the pentagon gives `qBiedenharnElliott_all` (F5). An earlier version of this section said the layers (a) to (c) were all absent and estimated several thousand lines; that was wrong about the state and is withdrawn.

### Route C, attempt 2 (superseded by `Kappa.lean`): the first vertex norms and where an independent attempt stopped

Proved in `Lightlike/TemperleyLieb/VertexNorm.lean` (the vertex norm `κ(a, b, i)` of `vertex_norm`, the scalar with
`p_c (cap-nest · p_a p_b' · cup-nest) p_c = κ p_c`, `c = a + b - 2 i`, `d_n = chebD δ n`, `δ = loopVal q`):
 - `vertex_norm_one_one`: `κ(1, 1, 1) = δ`; `vertex_norm_two_one`: `κ(2, 1, 1) = δ - δ⁻¹ = d_2 / d_1`.
 - `cap_jwAt_cup`: closing the last strand of `p_{n+1}` with a cap and a cup gives `(d_{n+1} / d_n) p_n` (from `jw_partial_trace`, with `e_n = cup_n cap_n` and the zigzags `cap_{n+1} cup_n = 1 = cap_n cup_{n+1}` cancelled by `cap_cup_cancel`, and `jwAt_comm_cup`).
 - `vertex_norm_succ_one`: `κ(n + 1, 1, 1) = d_{n+1} / d_n` for every `n` with `d_n ≠ 0` (the case of one junction arc and one strand on the right).

Where this attempt stopped (general `b`, one junction arc, `i = 1`; the general case is `vertex_norm_value` in `Kappa.lean`, by the eigen-equation `vertex_eigen` instead of the recursion in `b` below). Expanding the right projector by the recursion `p_b = P - (d_{b-2} / d_{b-1}) P e P`, with `P = p_{b-1}` on the first `b - 1` strands of the right leg and `e` on its last two strands, gives (ASSUMPTION: derived on paper, none of it proved in Lean)

    κ(a, b, 1) = κ(a, b - 1, 1) - (d_{b-2} / d_{b-1}) · λ_{a,b},

where the first term is `κ(a, b-1, 1)` because `p_c` absorbs `p_{c-1} ⊗ 1` (so only the vertex `(a, b-1; c-1)` between `p_{c-1}` remains), and `λ_{a,b}` is the scalar with `p_c (cap_{a-1} p_a P e P cup_{a-1}) p_c = λ_{a,b} p_c`. The scalar exists by the same Schur argument as `vertex_norm`, but its value is not given by `jw_partial_trace`: that identity needs `e` flanked by `p_{n+1}` on both sides, while here `P` is not flanked by the cap and cup but meets the junction cap itself, so `P e P` is not of the form `e J e`. Nor does `λ` vanish: `e` is the generator at the last two strands of the right leg, which after the cap sits at `e_{c-2}` (killed by `p_c`), but it is surrounded by `P` on both sides, so `p_c` cannot reach it. Writing `P e P = (P cup_n)(cap_n P)` turns `λ` into a network with a bent strand: the last strand of `P` is bent to the left through the junction.

Smallest next step (not proved, not measured): a rotation lemma, `p_k` with its last strand bent round to the front, between a cup and a cap and `p_c`, is a scalar times `p_c` (the scalar being a ratio of `d_j`, as for `cap_jwAt_cup`); with it, `λ_{a,b}` becomes a product of known partial-trace ratios and the recursion above closes to `κ(a, b, 1) = θ(a, b, a + b - 2) / Δ_{a+b-2}` in the form of Kauffman–Lins, by induction on `b`. Then the general `i` follows by induction on `i` with the same two steps, and layers (2) to (4) of the plan above are still not started. The alternative to the rotation lemma is the θ-recursion: compute the trace of `p_c · vertex · vertex'` as a closed network, reduce it by bubble removal, and read `κ` as `θ / d_c`; that needs a trace functional on the model, which the library does not have.

Status: the closed forms above (`VertexNorm.lean`) are special cases of `vertex_norm_value` and are redundant once `Kappa.lean` is on `main`. What remains of layer (1) is F4 of `docs/notes/g3-196-route-f.md`: the identification of the recoupling coefficients with `qSixJ` and the truncation at level `r`; QU1's items m1 and p1 stay open.

## Route C, step F4: measured dictionary, recursion scheme and truncation (26 Nov 2026)

All MEASURED with a numerical model of the library's operators (`modelE`, `capOp`, `cupOp`, `jwAt`, `Vop`, `Wop`, `UL`,
`ULd`, `UR`, `sh` re-implemented on bit strings, random complex `q`), exact rational arithmetic at `q = 3/2`, or mpmath at
40 digits. Scripts are local (not in the repository).

1. `kapRec q a b i = θ(a, b, a+b-2i) / Δ_{a+b-2i}` (Kauffman–Lins signs), already proved as `kapRec_eq` in `QNumbers.lean`.
2. **`Fc` is the Kauffman–Lins recoupling coefficient**: with `i = a+b-2e`, `D = i+c-2d`, `j = b+c-2f`,
   `Fc q a b c e d f d' = Tet(a,b,c,D,i,j) · Δ_i / (θ(a,b,i) θ(i,c,D))`, where `Tet` has the faces `(a,b,i), (i,c,D), (b,c,j),
   (a,j,D)` and the opposite pairs `(a,c), (b,D), (i,j)`; 342 cases with `a, b, c ≤ 3`, error at most `1.2e-15`, signs included.
3. **Recursion in the third block.** `pentagon` with a fourth block of one strand and `j = 0` collapses (the total-channel
   constraints leave one term on the right and two on the left) to
   `Fc(a,b,c+1,e₀,d₀+g₀,m,i) · Fc(X,c,1,d₀,g₀,0,d₀+g₀) = Σ_{f ∈ {m, m-1}} Fc(b,c,1,f,m-f,0,m) · Fc(a,b+c-2f,1,d',g₀,m-f,i) · Fc(a,b,c,e₀,d₀,f,d')`,
   `X = a+b-2e₀`. The pivot `Fc(X,c,1,d₀,g₀,0,d₀+g₀)` can be chosen nonzero for every target (all `X, c ≤ 6`). The
   Kauffman–Lins coefficient satisfies it exactly (711 of 711 instances in exact arithmetic). It is **not** a termwise
   identity of the `Tet` sums in about a third of the instances; the partial sums divided by a term are products of
   cyclotomic factors (an instance with a four-term sum, checked with SymPy), so a q-Gosper certificate exists. The
   certificate in closed form (variables `q^label`, `Z = q^z`, as in `RacahCert*`) is the next measurement.
4. **The family with a third block of one strand.** In each `2 × 2` block (fixed total `D`): the entry with both channels
   maximal is a vertex-norm ratio, `Fc(a,b,c,e,0,0,e) = κ(a,b+c,e)/κ(a,b,e)` (from `vertex_norm_value`, for every `c`); the
   pentagon with blocks `(a, b', 1, 1)` and `j = 1` gives the column of the lower channel of `(b'+1, 1)` from the blocks at
   `b'` and `b'-1`; the left–right mirror (`reflectOp`, which fixes cups, caps and projectors) turns the expansion of `UR` in
   `UL` for `(a,b,c)` into the expansion of `UL` in `UR` for `(c,b,a)`, so `Fc(a,b,c)` and `Fc(c,b,a)` are inverse matrices,
   which gives the last entry. Not yet proved in Lean.
5. **Truncation at `q = e^{iπ/r}`.** In the generic identity (all middle colours allowed by the triangle conditions), the
   terms with a colour above the level do **not** vanish one by one as `θ → π/r`: they cancel in pairs `x ↔ 2r−2−x`, and the
   term at `x = r−1` vanishes alone (r = 5 to 8, 41 tuples each; the sum of the bad terms is `O(θ − π/r)`). The root-of-unity
   statement therefore needs a pairing lemma for the regularised limits (only `[r]` vanishes among `[n]`, `n < 2r`).

Plan of the layers (stored in the QU1 plan): Kauffman–Lins coefficient and base entries, third-block recursion with its
certificate, `Fc = klCoef` by induction, the pentagon rewritten as `Model.BE` at generic `q = e^{iθ}`, and the limit
`θ → π/r` with the pairing.
