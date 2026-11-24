# G3-196: a new written route for the q-Biedenharn–Elliott identity at every level (24 Nov 2026)

TASK: prove `qBiedenharnElliott_all` so that LL-0031 becomes unconditional (every `r ≥ 4`).
QUESTION: which route to the identity is not already closed by a recorded failure, and what is the
cheapest first test that can falsify it?
METHOD (DS-3 record): re-read `docs/notes/qbe-all-levels.md` and `docs/notes/g3-196-attempt3.md`;
alternatives compared below. One alternative chosen: Route D (connection coefficients).
ACCEPTANCE CRITERION: for the chosen route, every new lemma is stated precisely and has a numerical
test that can fail, ordered by cost, before any Lean.
OUTPUT: this note; no Lean.

## What is closed, and why (MEASURED or recorded, not redone)

| Route | Where | Why it does not close |
|---|---|---|
| A: Watson transformation, then one summation | `qbe-all-levels.md` (Route A' count test, Watson certificate) | the left side has up to 4 nested sums, the right side 2; one transformation plus one summation cannot collapse it (3000 tuples at r = 5, 7, 9, 11). The Watson certificate exists numerically (run 2) but proves nothing about BE. |
| B: Racah sum rule plus orthogonality | `qbe-all-levels.md` (Step 5 check) | each pair of the three symbols in the BE sum shares a triad but their other entries are unrelated, so the sum rule applies to no pair; inverting by orthogonality gives BE again (circular). Structural reason (ASSUMPTION): the sum rule and orthogonality are the braiding and unitarity relations of the fusion category; the pentagon is an independent axiom. |
| C: induction in one external colour | `g3-196-attempt3.md` (Route C test) | no `x`-independent order-`k` recurrence for the summand (null vector in 0 of 267 tuples at `k = 1`, r = 9). |
| Rosengren (4.8) as stated | `qbe-all-levels.md` | `R = Σ R·R` has the shape "one coefficient equals a sum of products of two", BE has "product of two equals a sum of products of three"; the paper does not relate them. |

The common point of A, B, C: they use only the *numbers* `qSixJ`. The pentagon is a property of
the *structure* that defines them (associativity of coupling), so a proof has to use that structure.

## Route D: the 6j symbols as connection coefficients in an algebra of symmetric Laurent polynomials

Source: H. Rosengren, arXiv:math/0312310, Sections 2 to 4 (read from the PDF text, see `qbe-all-levels.md`).
Setting (basic case). `P_N` = symmetric Laurent polynomials in `x` of degree `≤ N` (dimension `N+1`).
`h_k(x; a) = (a x, a/x; q)_k`, with the splitting `h_{m+n}(x; c) = h_m(x; c) h_n(x; c q^m)` (eq. (3.4)).
For generic `a, b` the products `h_k(x; a) h_{N-k}(x; b)`, `k = 0..N`, are a basis of `P_N`.
The connection coefficients `R_kl(a, b, c, d; N)` between two such bases are the 6j symbols
(Theorem 3.4: explicit `₁₀W₉`, `q`-Racah polynomials in the basic case).

Why this could give the pentagon. A change of basis between coupled bases of the *same* space is
associative by linear algebra: three successive changes of basis compose to the same matrix however
they are grouped. If the four-fold products `h_{k1}(a) h_{k2}(b) h_{k3}(c) h_{k4}(d)` (using (3.4) to
split the factors) play the role of the four-fold coupling of angular momenta, then BE is the
statement that two groupings of three changes of basis agree, which is the associativity of matrix
multiplication, written in the coordinates of Theorem 3.4. All the analysis is then in the dictionary,
not in the pentagon.

New lemmas, in order:
- D1 (framework, finite linear algebra over a field): the bases, the splitting (3.4), existence and
  uniqueness of `R_kl` for parameters in general position. Elementary; the uniqueness is a dimension
  count in `P_N`.
- D2 (dictionary): `qSixJ r a b c d e f` equals `R_kl` with `a, b, c, d` powers of `q` and `k, l, N`
  linear in the spins, up to normalisation and sign (the twist phase measured in step 4 of
  `qbe-all-levels.md`). Needs the `₄φ₃` form of `qSixJ` (the library has the Racah sum) and Theorem 3.4,
  i.e. Jackson's terminating `₈φ₇` sum (DLMF 17.7.14; the library has `₆φ₅`, `jackson_sumT`).
- D3 (the pentagon in `R`-coordinates): associativity of three changes of basis, with the
  parameter shifts forced by (3.4).
- D4 (truncation): the specialisation `q = e^{iπ/r}` with the sum `x < r - 1`. The generic sum runs
  over all admissible `x`; at the root of unity the symbols with `a + b + x > 2r - 4` are set to zero in
  `qSixJ`. The library's reflection device (`b ↔ 1/x`, `qfact_mul_qfact_reflect`) shows that such terms
  pair up; whether they cancel in the generic identity is exactly what must be checked (see T3).

## Tests, cheapest first (Python, exact or 40-digit arithmetic; each can fail)

- T1 (dictionary, hours): compute `R_kl` at generic `q` by linear algebra in `P_N` for small `N`, and
  find the parameter identification with the library's `qSixJ` (`scripts/tv_check.py: q6j`) by
  searching over `a, b, c, d ∈ {±q^j}`; acceptance: equality up to a factor depending only on the
  triad, for `N ≤ 6`. FAIL means Route D is not about `qSixJ` and is dropped.
- T2 (pentagon shape, hours): at generic `q`, test whether the product of two `R`'s equals the sum of
  products of three `R`'s with the parameter shifts forced by (3.4), including the sign pattern;
  acceptance: relative error `≤ 1e-30`. FAIL here means D3 is not associativity of a basis change and
  the route reduces to (4.8) alone, which is stopped.
- T3 (truncation, hours): evaluate the generic BE sum (all admissible `x`) at `q = e^{iπ/r}` for
  `r = 5, 7, 9`, and compare with the truncated sum. If they agree, D4 is a specialisation argument;
  if not, the extra terms are identified and D4 becomes a separate lemma.

## What exists in the library for Route D

`qOrthogonality_proved` (D2 normalisation), `jackson_sumT` and `tDeg_sum` (the `₆φ₅` case of Jackson),
the Racah three-term recurrences (`Reflect/RacahRecurrence`), the reflection device, the `r = 3, 4, 5` BE
(consistency checks), the `U_q(sl₂)` Hopf algebra (G3-200) for the alternative categorical reading.
Not in the library: the polynomial-space framework (D1), Jackson's terminating `₈φ₇` (D2), the
specialisation argument (D4).

## Route E (recorded, not recommended): the categorical proof

`Rep U_q(sl₂)` at a root of unity modulo the negligible ideal is a fusion category, and the pentagon is a
coherence axiom (Turaev, Chapter VI). The library now has the Hopf algebra; it lacks the representation
category, the quotient, and the identification of the `F`-matrices with `qSixJ` (the `q`-Clebsch–Gordan
coefficients and their orthogonality). That is four milestones, each larger than D1 and D2.

## Decision

Route D, tests T1 to T3 first. The row stays conditional until T1 and T2 pass; if either fails the note
is updated and the row stays open with Route E as the only known structural route.
