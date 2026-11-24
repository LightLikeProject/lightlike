# G3-196 attempt 3: route search for q-Biedenharn–Elliott at every level (24 Nov 2026)

TASK: prove `qBiedenharnElliott_all` (T-QU1-P6) so that LL-0031 becomes unconditional.
QUESTION: is there a route to the identity, other than a Watson-style certificate, that needs at
most one new two-parameter identity and fits the library?
METHOD (DS-3 record): searched (1) `docs/notes/qbe-all-levels.md` in full outline form, (2) DLMF 17.9
(Watson, Bailey), (3) Rosengren math/0312310 (already read), (4) the library's own recurrence
machinery in `Lightlike/TuraevViro/Reflect`. One alternative chosen below.
ACCEPTANCE CRITERION: a route whose new lemmas are each stated precisely and checked numerically
at r = 4..10 before any Lean.
OUTPUT: this note; no Lean.

## Facts already measured (MEASURED, from earlier runs, not redone)

- Watson's transformation is true and has a numeric Zeilberger certificate (run 2: nullspace
  dimension 1 for 8 values of `a`, denominator `(1-y/(qx))(1-y/(q²x))(1-aqxy)(1-ay²)`). It exchanges
  one series for another; it removes no sum.
- Count test (3000 tuples at each of r = 5, 7, 9, 11): the left side of BE has up to 4 nested sums,
  the right side 2. One transformation plus one summation therefore cannot collapse it. **So finding
  the closed-form Watson certificate would not by itself prove BE.** This is why attempt 2 was a
  detour; recorded so nobody pays for the closed form again without a second identity.
- Rosengren's convolution (4.8) is not shown to be equivalent to BE; the route needs at least three
  new constructions (connection-coefficient framework, Jackson ₈φ₇, identification with `qSixJ` at
  the truncated level) plus the derivation of BE from (4.8). PROXY estimate, not measured.

## The alternative: induction in one external colour (Route C)

Both sides of BE are functions of one external colour `f` (say) over a finite range. The library
proves, at every `r`, the three-term recurrences of the q-Racah sum in the third colour
(`Reflect/RacahRecurrence`, `JacksonWZ`), orthogonality (`qOrthogonality_proved`) and the
`₆φ₅` Jackson sums. Route C: (i) the right side satisfies a second-order recurrence in `f` by two
applications of the 6j recurrence; (ii) the left side satisfies the same recurrence by applying the
6j recurrence termwise and summing by parts in `x` (the boundary terms vanish by the truncation
`x ≤ r-2`); (iii) equality at the two lowest values of `f` from the boundary evaluation
(`QDougallAll`). This is the classical Racah-style proof of BE.

Why it wins over the others: it uses only machinery already proved on main, needs no `₈φ₇`
transformation, and each step is a finite identity of the kind the kernel handles at fixed `r`.

Why it may fail (ASSUMPTION, untested): in step (ii) the shift in `f` acts on two of the three 6j
symbols in the `x`-sum, not uniformly, so the termwise recurrence is of higher order than two and
the summation by parts needs an auxiliary sum. Before any Lean, this must be tested: compute the
left side `L(f)` exactly at r = 7, 8, 9 and check whether it satisfies the order-2 recurrence
whose coefficients are the right side's. If a higher order is needed, the route reduces to a
`two-parameter identity`, which by the old stop trigger means: report, do not build.

## Status and decision needed

This is a research task of milestone size (rated L) and the two routes already studied each fall
short of BE. I have not started Route C numerically in this session. Estimate (PROXY): the
numeric test is under a day; a full Lean proof is several weeks of agent time and probably
exceeds the 3.5 % cap used for run 2. Recommend: run only the numeric test of step (ii), then stop
and report; G3-196 and everything it blocks (G3-197 general r, G3-199, G2-029) stay conditional.

## Result of the Route C numeric test (24 Nov 2026; FAIL)

TASK: test step (ii): does the x-sum of BE admit a termwise recurrence in the external colour `p`
whose coefficients do not depend on `x`?
METHOD: `scripts/research/be_recurrence_test.py R kmax` (mpmath, 40 digits, `q6j` of
`scripts/tv_check.py`). For tuples with at least `k + 2` nonzero `x`-rows, build the matrix
`M[x, j] = t_x(p + 2j)`, `j = 0..k`, and test for a null vector by its smallest singular value.
ACCEPTANCE CRITERION: a null vector in essentially every such tuple at some fixed `k`.

MEASURED (400 sampled tuples per level with `a..f` in the middle third of the colour range, so
many `x` terms survive; BE itself agrees to `<= 7e-41` at `r = 9, 11, 13`):
 - `k = 1`: null vector in 0/267 (r = 9), 5/323 (r = 11), 0/378 (r = 13);
 - `k = 2`: 0/12 (r = 9), 10/93 (r = 11), 13/234 (r = 13);
 - `k = 3`: 0/3 (r = 11), 8/44 (r = 13) (few discriminating tuples).
The occasional null vectors occur where the number of nonzero rows is barely above `k + 2`, so
they are not generic. No fixed order gives a termwise recurrence on all tuples.

Conclusion: step (ii) fails as stated. The recurrence coefficients of a single 6j symbol depend on
`x`, so the sum over `x` needs an auxiliary telescoping term in `x` (creative telescoping for a
sum of products of three terminating series), i.e. a two-parameter identity of the kind the old
stop trigger names. Per the owner's rule ("if it fails or needs a two-parameter identity,
G3-196 stays conditional"), **G3-196 stays conditional; no further attempts**. LL-0031 rests on
`qBiedenharnElliott` for `r >= 4`; `qOrthogonality` is proved (LL-0075).
Spend of this attempt: about $3 more (row total $7.0 at the last reading, 0.18 %).
