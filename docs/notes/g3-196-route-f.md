# G3-196: a new written route for the q-Biedenharn–Elliott identity at every level (24 Nov 2026)

TASK: prove `qBiedenharnElliott_all` so that LL-0031 becomes unconditional (every `r ≥ 4`).
QUESTION: which route to the identity is not already closed by a recorded failure, and what is the
cheapest first test that can falsify it?
METHOD (DS-3 record): re-read `docs/notes/qbe-all-levels.md` and `docs/notes/g3-196-attempt3.md`;
alternatives compared below (D examined and closed by re-reading its source; F recorded).
ACCEPTANCE CRITERION: each route is either closed by a stated reason or has milestones with a first
falsifiable test.
OUTPUT: this note; no Lean.

## What is closed, and why (MEASURED or recorded, not redone)

| Route | Where | Why it does not close |
|---|---|---|
| A: Watson transformation, then one summation | `qbe-all-levels.md` (Route A' count test, Watson certificate) | the left side has up to 4 nested sums, the right side 2; one transformation plus one summation cannot collapse it (3000 tuples at r = 5, 7, 9, 11). The Watson certificate exists numerically (run 2) but proves nothing about BE. |
| B: Racah sum rule plus orthogonality | `qbe-all-levels.md` (Step 5 check) | each pair of the three symbols in the BE sum shares a triad but their other entries are unrelated, so the sum rule applies to no pair; inverting by orthogonality gives BE again (circular). Structural reason (ASSUMPTION): the sum rule and orthogonality are the braiding and unitarity relations of the fusion category; the pentagon is an independent axiom. |
| C: induction in one external colour | `g3-196-attempt3.md` (Route C test) | no `x`-independent order-`k` recurrence for the summand (null vector in 0 of 267 tuples at `k = 1`, r = 9). |
| Rosengren (4.6), (4.8) | `qbe-all-levels.md`, section Route D below | `R = Σ R·R` has the shape "one coefficient equals a sum of products of two", BE has "product of two equals a sum of products of three"; the paper has no tensor-product structure and does not relate them. |

The common point of A, B, C: they use only the *numbers* `qSixJ`. The pentagon is a property of
the *structure* that defines them (associativity of coupling), so a proof has to use that structure.

## Route D (connection coefficients; examined and not a route to the pentagon)

Source: H. Rosengren, arXiv:math/0312310 (read again from the PDF text, Sections 1, 2, 3.1, 4.2).
In that paper `R_kl(a, b, c, d; N)` (eq. (3.6)) are the transition coefficients between two bases of
products `h_k(x; a) h_{N-k}(x; b)` of **one** space `P_N` of symmetric Laurent polynomials, i.e. a
change of basis inside a single irreducible representation (the introduction says so: the `q`-Racah
polynomials appear "as `q`-analogues of Krawtchouk polynomials rather than of Racah polynomials", with
a single irreducible representation instead of three-fold tensor products). Composing two changes of
basis gives the **addition formula (4.6)** `R(a,b,e,f) = Σ_k R(a,b,c,d) R(c,d,e,f)`, which the paper
calls "almost trivial", and the convolution (4.8). Both have the shape "one coefficient = a sum of
products of coefficients"; the paper traces (4.6) to the Yang–Baxter equation. The Biedenharn–Elliott
identity does not occur in the paper. A pentagon needs a four-fold tensor product with three
couplings, and nothing in the polynomial-space framework provides one. Hence the claim "BE is
associativity of basis changes in `P_N`" has no support, and tests T1 to T3 of the first draft of this
note are **not run** (they would test an identification that the source does not make). Route D is
closed.

## Route F: Temperley–Lieb recoupling (Kauffman–Lins), the combinatorial form of the categorical proof

Source: L. H. Kauffman and S. L. Lins, *Temperley–Lieb recoupling theory and invariants of 3-manifolds*
(1994), Chapters 5 to 7 (not read in this session; recorded from the literature, UNVERIFIED).
The category: objects `n ∈ ℕ`, morphisms `n → m` the span of crossingless matchings of `n + m`
points with a circle factor `δ = -A² - A⁻²`; the Jones–Wenzl projector `f_n` is the unique
idempotent killed by every cup/cap; the trivalent vertex `(a, b, c)` is `f_a ⊗ f_b ⊗ f_c` applied to the
unique matching on the three arcs; the 6j symbol is the coefficient of one tree basis in the other
(KL Theorem in Chapter 7). In this form the pentagon is **not** an extra axiom: both sides are the
expansion of the same morphism in the five-tree basis, so it follows from associativity of
composition in the category, provided the 6j are defined as the basis-change coefficients. The work is
to connect these coefficients to the library's `qSixJ`, which KL do by an explicit evaluation of the
tetrahedral net (their Chapter 7) by induction using the fusion identity.

Milestones (PROXY estimates in lines of Lean, no measurement):
- F1 the category of crossingless matchings with composition and the circle value `δ` (about 800).
- F2 Jones–Wenzl projectors by the recursion with coefficients `Δ_{n-1}/Δ_n`, at generic `A` and at
  the root of unity where `Δ_{r-1} = 0` (about 1500).
- F3 trivalent vertices, theta net, tetrahedral net, the fusion identity (about 1500).
- F4 the identification of the tetrahedral net with `qSixJ` (the Racah sum), including the twist phase
  measured in step 4 of `qbe-all-levels.md`, and the truncation to `x < r - 1` (about 2000, with the
  hardest content: the identification and the vanishing of the terms above the level).
- F5 the pentagon from associativity, and `qBiedenharnElliott_all` (about 800).

Route E (the same with `Rep U_q(sl₂)` instead of diagrams) needs the Hopf algebra (G3-200, on main or in
the queue), its finite-dimensional modules, the `q`-Clebsch–Gordan coefficients and the negligible
quotient; the milestones are the same shape with larger F1 and F3 and no diagrams.

## Decision

No route in this note is a row-sized step. The two structural routes (F, E) are milestone-sized
(about 6000 lines, PROXY). G3-196 stays conditional; LL-0031 rests on `qBiedenharnElliott` for
`r ≥ 4` and `qOrthogonality` is proved. If the work is to go on, the first falsifiable step is F1/F2
at generic parameter together with a numerical check that the tetrahedral net of KL equals
`qSixJ` for `r = 5, 7` (the library's `scripts/tv_check.py: q6j` against an exact evaluation of the
net by matching counts); this is the only test of the identification F4 that is cheap.
