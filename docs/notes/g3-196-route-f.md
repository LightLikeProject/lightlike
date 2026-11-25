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

## Progress (24 Nov 2026) and the measured dictionary for F4

F1 and F2 are Lean: `Lightlike/TemperleyLieb/Basic.lean` (the algebra `TL k δ` with relations, universal
property, the Chebyshev sequence `chebD`) and `JonesWenzl.lean` (in any algebra with an `IsTL` family, for
`d_i ≠ 0` up to `N`: `jw n` idempotent, killed by `e_i`, absorbing, commuting with `e_i` for `i ≥ n`, and the
partial trace identity `e_n jw(n+1) e_n = (d_{n+1}/d_n) jw n e_n`).

MEASURED dictionary (exact, ratio 1.0 on 400 sampled tuples at each of r = 5, 6, 7, 9; Python with mpmath at
30 digits, `scripts/tv_check.py: q6j` against Kauffman–Lins' formulas written from memory and corrected only
by this test): with `[n] = sin(nπ/r)/sin(π/r)`, `θ(a,b,c) = (-1)^{x+y+z} [x+y+z+1]! [x]![y]![z]! /
([x+y]![y+z]![x+z]!)` (`x = (a+b-c)/2`, etc., doubled spins) and
`Tet[A B E; C D F] = (I!/E!) Σ_s (-1)^s [s+1]! / (Π_i [s-a_i]! Π_j [b_j-s]!)` with
`a = ((A+D+E)/2, (B+C+E)/2, (A+B+F)/2, (C+D+F)/2)`, `b = ((B+D+E+F)/2, (A+C+E+F)/2, (A+B+C+D)/2)`,
`I! = Π_{i,j} [b_j - a_i]!`, `E! = [A]![B]![C]![D]![E]![F]!`:
`qSixJ r A D E C B F = Tet[A B E; C D F] / sqrt(|θ(A,D,E) θ(B,C,E) θ(A,B,F) θ(C,D,F)|)`.
So the identification F4 splits into (a) the evaluation of the tetrahedral net as this explicit sum (Kauffman–
Lins' theorem, by induction with the fusion identity) and (b) an elementary `q`-factorial manipulation.

Model and design decisions for F3 to F5:
- the model `Finset ℕ →₀ k` (the infinite tensor power of `k²`, a basis vector is the set of positions carrying
  `1`) carries `e_i` as local operators on the positions `i, i+1`, so the relations hold for every `i` with no
  length bookkeeping, and the finite tensor powers are the subspaces supported below `N`; cup and cap
  weights `a = d = 1`, `b = -q`, `c = -q⁻¹` give `δ = -q - q⁻¹`;
- nets are evaluated as pairings of vectors (states) in the model, so the trace and the pairing are
  explicit finite sums; the fusion identity and the evaluation of `θ` and `Tet` are inductions on
  the Jones–Wenzl recursion, which `JonesWenzl.lean` already provides;
- the root of unity: `d_{r-1} = 0`, projectors exist up to `jw (r-1)`, and the trees with all colours `≤ r-2`
  are the ones the library's `qAdm` keeps.

## F3: the crux and the two architectures (24 Nov 2026, after F1, F2, the model, cups and caps, Jones' expectation)

Done in Lean: `Basic` (algebra), `JonesWenzl` (projectors, partial trace), `Model` (the relations on the infinite
tensor power), `CupCap` (loop value, `e_i = cup cap`, zigzag), `Jones` (expectation, absorption).

The crux. The vertex `V(a,b;c) = (p_a ⊗ p_b) · Y · p_c` (`Y` = `i` nested cups at the junction) and its dual
`V'` satisfy `V' V = κ p_c` with `κ = θ(a,b,c)/Δ_c`.  Two ways to prove such statements:

(A) Diagrammatic operator calculus in `End(ModelSpace)`: `V'V` is a closed-up diagram, so it lies in
`tlSub e (c-1)` and `absorb` gives `κ`.  The reduction "`cap z cup ∈ tlSub`" needs the naturality of cups and
caps against `e_j` (cases `j` away from, adjacent to and equal to the junction) and an induction on words with
a drifting cap position; about 600 lines for one arc, more for nested arcs.
(B) Corner algebra: work only in `tlSub e (a+b-1)` with `W_i = Q N_i Q`, `Q = p_a p_b` shifted, `N_i` the nested
`e`-product.  Then `(Q e_{a-1} Q)² = c · Q e_{a-1} Q` follows from a generalised partial trace identity
`e_{a-1} p_a p_b e_{a-1} = c · e_{a-1} p_{a-1} p_{b-1}` plus absorption, with no cups or caps.  The channel
idempotents are Lagrange polynomials in the single operator `A = Q e_{a-1} Q`, and the two operators `A^{(ab)}`,
`A^{(bc)}` of a triple product form a Leonard pair; the 6j symbols are the overlaps of their eigenvectors,
fixed by the three-term recurrence that the library already proves for `qSixJ` in the third colour
(`Reflect/RacahRecurrence`).  Signs are the open point of (B): overlaps of eigenvectors give `F²` unless the
vectors are fixed by the tree construction.
CORRECTION (MEASURED, numpy, 2^n-dimensional model, random complex `q`): the identity
`e_{a-1} p_a p_b e_{a-1} = c · e_{a-1} p_{a-1} p'_{b-1}` holds for `(a,b) ∈ {(1,1),(2,1),(1,2)}` (with `c = d_a/d_{a-1}`
for `b = 1`) and FAILS for `(2,2), (3,2), (2,3), (3,3)`; so `(Q e Q)² = c Q e Q` is false for blocks of size at
least two, as it must be since `Q·TL·Q` has dimension `min(a,b)+1` and `Q e Q` has that many eigenvalues.  In (B) the
channel idempotents are Lagrange polynomials in `A = Q e_{a-1} Q` over its eigenvalues, which first have to be
computed (the partial trace identity only gives the top and bottom ones).
Next Lean step for (B): the shifted family `e ∘ (· + s)` is `IsTL`, the generalised partial trace identity,
and `A² = c A`.  Next step for (A): naturality lemmas of `cup` and `cap` against `e_j`.

## F3 status: the vertex norm is a scalar, and its value (MEASURED)

Lean (`Natural`, `Reduction`, `Vertex`): cups and caps slide through the generators; `cap_m z cup_{m'} ∈ C(n-1)` for
`z ∈ C(n+1)` (`cap_mul_cup_mem`); the nested junction sandwich `nestCap l i · Q · nestCup l i ∈ C(N - 2i)`
(`nestCap_mul_nestCup_mem`); and `vertex_norm`: `p_c · nestCap · (p_a p_b') · nestCup · p_c = κ p_c` for some scalar
`κ`, `c = a + b - 2i`, `l = a - i` (needs `d_j ≠ 0` for `j < c`).
MEASURED value of `κ` (numpy, matrices of cups, caps and projectors on `2^n`, random complex `q`, nine cases with
`a, b ≤ 3`, `i ≤ min(a,b)`): `κ(a,b,i) = θ(a,b,c) / Δ_c` exactly, with Kauffman–Lins' signed `θ` and
`Δ_c = (-1)^c [c+1]`, `[n] = (q^n - q^{-n})/(q - q^{-1})` (i.e. `A² = q`, loop value `-q - q^{-1}`); the
model's conventions (`cup = |01⟩ - q|10⟩`, `cap⟨01| = -q⁻¹, cap⟨10| = 1`) agree with Kauffman–Lins.
Next: prove this value (an induction on `b` through the Jones–Wenzl recursion; the naive recursion does not
close because `P'_b` does not commute with the new generator, so it needs the partial-trace identity of the vertex),
then the fusion identity `p_a p_b = Σ_c (Δ_c/θ(a,b,c)) V V'`, then recoupling and the pentagon.

## F3 status (25 Nov 2026): the fusion identity is proved (Lean, `TemperleyLieb/FusionIdentity.lean`)

`fusion_identity`: for `a, b ≥ 1`, `d_j ≠ 0` and `q^{2j} ≠ 1` for `1 ≤ j ≤ a + b + 1` (characteristic zero),
`Q(a,b) = Σ_{i ≤ min(a,b)} E_i` with `E_i = κ_i⁻¹ V_i W_i` the channel idempotents (`W_i V_i = κ_i p`, `κ_i = kapRec`
non-zero, `E_i E_j = 0` from `channel_orth`). Proof by rank count (MEASURED in Lean, no `sorry`, axioms
`propext, Classical.choice, Quot.sound`): in the window of the first `a + b` strands, `rank Q ≤ (a+1)(b+1)` (sorted
coordinates of the common kernel of the block generators, `Rank.lean`) and `rank E_i ≥ a + b - 2i + 1` (the
`q`-Dicke vectors `Σ q^{pos σ}|σ⟩` are independent, fixed by `p`, and sent to independent vectors by `V_i`); the
dimensions sum to `(a+1)(b+1)`, so `complete_of_rank` (a trace argument) gives equality on the window, and tail
equivariance (`Eqv`, `iota`) extends it to the whole model. Next: recoupling coefficients, the abstract pentagon,
and the F4 identification with `qSixJ`.

## F3/F4 status (25 Nov 2026, later): trees, one-dimensionality and the recoupling coefficients (Lean)

`Iterated.lean`, `Shift.lean`, `Recoupling.lean`. Iterated fusion: `Q(a,b) p_c = Σ_e Σ_d treeL e d` and `p_a Q(b,c) =
Σ_f Σ_d' treeR f d'` (the second by the translation homomorphism `sh`, which sends `e_j`, cups, caps and projectors to
their translates), the same projector `P3`; both families are orthogonal idempotents (`treeL_mul`, `treeR_mul`).
Expansion lemma `cup_mul_cap_mem` (`cup_m z cap_m ∈ C(n+2)` for `z ∈ C n`; the middle case is
`cup_{l+1} e_l cap_{l+1} = e_{l+1} e_l e_{l+2} e_{l+1}`, proved from the zigzags), hence `E_i ∈ C(a+b-1)` and
`treeL, treeR ∈ C(N-1)`. One-dimensionality: `treeL e d · Y · treeL e d ∈ k · treeL e d` for every `Y ∈ C(N-1)` (the
two-level sandwich `W_d W_e Y V_e V_d` is a scalar times a projector by `absorb`). Recoupling coefficients
`recoup e d f d'` := that scalar for `Y = treeR f d'`; `recoup_row_sum`: `Σ_{f,d'} recoup = 1`.
Also proved: the exact rank `D+1` of every tree idempotent on the window (trace of a conjugated idempotent) and
`recoup = 0` unless the total channels `D` agree (`recoup_eq_zero_of_ne`, from the two-sided minimality and the ranks).
Both readings of the coefficient agree (`recoupR_eq`) and the column sums are `1` too (`recoup_col_sum`): the matrix of
squared 6j symbols is doubly stochastic and block diagonal in the total channel `D`.
Open before the pentagon: (i) the signed matrix: expansion of `U_R` in the basis `U_e` of the multiplicity space
(spanning of `Hom_D`, a dimension count of order a thousand lines), because `recoup` only sees squares;
(ii) the matrix-unit identification giving `treeR = Σ U recoup U'` and the orthogonality relations; (iii) the
pentagon for four blocks; (iv) the dictionary with `qSixJ` (Tet formula) and the truncation at `r`.

### Signed Gram pairing: proved (25 Nov 2026, `TemperleyLieb/Gram.lean`)

`gram_scalar`: for equal total channels `D`, `(W_d W_e)(sh V_f · V_{d'}) = g · p_D` for a scalar `g` (the Gram pairing of
a first-bracketing and a second-bracketing tree vector). Proof: the product is `p_D · gramMid · p_D`, and `gramMid`, a word
`caps_d · [Q' p_A] · caps_e · Z · cups_f · [J Q''] · cups_{d'}` with `e + d = f + d'` and `Z ∈ C(N-1)`, is in `C(D-1)`
because caps and cups pair from the middle outward even when `e ≠ f` (`balanced_le`, `balanced_ge`, built on
`nestCap_mul_nestCup_mem_gen`: two junctions, equal count); then `jwAt_sandwich` makes `p_D · C(D-1) · p_D` a scalar.
Remaining before the pentagon: (i) DONE (`GramVanish.lean`, `gram_vanish`: the pairing vanishes for `D ≠ D'`; eight unbalanced three-layer reductions plus absorption and `cap_m p_D = 0`). The proof idea was: after the pairing of caps and
cups the unbalanced word is `p_{D1} · caps_k · Z'' · p_{D2}` (more caps) with `Z'' ∈ C(D2-1)`, so `Z'' p_{D2} = ε p_{D2}`
(`absorb`) and `cap_m p_{D2} = 0` (from `e_m p = 0` and `cap_m cup_m = δ`); symmetrically `p_{D1} Z'' cups_k` with
`p_{D1} cup_m = 0`. This needs the three-layer reductions with leftovers (`balanced_le/ge` for unequal totals, six
sub-cases, ~500 lines); an alternative is the `U_q(sl_2)` action on the model (`E`, `F` commute with `e_i`, cups, caps; the
highest-weight vector of `range p_{D2}` is sent to a vector of too high weight), ~300 lines for the action plus the
identification of `range p_D` with the module generated by `|1…1⟩`; (ii) the expansion `U_R(f) = Σ_e g/κ U_L(e)` in the
multiplicity space and the relation of `g` to `recoup` (`recoup = c · g · g'`); (iii) the same for four blocks (five
trees) and the pentagon for the matrix `g`; (iv) the dictionary of `g` with `qSixJ` (Tet) and the truncation at `r`.

## Decision

No route in this note is a row-sized step. The two structural routes (F, E) are milestone-sized
(about 6000 lines, PROXY). G3-196 stays conditional; LL-0031 rests on `qBiedenharnElliott` for
`r ≥ 4` and `qOrthogonality` is proved. If the work is to go on, the first falsifiable step is F1/F2
at generic parameter together with a numerical check that the tetrahedral net of KL equals
`qSixJ` for `r = 5, 7` (the library's `scripts/tv_check.py: q6j` against an exact evaluation of the
net by matching counts); this is the only test of the identification F4 that is cheap.
