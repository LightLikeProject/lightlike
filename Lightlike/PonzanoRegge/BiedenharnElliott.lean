module

public import Lightlike.Tests.SixJ

/-!
# The Biedenharn–Elliott identity - statement, checks, and plan

The Biedenharn–Elliott (pentagon) identity is the algebraic heart of the invariance of the
Ponzano–Regge state sum under the 2-3 Pachner move. In its standard form, with `S` the sum of
the nine fixed spins,

  `Σ_x (-1)^(S+x) (2x+1) {a b x; c d p}{c d x; e f q}{e f x; b a r} = {p q r; e a d}{p q r; f b c}`.

Here it is stated for Physlib's 6j symbol `sixJSym` in **doubled units** (`2j ∈ ℕ`, so `2x+1`
becomes `x+1` and `(-1)^(S+x)` becomes `(-1)^((S₂+x₂)/2)`).

## Status

* `BiedenharnElliott` - the statement, as a `Prop`. **PROVEN for all spins:**
  `Lightlike.Pentagon.biedenharnElliott` (`BEZero.lean`). The positive case comes from the recoupling
  pentagon (`Pentagon.lean`, `BEPositive.lean`). Zero spins come from the zero-spin closed form of
  the 6j symbol, the vertex symmetries of the identity, and 6j orthogonality (`BEZero.lean`). Downstream, the
  Pachner 2-3 move (`Lightlike.PR.weight_move23`, `Amplitude.lean`) takes the instance it needs
  (`Lightlike.PR.BEAt`) as an explicit hypothesis; it is *not* an axiom and there is no `sorry`.
* `biedenharnElliott_instance` - one nontrivial instance proven from Physlib's definition (all
  six outer spins `½`, `p = q = r = 1`; both sides equal `1/9`, two nonzero terms on the left).
* `triads_of_sixJSym_ne_zero`, `even_of_beTerm_ne_zero` - every nonzero 6j has four admissible
  triads, so the sign exponent `S + x` is an integer on every contributing term.
* Numerical evidence (not a proof): the identity in exactly this form holds to `1e-16` for all
  `262 144` choices of the nine spins in `{0, ½, 1, 3/2}` (1 495 nontrivial), checked against
  SymPy's independent `wigner_6j`.

## Proof plan (recoupling route - the pentagon)

Work with *vectors* in `((V(a) ⊗ V(b)) ⊗ V(c)) ⊗ V(d)`, indexed by naturals, not with maps out of
`V(J)`. This avoids casts between `StandardSl2Module ℝ n` for numerically equal but syntactically
different `n`. Progress lives in `Pentagon.lean`.

1. **Expansion lemma** (DONE: `Lightlike.Pentagon.stateB_eq_sum_stateA`). In a triple product,
   `stateB = Σ_{k₁} recoupling · stateA`, from Physlib's completeness `eq_sum_vecA` and its
   selection rule.
2. **Five tree states** as explicit sums in the four-fold product:
   - `T1 = ((12)3)4`: outer CG sum of `stateA(a,b,c) ⊗ e_δ`;
   - `T5 = (1(23))4`: the same with `stateB(a,b,c)`;
   - `T2 = (12)(34)`, `T3 = 1(2(34))`, `T4 = 1((23)4)`: via the embeddings `E12`, `E34`, `E23` of
     the triples `(j12,c,d)`, `(a,b,j34)`, `(a,j23,d)`, and a left lift for `(b,c,d)`.
   - **Consistency lemmas:** each tree written two ways agrees (unfolding `stateA`, `stateB`,
     `coupledVec_eq_sum`).
3. **Expand `T3` two ways** into the `T1` family, using stage 1 in each triple and
   `recoupling_eq_recoupling_zero` to pull coefficients out of outer CG sums:
   - via `T2`: two moves, giving `R_{a,b,j34} · R_{j12,c,d}`;
   - via `T4`, `T5`: three moves, giving `Σ_{j23} R_{b,c,d} R_{a,j23,d} R_{a,b,c}`.
4. **Compare coefficients** using the orthonormality of the `T1` family (isometry of the
   embeddings plus `tensorForm_coupledVec`). This gives the pentagon for recoupling coefficients.
5. **Translate** with `recoupling_eq_sixJ`, `sixJ_eq_sixJSym` and 6j symmetries to `beLHS = beRHS`.
   Cross-check the exact phase/letter dictionary with SymPy *before* the Lean translation. In
   pentagon terms `x = j23`, `{p,q,r} = {j12, j34, J}`, and `{a..f}` pairs as `{j2,j3}`,
   `{j4,j234}`, `{j1,j123}`.
6. **Zero spins.** Physlib needs `j1, j2, j3, j4, j12, j34 > 0`. The remaining cases need closed
   forms for 6j symbols with a zero entry (from the `sixJSym` definition), after which BE reduces to
   a single term or to 6j orthogonality.

Rough size: 1500–2500 lines in total. Main risks: the index bookkeeping in stage 2 and the phases
in stage 5. Alternatives considered:
- 3j-calculus: needs "three 3j contract to 3j × 6j", the same representation-theoretic core
  (stage 1 is exactly that statement in CG form).
- Racah's closed formula plus a hypergeometric identity: Racah's 6j formula is not in Physlib.
- Bounded-spin brute force: 6j values are algebraic irrationals, so `decide` does not apply.
-/

@[expose] public section

open PhyslibAlpha.Sl2

namespace Lightlike

/-- Left side of Biedenharn–Elliott (doubled units). The triad `(a b x)` of the first 6j symbol
forces `x ≤ a + b`, so the range `0 … a + b` loses no terms. -/
noncomputable def beLHS (a b c d e f p q r : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (a + b + 1),
    (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * ((x : ℝ) + 1) *
      (sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r)

/-- Right side of Biedenharn–Elliott (doubled units). -/
noncomputable def beRHS (a b c d e f p q r : ℕ) : ℝ :=
  sixJSym p q r e a d * sixJSym p q r f b c

/-- **The Biedenharn–Elliott identity** for Physlib's 6j symbols (doubled units).
Proven for all spins: `Lightlike.Pentagon.biedenharnElliott` (`BEZero.lean`). -/
def BiedenharnElliott : Prop :=
  ∀ a b c d e f p q r : ℕ, beLHS a b c d e f p q r = beRHS a b c d e f p q r

/-- The `x`-range of `beLHS` is complete: terms with `x > a + b` vanish (triangle rule). -/
lemma sixJSym_vanishes_beyond_range {a b x c d p : ℕ} (hx : a + b < x) :
    sixJSym a b x c d p = 0 :=
  Lightlike.SixJAudit.sixJSym_eq_zero_of_triangle hx

/-- A nonzero 6j symbol has four admissible triads: integer perimeters and triangle inequalities.
-/
theorem triads_of_sixJSym_ne_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : sixJSym j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    (j₁ + j₂ + j₃) % 2 = 0 ∧ (j₁ + j₅ + j₆) % 2 = 0 ∧ (j₄ + j₂ + j₆) % 2 = 0 ∧
      (j₄ + j₅ + j₃) % 2 = 0 ∧ j₃ ≤ j₁ + j₂ ∧ j₁ ≤ j₂ + j₃ ∧ j₂ ≤ j₁ + j₃ := by
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_contra hc
  apply hm
  apply Lightlike.SixJAudit.sixJTerm_eq_zero
  rintro ⟨h1, h2, h3, h4⟩
  apply hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, t1, t2, t3, p1⟩ := h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p2⟩ := h2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p3⟩ := h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p4⟩ := h4
  exact ⟨p1, p2, p3, p4, t1, t2, t3⟩

/-- On every contributing term of `beLHS` the sign exponent `S + x` is even, so `(-1)^(S+x)`
(in spins, not doubled spins) is well defined: the triads `(a b x)`, `(a d p)`, `(c f q)`,
`(e a r)` of the three 6j symbols have integer perimeters, and their sum is `S + x` mod 2. -/
theorem even_of_beTerm_ne_zero {a b c d e f p q r x : ℕ}
    (h : sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r ≠ 0) :
    (a + b + c + d + e + f + p + q + r + x) % 2 = 0 := by
  have h1 := triads_of_sixJSym_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have h2 := triads_of_sixJSym_ne_zero (right_ne_zero_of_mul (left_ne_zero_of_mul h))
  have h3 := triads_of_sixJSym_ne_zero (right_ne_zero_of_mul h)
  omega

/-- **One nontrivial instance**: all six outer spins `½` (doubled `1`), `p = q = r = 1` (doubled
`2`). Left: `(½)³ - 3·(1/6)³ = 1/9` (the `x = ½` term vanishes by parity); right: `(-1/3)² = 1/9`.
-/
theorem biedenharnElliott_instance : beLHS 1 1 1 1 1 1 2 2 2 = beRHS 1 1 1 1 1 1 2 2 2 := by
  have h0 : sixJSym 1 1 1 1 1 2 = 0 := Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (by norm_num)
  norm_num [beLHS, beRHS, Finset.sum_range_succ, h0, Lightlike.SixJAudit.sixJ_hh0_hh1,
    Lightlike.SixJAudit.sixJ_hh1_hh1, Lightlike.SixJAudit.sixJ_111_hhh]

end Lightlike
