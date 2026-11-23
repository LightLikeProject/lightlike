module

public import Lightlike.Upstream.SpinReps2.SixJOrth

/-!
# The two sides of the Biedenharn–Elliott identity

Definitions of `beLHS` and `beRHS` (doubled spins) for Physlib's 6j symbol `sixJSym`, with two
elementary support lemmas about their terms.

## Main definitions

* `PhyslibAlpha.Sl2.beLHS`, `PhyslibAlpha.Sl2.beRHS`: left and right side of the
  Biedenharn–Elliott identity.
-/

@[expose] public section

open PhyslibAlpha.Sl2

namespace PhyslibAlpha.Sl2

/-- Left side of the Biedenharn–Elliott identity (doubled units). The triad `(a b x)` of the first
6j symbol forces `x ≤ a + b`, so the range `0 … a + b` loses no terms. -/
noncomputable def beLHS (a b c d e f p q r : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (a + b + 1),
    (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * ((x : ℝ) + 1) *
      (sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r)

/-- Right side of the Biedenharn–Elliott identity (doubled units). -/
noncomputable def beRHS (a b c d e f p q r : ℕ) : ℝ :=
  sixJSym p q r e a d * sixJSym p q r f b c

/-- The `x`-range of `beLHS` is complete: terms with `x > a + b` vanish (triangle rule). -/
lemma sixJSym_eq_zero_of_gt {a b x c d p : ℕ} (hx : a + b < x) :
    sixJSym a b x c d p = 0 := by
  by_contra h
  have := (triads_of_sixJSym_ne_zero h).2.2.2.2.1
  omega

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

end PhyslibAlpha.Sl2
