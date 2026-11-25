import Mathlib

/-!
# An elementary evaluation of `₂F₁(a, −a; c; 1)`

`hgTerm a c n = (a)_n (−a)_n / ((c)_n n!)`.  Telescoping gives `(c² − a²) S(c+1) = c² S(c)` for the sums
`S(c) = Σ hgTerm a c n`, and for `c = 1` the terms are `P_n − P_{n−1}` with `P_n = ∏_{j ≤ n}(1 − a²/j²)`, so
`S(1) = sin(πa)/(πa)` (Euler's product).  This is the evaluation at infinity of the regular solution of the Dirac mode
system on the sphere.
-/

namespace Lightlike.Dirac

/-- The terms `(a)_n (−a)_n / ((c)_n n!)` of `₂F₁(a, −a; c; 1)`. -/
noncomputable def hgTerm (a c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => hgTerm a c n * (((n : ℂ) + a) * ((n : ℂ) - a)) / ((c + n) * ((n : ℂ) + 1))

/-- Shifting `c` by one multiplies the `n`-th term by `c / (c + n)`. -/
lemma hgTerm_shift (a c : ℂ) (hc : ∀ n : ℕ, c + n ≠ 0) : ∀ n : ℕ,
    hgTerm a (c + 1) n = c / (c + n) * hgTerm a c n := by
  intro n
  induction n with
  | zero =>
    have : c ≠ 0 := by simpa using hc 0
    simp [hgTerm, div_self this]
  | succ n ih =>
    have h1 : c + n ≠ 0 := hc n
    have h2 : c + (n + 1 : ℕ) ≠ 0 := hc (n + 1)
    have h3 : c + 1 + n ≠ 0 := by
      have := hc (n + 1); push_cast at this; intro h; apply this; linear_combination h
    have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [hgTerm, ih]
    push_cast at h2 ⊢
    field_simp
    ring

/-- **The telescoping identity.** -/
lemma hgTerm_telescope (a c : ℂ) (hc : ∀ n : ℕ, c + n ≠ 0) (n : ℕ) :
    (c ^ 2 - a ^ 2) * hgTerm a (c + 1) n - c ^ 2 * hgTerm a c n =
      c * ((n : ℂ) + 1) * hgTerm a c (n + 1) - c * (n : ℂ) * hgTerm a c n := by
  have h1 : c + n ≠ 0 := hc n
  have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [hgTerm_shift a c hc n]
  simp only [hgTerm]
  field_simp
  ring

end Lightlike.Dirac
