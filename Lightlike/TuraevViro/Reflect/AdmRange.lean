import Lightlike.TuraevViro.QSixJ

/-!
# The common admissible colours of two triads form a progression

For two pairs `(a, b)` and `(c, d)` of colours with `a + b + c + d` even, the colours `x` that are
`q`-admissible with both pairs are exactly the integers of the right parity between `aLo` and `aHi`
(and then `a + b` and `c + d` are within the level bound).
-/

namespace Lightlike.TV.Refl

open Lightlike.TV

/-- The least colour admissible with both pairs. -/
def aLo (a b c d : ℕ) : ℕ := max (max (a - b) (b - a)) (max (c - d) (d - c))

/-- The greatest colour admissible with both pairs at level `r`. -/
def aHi (r a b c d : ℕ) : ℕ := min (min (a + b) (c + d)) (min (2 * (r - 2) - (a + b)) (2 * (r - 2) - (c + d)))

/-- The common admissible third colours of two triads are the integers of one parity between `aLo` and `aHi`. -/
lemma adm_pair_iff {r : ℕ} (hr : 2 ≤ r) {a b c d : ℕ} (hpar : (a + b + c + d) % 2 = 0) (x : ℕ) :
    (qAdm r a b x ∧ qAdm r c d x) ↔
      (aLo a b c d ≤ x ∧ x ≤ aHi r a b c d ∧ (x + a + b) % 2 = 0 ∧
        a + b ≤ 2 * (r - 2) ∧ c + d ≤ 2 * (r - 2)) := by
  unfold qAdm Lightlike.Pentagon.Tri aLo aHi
  simp only [max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4⟩, h5⟩, ⟨h6, h7, h8, h9⟩, h10⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8, h9⟩
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega

/-- `aLo` bounds and is one of the four differences. -/
lemma aLo_spec (a b c d : ℕ) :
    a ≤ b + aLo a b c d ∧ b ≤ a + aLo a b c d ∧ c ≤ d + aLo a b c d ∧ d ≤ c + aLo a b c d ∧
      (aLo a b c d + b = a ∨ aLo a b c d + a = b ∨ aLo a b c d + d = c ∨ aLo a b c d + c = d) := by
  unfold aLo
  omega

/-- `aHi` is bounded by the four sums and equals one of them. -/
lemma aHi_spec (r a b c d : ℕ) :
    aHi r a b c d ≤ a + b ∧ aHi r a b c d ≤ c + d ∧ aHi r a b c d ≤ 2 * (r - 2) - (a + b) ∧
      aHi r a b c d ≤ 2 * (r - 2) - (c + d) ∧
      (aHi r a b c d = a + b ∨ aHi r a b c d = c + d ∨ aHi r a b c d = 2 * (r - 2) - (a + b) ∨
        aHi r a b c d = 2 * (r - 2) - (c + d)) := by
  unfold aHi
  omega

/-- The endpoint facts of the progression of common admissible colours, for the recurrence. -/
lemma pair_facts {r : ℕ} {a b c d : ℕ} (hpar : (a + b + c + d) % 2 = 0)
    (hab : a + b ≤ 2 * (r - 2)) (hcd : c + d ≤ 2 * (r - 2)) :
    (aLo a b c d + a + b) % 2 = 0 ∧ (aHi r a b c d + a + b) % 2 = 0 ∧
      ((aLo a b c d : ℤ) = (a : ℤ) - b ∨ (aLo a b c d : ℤ) = (b : ℤ) - a ∨
        (aLo a b c d : ℤ) = (c : ℤ) - d ∨ (aLo a b c d : ℤ) = (d : ℤ) - c) ∧
      ((aLo a b c d : ℤ) < (a : ℤ) - b + 2 ∨ (aLo a b c d : ℤ) < (b : ℤ) - a + 2 ∨
        (aLo a b c d : ℤ) < (c : ℤ) - d + 2 ∨ (aLo a b c d : ℤ) < (d : ℤ) - c + 2) ∧
      ((a : ℤ) + b < aHi r a b c d + 2 ∨ (c : ℤ) + d < aHi r a b c d + 2 ∨
        (2 * r : ℤ) - 2 ≤ (a : ℤ) + b + (aHi r a b c d + 2) ∨
        (2 * r : ℤ) - 2 ≤ (c : ℤ) + d + (aHi r a b c d + 2)) := by
  have h1 := (aLo_spec a b c d).2.2.2.2
  have h2 := (aHi_spec r a b c d).2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Lightlike.TV.Refl
