import Lightlike.TuraevViro.Reflect.SixJNorm

/-!
# The boundary evaluation that fixes the norms

`sixj_norm_const` shows that all weighted norms of the q-6j matrix are one constant. That the
constant is `1` is the evaluation of one terminating very-well-poised basic hypergeometric sum
(a `₆φ₅` at a root of unity, the quantum analogue of Dougall's `₅F₄` sum): the weighted norm of
the column of the lowest sixth colour. It is stated here as the hypothesis `QDougall`, and the
conclusion that every row and every column has norm `1` is derived from it.

## Main results

* `QDougall`: the boundary evaluation, a hypothesis.
* `sixj_norm_one`: given `QDougall`, every weighted norm of the q-6j matrix is `1`.

## References

* `koekoek-swarttouw-1996`, the q-Racah polynomials. No source for the summation itself has been
  verified, so none is listed.
-/


namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- **The boundary evaluation** (hypothesis, the `₆φ₅` evaluation): the weighted norm of the
column of the lowest sixth colour `q₀` equals `1`. -/
def QDougall (r j1 j2 j4 j5 x0 n q0 : ℕ) : Prop :=
  jOmega r j1 j5 j4 j2 q0 *
    (∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
      Sj r j1 j2 j4 j5 q0 ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = 1

/-- Given the boundary evaluation, every column and every row of the q-6j matrix has norm `1`. -/
theorem sixj_norm_one {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 x0 n q0 m : ℕ)
    (hadmX : ∀ k ≤ n, qAdm r j1 j2 (x0 + 2 * k) ∧ qAdm r j4 j5 (x0 + 2 * k))
    (hloX : (x0 : ℤ) < (j1 : ℤ) - j2 + 2 ∨ (x0 : ℤ) < (j2 : ℤ) - j1 + 2 ∨
      (x0 : ℤ) < (j4 : ℤ) - j5 + 2 ∨ (x0 : ℤ) < (j5 : ℤ) - j4 + 2)
    (hhiX : (j1 : ℤ) + j2 < (x0 + 2 * n : ℕ) + 2 ∨ (j4 : ℤ) + j5 < (x0 + 2 * n : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j2 + ((x0 + 2 * n : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j5 + ((x0 + 2 * n : ℕ) + 2))
    (hadmQ : ∀ l ≤ m, qAdm r j1 j5 (q0 + 2 * l) ∧ qAdm r j4 j2 (q0 + 2 * l))
    (hloQ : (q0 : ℤ) < (j1 : ℤ) - j5 + 2 ∨ (q0 : ℤ) < (j5 : ℤ) - j1 + 2 ∨
      (q0 : ℤ) < (j4 : ℤ) - j2 + 2 ∨ (q0 : ℤ) < (j2 : ℤ) - j4 + 2)
    (hhiQ : (j1 : ℤ) + j5 < (q0 + 2 * m : ℕ) + 2 ∨ (j4 : ℤ) + j2 < (q0 + 2 * m : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j5 + ((q0 + 2 * m : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j2 + ((q0 + 2 * m : ℕ) + 2))
    (heqX : (x0 : ℤ) = (j1 : ℤ) - j2 ∨ (x0 : ℤ) = (j2 : ℤ) - j1 ∨ (x0 : ℤ) = (j4 : ℤ) - j5 ∨
      (x0 : ℤ) = (j5 : ℤ) - j4)
    (heqQ : (q0 : ℤ) = (j1 : ℤ) - j5 ∨ (q0 : ℤ) = (j5 : ℤ) - j1 ∨ (q0 : ℤ) = (j4 : ℤ) - j2 ∨
      (q0 : ℤ) = (j2 : ℤ) - j4)
    (hD : QDougall r j1 j2 j4 j5 x0 n q0) :
    (∀ l ≤ m, jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
        (∑ k ∈ range (n + 1), jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = 1) ∧
      (∀ k ≤ n, jOmega r j1 j2 j4 j5 (x0 + 2 * k) *
        (∑ l ∈ range (m + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * l) *
          Sj r j1 j2 j4 j5 (q0 + 2 * l) ((x0 + 2 * k : ℕ) : ℤ) ^ 2) = 1) := by
  obtain ⟨c, hc1, hc2⟩ := sixj_norm_const hr j1 j2 j4 j5 x0 n q0 m hadmX hloX hhiX hadmQ
    hloQ hhiQ heqX heqQ
  have h0 := hc1 0 (Nat.zero_le _)
  have hc : c = 1 := by
    rw [← h0]
    simpa [QDougall] using hD
  exact ⟨fun l hl => (hc1 l hl).trans hc, fun k hk => (hc2 k hk).trans hc⟩

end Lightlike.TV.Refl
