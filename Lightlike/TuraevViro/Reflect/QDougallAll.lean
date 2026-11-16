import Lightlike.TuraevViro.Reflect.QDougallMap
import Lightlike.TuraevViro.Reflect.OrthConditional

/-!
# The boundary evaluation `QDougallAll` at every level

`QDougallAll r` says that the weighted norm of the lowest column of the q-6j matrix is `1` for every
admissible quadruple at level `r`. The summation theorems of `QDougallMap` prove it in the first and the
third orbit of the forms of the lowest colours, with the third colours running up to the triangle top
or stopping at the level cut-off, and in the images of those forms under the permutations of the four
spins. This file shows that every admissible case is one of them, by a finite case split (no induction
on the level).

## Main results

* `coverO1`, `coverO3`: `QDougallAt` for the first and the third orbit, for either range.
* `coverPair00` to `coverPair33`: the 16 pairs of a form of the lowest third colour and of the lowest
  sixth colour, each covered by `coverO1` or `coverO3` or an image.
* `qDougallAll_proved`: **`QDougallAll r` holds for every `r ≥ 2`.**
* `qOrthogonality_proved`: q-orthogonality of the 6j symbol at every level `r ≥ 2`.
-/

namespace Lightlike.TV.Refl
open Lightlike.TV

/-- **Covering, first orbit.** If the lowest third colour is `B - A` and the lowest sixth colour is
`B - F`, then `QDougallAt` holds: the third colours run up to `E + F`, or stop at the level cut-off
`2(r-2) - (B + A)`. -/
theorem coverO1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : A ≤ B) (hF : F ≤ B) (hx : aLo B A E F = B - A) (hq : aLo B F E A = B - F) :
    QDougallAt r B A E F := by
  have hEF : E + F ≤ B + A := by unfold aLo at hx hq; omega
  by_cases hc : E + F ≤ 2 * (r - 2) - (B + A)
  · exact qDougallAt_O1 hr B A E F q hq1 hq2 hA hF hx hq (by unfold aHi; omega)
  · exact qDougallAt_O1_trunc hr B A E F q hq1 hq2 hA hF hEF hx hq (by unfold aHi; omega)

/-- **Covering, third orbit.** If the lowest third colour is `B - A` and the lowest sixth colour is
`E - A`, then `QDougallAt` holds. -/
theorem coverO3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : A ≤ B) (hE : A ≤ E) (hx : aLo B A E F = B - A) (hq : aLo B F E A = E - A) :
    QDougallAt r B A E F := by
  have hEF : B + A ≤ E + F := by unfold aLo at hx hq; omega
  rcases hEF.lt_or_eq with hlt | heq
  · by_cases hc : B + A ≤ 2 * (r - 2) - (E + F)
    · exact qDougallAt_O3 hr B A E F q hq1 hq2 hA hE hlt hx hq (by unfold aHi; omega)
    · exact qDougallAt_O3_trunc hr B A E F q hq1 hq2 hA hE hlt (by omega) hx hq
        (by unfold aHi; omega)
  · refine coverO1 hr B A E F q hq1 hq2 hA (by unfold aLo at hx hq; omega) hx ?_
    unfold aLo at hx hq ⊢; omega


/-- Covering, first orbit, image under `(B E)(A F)`. -/
theorem coverO1_k1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : F ≤ E) (hF : A ≤ E) (hx : aLo E F B A = E - F) (hq : aLo E A B F = E - A) :
    QDougallAt r B A E F :=
  (qDougallAt_k1 r B A E F).1 (coverO1 hr E F B A q hq2 hq1 hA hF hx hq)

/-- Covering, first orbit, image under `(B A)(E F)`. -/
theorem coverO1_k2 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : B ≤ A) (hF : E ≤ A) (hx : aLo A B F E = A - B) (hq : aLo A E F B = A - E) :
    QDougallAt r B A E F :=
  (qDougallAt_k2 r B A E F).1 (coverO1 hr A B F E q (qAdm_swap12 hq2) (qAdm_swap12 hq1) hA hF hx hq)

/-- Covering, first orbit, image under `(B F)(A E)`. -/
theorem coverO1_k3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : E ≤ F) (hF : B ≤ F) (hx : aLo F E A B = F - E) (hq : aLo F B A E = F - B) :
    QDougallAt r B A E F :=
  (qDougallAt_k3 r B A E F).1 (coverO1 hr F E A B q (qAdm_swap12 hq1) (qAdm_swap12 hq2) hA hF hx hq)

/-- Covering, third orbit, image under `(B E)(A F)`. -/
theorem coverO3_k1 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : F ≤ E) (hE : F ≤ B) (hx : aLo E F B A = E - F) (hq : aLo E A B F = B - F) :
    QDougallAt r B A E F :=
  (qDougallAt_k1 r B A E F).1 (coverO3 hr E F B A q hq2 hq1 hA hE hx hq)

/-- Covering, third orbit, image under `(B A)(E F)`. -/
theorem coverO3_k2 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : B ≤ A) (hE : B ≤ F) (hx : aLo A B F E = A - B) (hq : aLo A E F B = F - B) :
    QDougallAt r B A E F :=
  (qDougallAt_k2 r B A E F).1 (coverO3 hr A B F E q (qAdm_swap12 hq2) (qAdm_swap12 hq1) hA hE hx hq)

/-- Covering, third orbit, image under `(B F)(A E)`. -/
theorem coverO3_k3 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (hq1 : qAdm r B F q) (hq2 : qAdm r E A q)
    (hA : E ≤ F) (hE : E ≤ A) (hx : aLo F E A B = F - E) (hq : aLo F B A E = A - E) :
    QDougallAt r B A E F :=
  (qDougallAt_k3 r B A E F).1 (coverO3 hr F E A B q (qAdm_swap12 hq1) (qAdm_swap12 hq2) hA hE hx hq)

/-- Covering of the pair of lowest colours `(B-A, B-F)`. -/
theorem coverPair00 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + A = B) (hq : aLo B F E A + F = B) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  exact coverO1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(B-A, F-B)`. -/
theorem coverPair01 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + A = B) (hq : aLo B F E A + B = F) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo F E A B = aLo B A E F := by unfold aLo; omega
  have eq : aLo F B A E = aLo B F E A := by unfold aLo; omega
  exact coverO1_k3 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(B-A, E-A)`. -/
theorem coverPair02 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + A = B) (hq : aLo B F E A + A = E) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  exact coverO3 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(B-A, A-E)`. -/
theorem coverPair03 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + A = B) (hq : aLo B F E A + E = A) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  exact coverO1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(A-B, B-F)`. -/
theorem coverPair10 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + B = A) (hq : aLo B F E A + F = B) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo A B F E = aLo B A E F := by unfold aLo; omega
  have eq : aLo A E F B = aLo B F E A := by unfold aLo; omega
  exact coverO1_k2 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(A-B, F-B)`. -/
theorem coverPair11 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + B = A) (hq : aLo B F E A + B = F) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo A B F E = aLo B A E F := by unfold aLo; omega
  have eq : aLo A E F B = aLo B F E A := by unfold aLo; omega
  exact coverO3_k2 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(A-B, E-A)`. -/
theorem coverPair12 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + B = A) (hq : aLo B F E A + A = E) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo E F B A = aLo B A E F := by unfold aLo; omega
  have eq : aLo E A B F = aLo B F E A := by unfold aLo; omega
  exact coverO1_k1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(A-B, A-E)`. -/
theorem coverPair13 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + B = A) (hq : aLo B F E A + E = A) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo A B F E = aLo B A E F := by unfold aLo; omega
  have eq : aLo A E F B = aLo B F E A := by unfold aLo; omega
  exact coverO1_k2 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(E-F, B-F)`. -/
theorem coverPair20 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + F = E) (hq : aLo B F E A + F = B) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo E F B A = aLo B A E F := by unfold aLo; omega
  have eq : aLo E A B F = aLo B F E A := by unfold aLo; omega
  exact coverO3_k1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(E-F, F-B)`. -/
theorem coverPair21 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + F = E) (hq : aLo B F E A + B = F) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo E F B A = aLo B A E F := by unfold aLo; omega
  have eq : aLo E A B F = aLo B F E A := by unfold aLo; omega
  exact coverO1_k1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(E-F, E-A)`. -/
theorem coverPair22 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + F = E) (hq : aLo B F E A + A = E) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo E F B A = aLo B A E F := by unfold aLo; omega
  have eq : aLo E A B F = aLo B F E A := by unfold aLo; omega
  exact coverO1_k1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(E-F, A-E)`. -/
theorem coverPair23 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + F = E) (hq : aLo B F E A + E = A) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo A B F E = aLo B A E F := by unfold aLo; omega
  have eq : aLo A E F B = aLo B F E A := by unfold aLo; omega
  exact coverO1_k2 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(F-E, B-F)`. -/
theorem coverPair30 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + E = F) (hq : aLo B F E A + F = B) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  exact coverO1 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(F-E, F-B)`. -/
theorem coverPair31 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + E = F) (hq : aLo B F E A + B = F) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo F E A B = aLo B A E F := by unfold aLo; omega
  have eq : aLo F B A E = aLo B F E A := by unfold aLo; omega
  exact coverO1_k3 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(F-E, E-A)`. -/
theorem coverPair32 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + E = F) (hq : aLo B F E A + A = E) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo F E A B = aLo B A E F := by unfold aLo; omega
  have eq : aLo F B A E = aLo B F E A := by unfold aLo; omega
  exact coverO1_k3 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- Covering of the pair of lowest colours `(F-E, A-E)`. -/
theorem coverPair33 {r : ℕ} (hr : 2 ≤ r) (B A E F q : ℕ) (h1 : qAdm r B F q)
    (h2 : qAdm r E A q) (hx : aLo B A E F + E = F) (hq : aLo B F E A + E = A) :
    QDougallAt r B A E F := by
  obtain ⟨a1, a2, a3, a4, -⟩ := aLo_spec B A E F
  obtain ⟨b1, b2, b3, b4, -⟩ := aLo_spec B F E A
  have ex : aLo F E A B = aLo B A E F := by unfold aLo; omega
  have eq : aLo F B A E = aLo B F E A := by unfold aLo; omega
  exact coverO3_k3 hr B A E F q h1 h2 (by omega) (by omega) (by omega) (by omega)

/-- **The boundary evaluation at every level.** For every `r ≥ 2` and all spins `B, A, E, F` with an
admissible colour `q` on both sides, the norm of the lowest column of the q-6j matrix is `1`: the
lowest third and sixth colours are one of four differences each, and each of the 16 pairs is covered
by `coverO1` or `coverO3` or one of their images under the permutations of the four spins. -/
theorem qDougallAll_proved {r : ℕ} (hr : 2 ≤ r) : QDougallAll r := by
  intro B A E F q h1 h2
  obtain ⟨-, -, -, -, hx⟩ := aLo_spec B A E F
  obtain ⟨-, -, -, -, hq⟩ := aLo_spec B F E A
  rcases hx with hx | hx | hx | hx <;> rcases hq with hq | hq | hq | hq
  · exact coverPair00 hr B A E F q h1 h2 hx hq
  · exact coverPair01 hr B A E F q h1 h2 hx hq
  · exact coverPair02 hr B A E F q h1 h2 hx hq
  · exact coverPair03 hr B A E F q h1 h2 hx hq
  · exact coverPair10 hr B A E F q h1 h2 hx hq
  · exact coverPair11 hr B A E F q h1 h2 hx hq
  · exact coverPair12 hr B A E F q h1 h2 hx hq
  · exact coverPair13 hr B A E F q h1 h2 hx hq
  · exact coverPair20 hr B A E F q h1 h2 hx hq
  · exact coverPair21 hr B A E F q h1 h2 hx hq
  · exact coverPair22 hr B A E F q h1 h2 hx hq
  · exact coverPair23 hr B A E F q h1 h2 hx hq
  · exact coverPair30 hr B A E F q h1 h2 hx hq
  · exact coverPair31 hr B A E F q h1 h2 hx hq
  · exact coverPair32 hr B A E F q h1 h2 hx hq
  · exact coverPair33 hr B A E F q h1 h2 hx hq

/-- **q-orthogonality of the 6j symbol at every level `r ≥ 2`**, with the boundary evaluation
`QDougallAll r` proved by `qDougallAll_proved`. -/
theorem qOrthogonality_proved {r : ℕ} (hr : 2 ≤ r) : qOrthogonality hr :=
  qOrthogonality_of hr (qDougallAll_proved hr)

end Lightlike.TV.Refl
