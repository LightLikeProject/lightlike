import Lightlike.TuraevViro.Reflect.OrthInterior
import Lightlike.TuraevViro.TuraevViro

/-!
# q-orthogonality of the 6j symbol, conditional

`qOrthogonality r` follows from one named hypothesis, the boundary evaluation `QDougallAll` (the
terminating very-well-poised sum). The endpoint rows of the recurrence, at the third colours `0`
and `r - 2`, are proved, so no hypothesis about the edge colours remains.
-/

set_option maxHeartbeats 400000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- **Hypothesis (boundary evaluation).** The norm of the lowest column is `1`. -/
def QDougallAll (r : ℕ) : Prop :=
  ∀ B A E F q : ℕ, qAdm r B F q → qAdm r E A q → QDougallAt r B A E F

/-- **q-orthogonality of the 6j symbol**, given the boundary evaluation. -/
theorem qOrthogonality_of {r : ℕ} (hr : 2 ≤ r) (hD : QDougallAll r) :
    qOrthogonality hr := by
  intro B A E F q
  show ∑ x ∈ range (r - 1), qnum r (x + 1) * qSixJ r B A x E F q ^ 2 =
    if qAdm r A E q ∧ qAdm r B q F then 1 / qnum r (q + 1) else 0
  by_cases hok : qAdm r A E q ∧ qAdm r B q F
  · simp only [hok]
    have h1 : qAdm r B F q := qAdm_swap23 hok.2
    have h2 : qAdm r E A q := qAdm_swap12 hok.1
    exact orth_interior hr B A E F q h1 h2 (hD B A E F q h1 h2)
  · simp only [hok, ↓reduceIte]
    refine Finset.sum_eq_zero fun x _ => ?_
    have : qSixJ r B A x E F q = 0 := by
      by_contra h
      obtain ⟨-, h2, h3, -⟩ := qSixJ_ok h
      exact hok ⟨qAdm_swap12 h3, qAdm_swap23 h2⟩
    rw [this]; simp

end Lightlike.TV.Refl
