import Lightlike.TuraevViro.Reflect.RacahReal

/-!
# The q-Racah sum of a quantum 6j symbol is `SR`

`qRacahSum r j₁ … j₆` is the sum `SR` for the integer tuple `α₁ … β₃` of the 6j symbol. The
variable `j₃` enters `α₁, α₄, β₂, β₃` (each by `+1` when `j₃` grows by `2`) and not `α₂, α₃, β₁`, so
the recurrence of `RacahReal` is a recurrence in `j₃` with step `2`.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Finset Lightlike.TV

lemma qRacahSum_eq_SR (r j1 j2 j3 j4 j5 j6 : ℕ) :
    qRacahSum r j1 j2 j3 j4 j5 j6 =
      SR r (((j1 + j2 + j3) / 2 : ℕ) : ℤ) (((j1 + j5 + j6) / 2 : ℕ) : ℤ)
        (((j4 + j2 + j6) / 2 : ℕ) : ℤ) (((j4 + j5 + j3) / 2 : ℕ) : ℤ)
        (((j1 + j2 + j4 + j5) / 2 : ℕ) : ℤ) (((j2 + j3 + j5 + j6) / 2 : ℕ) : ℤ)
        (((j3 + j1 + j6 + j4) / 2 : ℕ) : ℤ) := by
  unfold qRacahSum SR
  symm
  refine Finset.sum_subset ?_ ?_
  · intro z hz
    simp only [mem_range] at hz ⊢
    omega
  · intro z hz hz'
    simp only [mem_range] at hz hz'
    apply qRacahTerm_zero_of_gt
    omega

end Lightlike.TV.Refl
