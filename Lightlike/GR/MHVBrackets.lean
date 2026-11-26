import Lightlike.GR.MHVFive

/-!
# Bracket formulas for the invariants of momentum sums

For `p_t = nullMom (l t) (lt t)` the invariant masses and the products with the reference momentum of sums of
consecutive momenta are sums of brackets: `mdot (Σ_{t=a}^b p_t) (Σ_{t=a}^b p_t) = ½ Σ_{s,t} ⟨s t⟩ [s t]` and
`mdot (Σ_{t=a}^b p_t) (nullMom (l 1) (lt 0)) = ½ Σ_t ⟨t 0⟩ [t 1]`. These make every hypothesis of the recursion a finite
statement about brackets, so that explicit kinematics can be checked by `norm_num`.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

open Finset

/-- **The invariant mass of consecutive gluons**: `P² = ½ Σ_{s,t} ⟨s t⟩ [s t]` over the range. -/
lemma mdot_range_self (l lt : ℕ → Fin 2 → ℂ) (a b : ℕ) :
    mdot (momRange (fun t => nullMom (l t) (lt t)) a b) (momRange (fun t => nullMom (l t) (lt t)) a b) =
      ∑ s ∈ Ico a (b + 1), ∑ t ∈ Ico a (b + 1), (1 / 2 : ℂ) * (angleBr (lt s) (lt t) * squareBr (l s) (l t)) := by
  unfold momRange
  rw [mdot_sum_left]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mdot_sum_right]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mdot_nullMom_two]; ring

/-- **The product of a range momentum with the reference momentum** `nullMom (l 1) (lt 0)`. -/
lemma mdot_range_ref (l lt : ℕ → Fin 2 → ℂ) (a b : ℕ) :
    mdot (momRange (fun t => nullMom (l t) (lt t)) a b) (nullMom (l 1) (lt 0)) =
      ∑ s ∈ Ico a (b + 1), (1 / 2 : ℂ) * (angleBr (lt s) (lt 0) * squareBr (l s) (l 1)) := by
  unfold momRange
  rw [mdot_sum_left]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mdot_nullMom_two]; ring

/-- **The pole of the channel `[1, d]` in brackets**. -/
lemma zpole_eq_sums (l lt : ℕ → Fin 2 → ℂ) (d : ℕ) :
    zpole l lt d =
      -(∑ s ∈ Ico 1 (d + 1), ∑ t ∈ Ico 1 (d + 1), (1 / 2 : ℂ) * (angleBr (lt s) (lt t) * squareBr (l s) (l t))) /
        (-2 * ∑ s ∈ Ico 1 (d + 1), (1 / 2 : ℂ) * (angleBr (lt s) (lt 0) * squareBr (l s) (l 1))) := by
  unfold zpole
  rw [shiftedMom_zero, mdot_range_self, mdot_range_ref]

end Lightlike.SpinorHelicity
