import Mathlib
import Lightlike.TemperleyLieb.Expansion
import Lightlike.TemperleyLieb.ShiftComm

/-!
# The five bracketings of four blocks and the relations between them

`TA = ((ab)c)d`, `TB = (a(bc))d`, `TC = a((bc)d)`, `TD = a(b(cd))`, `TE = (ab)(cd)`.
Each arrow of the pentagon is one `expansion` (the `F`-move on three blocks), multiplied by a fixed
operator on the left or on the right.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- `(ab)(cd)` with channels `e` (for `a, b`), `j` (for `c, d`), `g` (total). -/
noncomputable def TE (q : kˣ) (a b c d e j g : ℕ) : Module.End k (ModelSpace k) :=
  Vop q a b e * sh (a + b - 2 * e) (Vop q c d j) * Vop q (a + b - 2 * e) (c + d - 2 * j) g

/-- `UL4` as a left factor times a three-block left tree. -/
theorem UL4_eq (q : kˣ) (a b c d e d₁ g : ℕ) :
    UL4 q a b c d e d₁ g = Vop q a b e * UL q (a + b - 2 * e) c d d₁ g := by
  simp only [UL4, UL, mul_assoc]

/-- A left factor times a three-block right tree. -/
theorem TE_eq_mul_UR (q : kˣ) (a b c d e j g : ℕ) :
    TE q a b c d e j g = Vop q a b e * UR q (a + b - 2 * e) c d j g := by
  simp only [TE, UR, mul_assoc]

/-- **`(ab)(cd)` in the basis `((ab)c)d`** (the arrow `E → A` of the pentagon). -/
theorem TE_expand [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d e j g : ℕ) (hc : 1 ≤ c)
    (hd : ∀ i, i ≤ a + b + c + d → chebD (loopVal q) i ≠ 0)
    (hq2 : ∀ i, 1 ≤ i → i ≤ a + b + c + d + 1 → (q : k) ^ (2 * i) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hjc : j ≤ c) (hjd : j ≤ d)
    (hga : g ≤ a + b - 2 * e) (hgf : g ≤ c + d - 2 * j) :
    TE q a b c d e j g = ∑ d₁ ∈ Finset.range (a + b - 2 * e + 1), ∑ g' ∈ Finset.range (d + 1),
      Fc q (a + b - 2 * e) c d d₁ g' j g • UL4 q a b c d e d₁ g' := by
  rw [TE_eq_mul_UR, expansion_range q hδ (a + b - 2 * e) c d j g (by omega)
    (fun i hi => hd i (by omega)) (fun i h1 h2 => hq2 i h1 (by omega)) hjc hjd hga hgf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [UL4_eq, mul_smul_comm]

end Lightlike.TemperleyLieb
