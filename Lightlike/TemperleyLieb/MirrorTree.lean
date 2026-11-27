import Mathlib
import Lightlike.TemperleyLieb.Mirror
import Lightlike.TemperleyLieb.CupCap
import Lightlike.TemperleyLieb.Reduction

/-!
# The mirror image of caps and cups

The reflection `reflectOp N` (`Mirror.lean`) reverses and flips the first `N` bits. A cap at the positions
`j, j+1` of a word with `j + j' + 2` letters is turned into the cap at the mirror positions `j', j'+1`
(`reflect_capOp`), and likewise for cups (`reflect_cupOp`): the cap and cup weights only see the pairs `01`
and `10`, which the reflection fixes. With `jwAt_mirror` these are the rules by which the mirror turns the
second-bracketing tree vectors of the blocks `(a, b, c)` into the first-bracketing ones of `(c, b, a)`.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

lemma reflect_removeTwo (σ : ℕ → Bool) (j j' : ℕ) :
    removeTwo (reflect (j + j' + 2) σ) j' = reflect (j + j') (removeTwo σ j) := by
  funext n
  simp only [reflect, removeTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega) | (congr 1; omega)

lemma reflect_insertTwo (σ : ℕ → Bool) (j j' : ℕ) (x y : Bool) :
    reflect (j + j' + 2) (insertTwo σ j x y) = insertTwo (reflect (j + j') σ) j' (!y) (!x) := by
  funext n
  simp only [reflect, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega) | (congr 1; omega)

lemma capWeight_reflect (q : kˣ) (x y : Bool) : capWeight q (!y) (!x) = capWeight q x y := by
  cases x <;> cases y <;> rfl

/-- **The mirror of a cap**: `R_{j+j'} cap_j = cap_{j'} R_{j+j'+2}`. -/
theorem reflect_capOp (q : kˣ) (j j' : ℕ) :
    reflectOp k (j + j') * capOp q j = capOp q j' * reflectOp k (j + j' + 2) := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, reflectOp_single, capOp_single, capBasis, one_smul, reflectOp_single]
  rw [reflect_removeTwo, reflect_apply_lo σ j j', reflect_apply_hi σ j j', capWeight_reflect]

/-- **The mirror of a cup**: `R_{j+j'+2} cup_j = cup_{j'} R_{j+j'}`. -/
theorem reflect_cupOp (q : kˣ) (j j' : ℕ) :
    reflectOp k (j + j' + 2) * cupOp q j = cupOp q j' * reflectOp k (j + j') := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, reflectOp_single, cupOp_single, cupBasis, one_smul, map_sub, map_smul]
  rw [reflect_insertTwo, reflect_insertTwo]
  rfl

/-- The mirror of a projector, as a commutation: `R_{s+s'+m} p_{[s,s+m)} = p_{[s',s'+m)} R_{s+s'+m}`. -/
theorem reflect_jwAt (q : kˣ) (s s' m : ℕ) (hd : ∀ j, j < m → chebD (loopVal q) j ≠ 0) :
    reflectOp k (s + s' + m) * jwAt q s m = jwAt q s' m * reflectOp k (s + s' + m) := by
  rw [jwAt_mirror q s s' m hd, mul_assoc, mul_assoc, reflectOp_mul_self, mul_one]

/-- **The mirror of nested cups**: `R_{n+2i} nestCup_l^i = nestCup_{n-l}^i R_n` for `l ≤ n`. -/
theorem reflect_nestCup (q : kˣ) {l n : ℕ} (hl : l ≤ n) : ∀ i,
    reflectOp k (n + 2 * i) * nestCup q l i = nestCup q (n - l) i * reflectOp k n
  | 0 => by simp [nestCup]
  | i + 1 => by
    have hc := reflect_cupOp (k := k) q (l + i) (n - l + i)
    rw [show l + i + (n - l + i) + 2 = n + 2 * (i + 1) by omega, show l + i + (n - l + i) = n + 2 * i by omega] at hc
    simp only [nestCup]
    rw [← mul_assoc, hc, mul_assoc, reflect_nestCup q hl i, ← mul_assoc]

end Lightlike.TemperleyLieb
