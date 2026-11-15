import Lightlike.TuraevViro.Reflect.RacahReal

/-!
# The recurrence coefficients as quantum integers of the exponents

At `u = e^{iπ/r}` and `p_i = u^{a_i}`, `q_j = u^{b_j}` every recurrence coefficient of the q-Racah
sum is a product of the expressions `bk (u^m)` and `ck (u^m)` with integer `m` that are linear in the
exponents. These are the forms used to read off the dependence on the colours of a 6j symbol.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV

variable (r : ℕ)

private lemma uz (n : ℤ) : uC r ^ n ≠ 0 := zpow_ne_zero _ (uC_ne_zero r)

/-- A product of powers of `u` collapses to one power. -/
lemma uC_mul_zpow (m n : ℤ) : uC r ^ m * uC r ^ n = uC r ^ (m + n) :=
  (zpow_add₀ (uC_ne_zero r) m n).symm

lemma uC_inv_zpow (m : ℤ) : (uC r ^ m)⁻¹ = uC r ^ (-m) := (zpow_neg _ m).symm

lemma uC_zpow_one : uC r = uC r ^ (1 : ℤ) := (zpow_one _).symm


/-- Closes an equality between products of powers of `u` by expanding all `zpow`s. -/
macro "uarg" : tactic =>
  `(tactic| (have hu := uC_ne_zero r
             simp only [zpow_add₀ hu, zpow_sub₀ hu, zpow_neg, zpow_one, zpow_natCast] <;>
             field_simp))

section
variable (a1 a2 a3 a4 b2 b3 : ℤ)

/-- The recurrence coefficient `Na` evaluated at the root of unity. -/
theorem rcR_fNa : rcR r a1 a2 a3 a4 b2 b3 fNa =
    bk (uC r ^ (1 - a3 + b3)) * bk (uC r ^ (1 - a2 + b2)) * bk (uC r ^ (1 - a3 + b2)) *
      bk (uC r ^ (1 - a2 + b3)) := by
  unfold rcR recCoef
  rw [eval_fNa (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) one_ne_zero]
  rw [show uC r * (uC r ^ a3)⁻¹ * uC r ^ b3 = uC r ^ (1 - a3 + b3) by uarg,
    show uC r * (uC r ^ a2)⁻¹ * uC r ^ b2 = uC r ^ (1 - a2 + b2) by uarg,
    show uC r * (uC r ^ a3)⁻¹ * uC r ^ b2 = uC r ^ (1 - a3 + b2) by uarg,
    show uC r * (uC r ^ a2)⁻¹ * uC r ^ b3 = uC r ^ (1 - a2 + b3) by uarg]

theorem rcR_fNc : rcR r a1 a2 a3 a4 b2 b3 fNc =
    bk (uC r ^ (1 + a1)) * bk (uC r ^ (1 + a4)) * bk (uC r ^ (1 + a1 + a2 + a3 - b2 - b3)) *
      bk (uC r ^ (1 + a2 + a3 + a4 - b2 - b3)) := by
  unfold rcR recCoef
  rw [eval_fNc (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) one_ne_zero]
  rw [show uC r * uC r ^ a1 * uC r ^ a2 * uC r ^ a3 * (uC r ^ b2)⁻¹ * (uC r ^ b3)⁻¹
      = uC r ^ (1 + a1 + a2 + a3 - b2 - b3) by uarg,
    show uC r * uC r ^ a2 * uC r ^ a3 * uC r ^ a4 * (uC r ^ b2)⁻¹ * (uC r ^ b3)⁻¹
      = uC r ^ (1 + a2 + a3 + a4 - b2 - b3) by uarg,
    show uC r * uC r ^ a1 = uC r ^ (1 + a1) by uarg,
    show uC r * uC r ^ a4 = uC r ^ (1 + a4) by uarg]

theorem rcR_fCq : rcR r a1 a2 a3 a4 b2 b3 fCq = ck (uC r ^ (1 - a1 - a4 + b2 + b3)) := by
  unfold rcR recCoef
  rw [eval_fCq (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) one_ne_zero]
  rw [show uC r * (uC r ^ a1)⁻¹ * (uC r ^ a4)⁻¹ * uC r ^ b2 * uC r ^ b3
    = uC r ^ (1 - a1 - a4 + b2 + b3) by uarg]

theorem rcR_fQ0 : rcR r a1 a2 a3 a4 b2 b3 fQ0 = bk (uC r ^ (b2 + b3 - a2 - a3)) := by
  unfold rcR
  rw [(recCoef_fQ _ _ _ _ _ _ _ (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _)
    (uz r _)).1]
  rw [show (uC r ^ a2)⁻¹ * (uC r ^ a3)⁻¹ * uC r ^ b2 * uC r ^ b3 = uC r ^ (b2 + b3 - a2 - a3)
    by uarg]

theorem rcR_fQ1 : rcR r a1 a2 a3 a4 b2 b3 fQ1 = bk (uC r ^ (1 + b2 + b3 - a2 - a3)) := by
  unfold rcR
  rw [(recCoef_fQ _ _ _ _ _ _ _ (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _)
    (uz r _)).2.1]
  rw [show uC r * (uC r ^ a2)⁻¹ * (uC r ^ a3)⁻¹ * uC r ^ b2 * uC r ^ b3
    = uC r ^ (1 + b2 + b3 - a2 - a3) by uarg]

theorem rcR_fQ2 : rcR r a1 a2 a3 a4 b2 b3 fQ2 = bk (uC r ^ (2 + b2 + b3 - a2 - a3)) := by
  unfold rcR
  rw [(recCoef_fQ _ _ _ _ _ _ _ (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _)
    (uz r _)).2.2]
  rw [show uC r ^ 2 * (uC r ^ a2)⁻¹ * (uC r ^ a3)⁻¹ * uC r ^ b2 * uC r ^ b3
    = uC r ^ (2 + b2 + b3 - a2 - a3) by uarg]

/-- The middle numerator `bn` evaluated at the root of unity. -/
theorem rcR_fbn : rcR r a1 a2 a3 a4 b2 b3 fbn =
    (ck (uC r ^ (1 + a1 + a2 - b2)) * ck (uC r ^ (1 + a3 + a4 - b2))
        + ck (uC r ^ (1 + a1 + a3 - b3)) * ck (uC r ^ (1 + a2 + a4 - b3)))
        * ck (uC r ^ (1 - a2 - a3 + b2 + b3))
      - (uC r + (uC r)⁻¹) *
        (ck (uC r ^ (1 + a1 + a2 - b2)) * ck (uC r ^ (1 + a2 + a4 - b3))
          + ck (uC r ^ (1 + a1 + a3 - b3)) * ck (uC r ^ (1 + a3 + a4 - b2))) := by
  unfold rcR recCoef
  rw [eval_fbn (uC_ne_zero r) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) (uz r _) one_ne_zero]
  rw [show uC r * uC r ^ a1 * uC r ^ a2 * (uC r ^ b2)⁻¹ = uC r ^ (1 + a1 + a2 - b2) by uarg,
    show uC r * uC r ^ a3 * uC r ^ a4 * (uC r ^ b2)⁻¹ = uC r ^ (1 + a3 + a4 - b2) by uarg,
    show uC r * uC r ^ a1 * uC r ^ a3 * (uC r ^ b3)⁻¹ = uC r ^ (1 + a1 + a3 - b3) by uarg,
    show uC r * uC r ^ a2 * uC r ^ a4 * (uC r ^ b3)⁻¹ = uC r ^ (1 + a2 + a4 - b3) by uarg,
    show uC r * (uC r ^ a2)⁻¹ * (uC r ^ a3)⁻¹ * uC r ^ b2 * uC r ^ b3
      = uC r ^ (1 - a2 - a3 + b2 + b3) by uarg]
  ring

end

end Lightlike.TV.Refl
