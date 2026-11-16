import Lightlike.TuraevViro.Reflect.SixJRow

/-!
# The trigonometric identity behind the endpoint rows

At the lowest third colour the q-Racah sums of the recurrence have one and two terms. After dividing
by the single term, the endpoint row becomes an identity between the quantum integers `[n₁], [n₂], [n₃]`
of the three exponents of the term, where `n₁ + n₂ = q`, `n₂ + n₃ = j₁` and `n₁ + n₃ = j₄`.
It is an identity of Laurent polynomials in `u`, `u^{n₁}`, `u^{n₂}`, `u^{n₃}`, proved by `field_simp`.
-/

set_option maxHeartbeats 400000

namespace Lightlike.TV.Refl

open Lightlike.TV

/-- The identity of the endpoint row, for any `u ≠ 0`, in the variables `p_i = u^{n_i}`. -/
lemma end_trig_alg (u p1 p2 p3 : ℂ) (hu : u ≠ 0) (h1 : p1 ≠ 0) (h2 : p2 ≠ 0) (h3 : p3 ≠ 0) :
    (p1 - p1⁻¹) * (p2 - p2⁻¹) - (p1 * p2 * p3 * u ^ 2 - (p1 * p2 * p3 * u ^ 2)⁻¹) * (p3 - p3⁻¹)
      + (u * p2 * p3 + (u * p2 * p3)⁻¹) * (u * p1 * p3 + (u * p1 * p3)⁻¹)
      = (u + u⁻¹) * (u * p1 * p2 + (u * p1 * p2)⁻¹) := by
  field_simp
  ring

/-- The endpoint identity in terms of `bz` and `cz`. -/
lemma end_trig (r n1 n2 n3 : ℕ) :
    bz r n1 * bz r n2 - bz r ((n1 + n2 + n3 + 2 : ℕ) : ℤ) * bz r n3
      + cz r ((n2 + n3 + 1 : ℕ) : ℤ) * cz r ((n1 + n3 + 1 : ℕ) : ℤ)
      = cz r 1 * cz r ((n1 + n2 + 1 : ℕ) : ℤ) := by
  have hu := uC_ne_zero r
  have hp : ∀ n : ℕ, uC r ^ (n : ℤ) ≠ 0 := fun n => zpow_ne_zero _ hu
  have := end_trig_alg (uC r) (uC r ^ (n1 : ℤ)) (uC r ^ (n2 : ℤ)) (uC r ^ (n3 : ℤ)) hu (hp n1)
    (hp n2) (hp n3)
  unfold bz cz bk ck
  simp only [zpow_natCast, zpow_one, pow_add, pow_one] at this ⊢
  linear_combination this

/-- The identity of the top endpoint row, under the constraint `p₁p₂p₃p₄u² = -1` (that is
`u^(k₁+k₂+k₃+k₄+2) = u^r = -1`). -/
lemma end_trig_top_alg (u p1 p2 p3 p4 : ℂ) (hu : u ≠ 0) (h1 : p1 ≠ 0) (h2 : p2 ≠ 0) (h3 : p3 ≠ 0)
    (h4 : p4 ≠ 0) (h : p1 * p2 * p3 * p4 * u ^ 2 = -1) :
    -((p1 - p1⁻¹) * (p2 - p2⁻¹)) + (p3 - p3⁻¹) * (p4 - p4⁻¹)
      - (u * p2 * p4 + (u * p2 * p4)⁻¹) * (u * p1 * p4 + (u * p1 * p4)⁻¹)
      = (u + u⁻¹) * (u * p3 * p4 + (u * p3 * p4)⁻¹) := by
  have e : p4 = -(p1 * p2 * p3 * u ^ 2)⁻¹ := by
    field_simp; linear_combination h
  subst e
  field_simp
  ring

lemma uC_pow_self {r : ℕ} (hr : 2 ≤ r) : uC r ^ r = -1 := by
  have h := uC_zpow r (r : ℤ)
  have hr' : (r : ℝ) ≠ 0 := by positivity
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [zpow_natCast] at h
  rw [h]
  have : ((((r : ℤ) : ℝ) * Real.pi / r : ℝ) : ℂ) = (Real.pi : ℂ) := by
    push_cast; field_simp
  rw [this, mul_comm, Complex.exp_pi_mul_I]

/-- The top endpoint identity. -/
lemma end_trig_top {r : ℕ} (hr : 2 ≤ r) (k1 k2 k3 k4 : ℕ) (h : k1 + k2 + k3 + k4 + 2 = r) :
    -(bz r k1 * bz r k2) + bz r k3 * bz r k4
      - cz r ((k2 + k4 + 1 : ℕ) : ℤ) * cz r ((k1 + k4 + 1 : ℕ) : ℤ)
      = cz r 1 * cz r ((k3 + k4 + 1 : ℕ) : ℤ) := by
  have hu := uC_ne_zero r
  have hp : ∀ n : ℕ, uC r ^ n ≠ 0 := fun n => pow_ne_zero _ hu
  have hc : uC r ^ k1 * uC r ^ k2 * uC r ^ k3 * uC r ^ k4 * uC r ^ 2 = -1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, h]; exact uC_pow_self hr
  have := end_trig_top_alg (uC r) (uC r ^ k1) (uC r ^ k2) (uC r ^ k3) (uC r ^ k4) hu (hp k1)
    (hp k2) (hp k3) (hp k4) hc
  unfold bz cz bk ck
  simp only [zpow_natCast, zpow_one, pow_add, pow_one] at this ⊢
  linear_combination this

end Lightlike.TV.Refl
