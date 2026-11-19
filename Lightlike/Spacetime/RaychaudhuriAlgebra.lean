import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The algebra of the Raychaudhuri identity

The index computation behind the Raychaudhuri equation, for abstract arrays: `V` (the vector field at a point),
`D a b = ∂_b v^a`, `H a b c = ∂_c ∂_b v^a`, `Γ` (the Christoffel symbols) and `dΓ a b c d = ∂_d Γ^a_{bc}`.
From the derivative of the geodesic equation (`hE`) and the geodesic equation itself (`hG`) it follows that
`v^c ∂_c (∇_a v^a) = -(∇_b v^a)(∇_a v^b) - R_{σν} v^σ v^ν` (`raychaudhuri_algebra`).
-/

open Finset

namespace Lightlike.Raychaudhuri

variable {n : ℕ}

lemma sum3_rot (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

lemma sum3_rev (F : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [sum3_rot]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma sum4_perm (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ e, ∑ c, ∑ a, ∑ b, F a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, F a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, F a b c e := Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ a, ∑ b, F a b c e := Finset.sum_comm

/-- **The index computation of the Raychaudhuri identity.** -/
theorem raychaudhuri_algebra (V : Fin n → ℝ) (D : Fin n → Fin n → ℝ) (H : Fin n → Fin n → Fin n → ℝ)
    (Γ : Fin n → Fin n → Fin n → ℝ) (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hH : ∀ a b c, H a b c = H a c b) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hE : ∀ a, ∑ b, (D b a * (D a b + ∑ c, Γ a b c * V c) +
      V b * (H a b a + ∑ c, (dΓ a b c a * V c + Γ a b c * D c a))) = 0)
    (hG : ∀ d, ∑ c, V c * (D d c + ∑ e, Γ d c e * V e) = 0) :
    ∑ c, V c * ∑ a, (H a a c + ∑ d, (dΓ a a d c * V d + Γ a a d * D d c)) =
      -(∑ a, ∑ b, (D a b + ∑ c, Γ a b c * V c) * (D b a + ∑ c, Γ b a c * V c)) -
        ∑ s, ∑ t, (∑ r, (dΓ r t s r - dΓ r r s t + ∑ l, (Γ r r l * Γ l t s - Γ r t l * Γ l r s))) *
          V s * V t := by
  -- the named sums
  set A1 := ∑ c, ∑ a, V c * H a a c with hA1
  set A2 := ∑ c, ∑ a, ∑ d, V c * (dΓ a a d c * V d) with hA2
  set A3 := ∑ c, ∑ a, ∑ d, V c * (Γ a a d * D d c) with hA3
  set B1 := ∑ a, ∑ b, D a b * D b a with hB1
  set B2 := ∑ a, ∑ b, ∑ c, D a b * (Γ b a c * V c) with hB2
  set B4 := ∑ a, ∑ b, ∑ c, ∑ e, Γ a b c * V c * (Γ b a e * V e) with hB4
  set C1 := ∑ s, ∑ t, ∑ r, dΓ r t s r * V s * V t with hC1
  set C2 := ∑ s, ∑ t, ∑ r, dΓ r r s t * V s * V t with hC2
  set C3 := ∑ s, ∑ t, ∑ r, ∑ l, Γ r r l * Γ l t s * V s * V t with hC3
  set C4 := ∑ s, ∑ t, ∑ r, ∑ l, Γ r t l * Γ l r s * V s * V t with hC4
  have hL : ∑ c, V c * ∑ a, (H a a c + ∑ d, (dΓ a a d c * V d + Γ a a d * D d c)) = A1 + A2 + A3 := by
    simp only [hA1, hA2, hA3, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    ring
  have hT : ∑ a, ∑ b, (D a b + ∑ c, Γ a b c * V c) * (D b a + ∑ c, Γ b a c * V c) =
      B1 + 2 * B2 + B4 := by
    have e3 : ∑ a, ∑ b, ∑ c, Γ a b c * V c * D b a = B2 := by
      rw [hB2, Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun c _ => by ring
    have e : ∀ a b, (D a b + ∑ c, Γ a b c * V c) * (D b a + ∑ c, Γ b a c * V c) =
        D a b * D b a + ∑ c, D a b * (Γ b a c * V c) + ∑ c, Γ a b c * V c * D b a +
          ∑ c, ∑ e, Γ a b c * V c * (Γ b a e * V e) := fun a b => by
      rw [add_mul, mul_add, mul_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul_sum]
      ring
    simp only [e, Finset.sum_add_distrib]
    rw [e3]
    ring
  have hR : ∑ s, ∑ t, (∑ r, (dΓ r t s r - dΓ r r s t + ∑ l, (Γ r r l * Γ l t s - Γ r t l * Γ l r s))) *
      V s * V t = C1 - C2 + C3 - C4 := by
    simp only [hC1, hC2, hC3, hC4, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      add_mul, sub_mul]
    ring
  -- the derivative of the geodesic equation, summed
  have hEs : B1 + B2 + A1 + C1 + B2 = 0 := by
    have h0 : ∑ a, ∑ b, (D b a * (D a b + ∑ c, Γ a b c * V c) +
        V b * (H a b a + ∑ c, (dΓ a b c a * V c + Γ a b c * D c a))) = 0 :=
      Finset.sum_eq_zero fun a _ => hE a
    have e1 : ∑ a, ∑ b, D b a * D a b = B1 :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have e2 : ∑ a, ∑ b, ∑ c, D b a * (Γ a b c * V c) = B2 := by
      rw [hB2, Finset.sum_comm]
    have e3 : ∑ a, ∑ b, V b * H a b a = A1 := by
      rw [hA1, Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [hH a c a]
    have e4 : ∑ a, ∑ b, ∑ c, V b * (dΓ a b c a * V c) = C1 := by
      rw [hC1, sum3_rev]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun a _ => by ring
    have e5 : ∑ a, ∑ b, ∑ c, V b * (Γ a b c * D c a) = B2 := by
      rw [hB2, sum3_rot]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by rw [hΓ a b c]; ring
    have h1 : ∑ a, ∑ b, (D b a * (D a b + ∑ c, Γ a b c * V c) +
        V b * (H a b a + ∑ c, (dΓ a b c a * V c + Γ a b c * D c a))) =
        ∑ a, ∑ b, D b a * D a b + ∑ a, ∑ b, ∑ c, D b a * (Γ a b c * V c) + ∑ a, ∑ b, V b * H a b a +
          ∑ a, ∑ b, ∑ c, V b * (dΓ a b c a * V c) + ∑ a, ∑ b, ∑ c, V b * (Γ a b c * D c a) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      ring
    rw [h1, e1, e2, e3, e4, e5] at h0
    linarith
  -- the geodesic equation, contracted with `Γ^a_{ad}`
  have hGs : A3 + C3 = 0 := by
    have h0 : ∑ a, ∑ d, Γ a a d * ∑ c, V c * (D d c + ∑ e, Γ d c e * V e) = 0 :=
      Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun d _ => by rw [hG d, mul_zero]
    have k1 : ∑ a, ∑ d, ∑ c, Γ a a d * (V c * D d c) = A3 := by
      rw [hA3, sum3_rot]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun d _ => by ring
    have k2 : ∑ a, ∑ d, ∑ c, ∑ e, Γ a a d * (V c * (Γ d c e * V e)) = C3 := by
      rw [hC3, sum4_perm]
      exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => by ring
    have h1 : ∑ a, ∑ d, Γ a a d * ∑ c, V c * (D d c + ∑ e, Γ d c e * V e) =
        ∑ a, ∑ d, ∑ c, Γ a a d * (V c * D d c) + ∑ a, ∑ d, ∑ c, ∑ e, Γ a a d * (V c * (Γ d c e * V e)) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    rw [h1, k1, k2] at h0
    exact h0
  have hAC : A2 = C2 := by
    rw [hA2, hC2, sum3_rot]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun a _ => by ring
  have hBC : B4 = C4 := by
    rw [hB4, hC4, sum4_perm]
    exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hΓ a c b]; ring
  rw [hL, hT, hR]
  linarith

end Lightlike.Raychaudhuri
