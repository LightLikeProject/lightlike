import Mathlib
import Lightlike.TemperleyLieb.JwNatural
import Lightlike.TemperleyLieb.Vertex

/-!
# Contracting the junction of two projectors

For `a = α + 2`, `b = β + 2` let `Q = p_a p_b'` (the projectors on the strands `0..a-1` and `a..a+b-1`) and
`Q'' = p_{a-1} p''_{b-1}` (on `0..a-2` and `a-1..a+b-3`), `J = e_{a-2}`.  Then
`cap_{a-1} Q cup_{a-1} = (δ - s - t) Q'' + s t Q'' J Q''`, with `s = d_{a-2}/d_{a-1}`, `t = d_{b-2}/d_{b-1}`
(`contraction`).  It is obtained by expanding both projectors with the Jones–Wenzl recursion from the junction
end (`jw_succ_succ`, `jwAt_succ_succ_left`) and moving the cap and cup through the pieces.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- `cap_m cup_{m+2} = e_m`. -/
theorem cap_cup_far_zero (q : kˣ) (m : ℕ) : capOp q m * cupOp q (m + 2) = modelE q m := by
  have h1 : cupOp q (m + 2) = modelE q (m + 2) * cupOp q (m + 1) := (e_mul_cup_succ q (m + 1)).symm
  rw [h1, ← mul_assoc, cap_mul_e_far q (le_refl m), mul_assoc, cap_cup_succ, mul_one]

/-- Projectors on disjoint blocks of strands commute. -/
theorem jwAt_comm_far (q : kˣ) {s n s' n' : ℕ} (h : s + n ≤ s') :
    jwAt q s n * jwAt q s' n' = jwAt q s' n' * jwAt q s n := by
  rcases n with _ | n
  · simp [jwAt, jw_zero]
  · have hx := jwAt_mem q s (n + 1)
    have hc : ∀ j, jwAt q s (n + 1) * modelE q (j + s') = modelE q (j + s') * jwAt q s (n + 1) := fun j =>
      (comm_tlSub (modelE_isTL q) (m := s + (n + 1) - 1) (n := j + s') (by omega) hx).symm
    exact jw_intertwine (loopVal q) (jwAt q s (n + 1)) _ _ n' (fun j _ => hc j)

/-- **The contraction in an abstract ring.**  If the cap `c` and cup `u` satisfy the relations
listed (all of which hold in the model, see `contraction`), then the sandwich of the product of the expanded
projectors is `(δ - s - t) Q'' + s t Q'' J Q''`. -/
theorem contraction_abstract {A : Type*} [Ring A] [Algebra k A] (δ s t : k)
    (c u Pl Pr Pr2 Ea Eb capa capb cupb : A)
    (h_cu : c * u = algebraMap k A δ) (h_Pl_c : c * Pl = Pl * c) (h_Pl_u : u * Pl = Pl * u)
    (h_Pr_c : c * Pr = Pr2 * c) (h_Pr_u : u * Pr2 = Pr * u) (h_comm : Pl * Pr = Pr * Pl)
    (h_cEb : c * Eb = capb) (h_capb_u : capb * u = 1) (h_cEa : c * Ea = capa)
    (h_capa_u : capa * u = 1) (h_Eb_u : Eb * u = cupb) (h_capa_Pr : capa * Pr = Pr2 * capa)
    (h_Pl_cupb : Pl * cupb = cupb * Pl) (h_capa_cupb : capa * cupb = Ea)
    (h_Pl_idem : Pl * Pl = Pl) (h_Pr2_idem : Pr2 * Pr2 = Pr2) (h_Pl_Pr2 : Pl * Pr2 = Pr2 * Pl) :
    c * ((Pl - s • (Pl * Ea * Pl)) * (Pr - t • (Pr * Eb * Pr))) * u =
      (δ - s - t) • (Pl * Pr2) + (s * t) • ((Pl * Pr2) * Ea * (Pl * Pr2)) := by
  -- right-associated rewriting rules: push `c` to the right and `u` to the left
  have R1 : ∀ x, c * (Pl * x) = Pl * (c * x) := fun x => by rw [← mul_assoc, h_Pl_c, mul_assoc]
  have R2 : ∀ x, c * (Pr * x) = Pr2 * (c * x) := fun x => by rw [← mul_assoc, h_Pr_c, mul_assoc]
  have R3 : ∀ x, c * (Eb * x) = capb * x := fun x => by rw [← mul_assoc, h_cEb]
  have R4 : ∀ x, c * (Ea * x) = capa * x := fun x => by rw [← mul_assoc, h_cEa]
  have R5 : ∀ x, Pr * (u * x) = u * (Pr2 * x) := fun x => by rw [← mul_assoc, ← h_Pr_u, mul_assoc]
  have R6 : ∀ x, Pl * (u * x) = u * (Pl * x) := fun x => by rw [← mul_assoc, ← h_Pl_u, mul_assoc]
  have R7 : ∀ x, capb * (u * x) = x := fun x => by rw [← mul_assoc, h_capb_u, one_mul]
  have R8 : ∀ x, capa * (u * x) = x := fun x => by rw [← mul_assoc, h_capa_u, one_mul]
  have R9 : ∀ x, Eb * (u * x) = cupb * x := fun x => by rw [← mul_assoc, h_Eb_u]
  have R10 : ∀ x, capa * (Pr * x) = Pr2 * (capa * x) := fun x => by rw [← mul_assoc, h_capa_Pr, mul_assoc]
  have R11 : ∀ x, Pl * (cupb * x) = cupb * (Pl * x) := fun x => by rw [← mul_assoc, h_Pl_cupb, mul_assoc]
  have R12 : ∀ x, capa * (cupb * x) = Ea * x := fun x => by rw [← mul_assoc, h_capa_cupb]
  have I1 : ∀ x, Pl * (Pl * x) = Pl * x := fun x => by rw [← mul_assoc, h_Pl_idem]
  have I2 : ∀ x, Pr2 * (Pr2 * x) = Pr2 * x := fun x => by rw [← mul_assoc, h_Pr2_idem]
  have P5 : Pr * u = u * Pr2 := h_Pr_u.symm
  have P6 : Pl * u = u * Pl := h_Pl_u.symm
  have S1 : c * (Pl * (Pr * Eb * Pr)) * u = Pl * Pr2 := by
    simp only [mul_assoc, R1, R2, R3, R5, P5, h_capb_u, R7, mul_one, I2, h_Pr2_idem]
  have S0 : c * (Pl * Pr) * u = δ • (Pl * Pr2) := by
    simp only [mul_assoc, R1, R2, h_cu, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have S2 : c * ((Pl * Ea * Pl) * Pr) * u = Pl * Pr2 := by
    simp only [mul_assoc, R1, R4, R10, P5, P6, R6, R8, I1, mul_one, h_Pl_idem, h_capa_u]
  have S3 : c * ((Pl * Ea * Pl) * (Pr * Eb * Pr)) * u = (Pl * Pr2) * Ea * (Pl * Pr2) := by
    have R13 : ∀ x, Pl * (Pr * x) = Pr * (Pl * x) := fun x => by rw [← mul_assoc, h_comm, mul_assoc]
    simp only [mul_assoc, R1, R4, R2, R3, R5, R6, R9, P5, P6, mul_one, R13, R11, R10, R12]
  have expand : (Pl - s • (Pl * Ea * Pl)) * (Pr - t • (Pr * Eb * Pr)) =
      Pl * Pr - t • (Pl * (Pr * Eb * Pr)) - s • ((Pl * Ea * Pl) * Pr) + (s * t) • ((Pl * Ea * Pl) * (Pr * Eb * Pr)) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_smul]
    module
  rw [expand]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, S0, S1, S2, S3]
  module

/-- **Contraction of the junction** (`a = α + 2`, `b = β + 2`): with `Q'' = p_{a-1} p''_{b-1}`,
`s = d_α / d_{α+1}`, `t = d_β / d_{β+1}` and `J = e_α`,
`cap_{a-1} (p_a p_b') cup_{a-1} = (δ - s - t) Q'' + s t Q'' J Q''`. -/
theorem contraction (q : kˣ) (α β : ℕ) (hd : ∀ j, j ≤ α + β + 2 → chebD (loopVal q) j ≠ 0) :
    capOp q (α + 1) * (jwAt q 0 (α + 2) * jwAt q (α + 2) (β + 2)) * cupOp q (α + 1) =
      (loopVal q - chebD (loopVal q) α / chebD (loopVal q) (α + 1) -
          chebD (loopVal q) β / chebD (loopVal q) (β + 1)) •
        (jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1)) +
      (chebD (loopVal q) α / chebD (loopVal q) (α + 1) *
          (chebD (loopVal q) β / chebD (loopVal q) (β + 1))) •
        ((jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1)) * modelE q α *
          (jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1))) := by
  have hPl : jwAt q 0 (α + 2) = jwAt q 0 (α + 1) -
      (chebD (loopVal q) α / chebD (loopVal q) (α + 1)) •
        (jwAt q 0 (α + 1) * modelE q α * jwAt q 0 (α + 1)) := jw_succ_succ α
  have hPr : jwAt q (α + 2) (β + 2) = jwAt q (α + 3) (β + 1) -
      (chebD (loopVal q) β / chebD (loopVal q) (β + 1)) •
        (jwAt q (α + 3) (β + 1) * modelE q (α + 2) * jwAt q (α + 3) (β + 1)) :=
    jwAt_succ_succ_left q (α + 2) β (fun j hj => hd j (by omega))
  have p1 := jwProps_of_le (isTL_shift q 0) (α + 1) (fun j hj => hd j (by omega)) (α + 1) le_rfl
  have p2 := jwProps_of_le (isTL_shift q (α + 1)) (β + 1) (fun j hj => hd j (by omega)) (β + 1) le_rfl
  rw [hPl, hPr]
  exact contraction_abstract (loopVal q) _ _ (capOp q (α + 1)) (cupOp q (α + 1))
    (jwAt q 0 (α + 1)) (jwAt q (α + 3) (β + 1)) (jwAt q (α + 1) (β + 1)) (modelE q α) (modelE q (α + 2))
    (capOp q α) (capOp q (α + 2)) (cupOp q (α + 2))
    (cap_cup q (α + 1)) (cap_mul_jwAt_near q (m := α + 1) (s := 0) (n := α + 1) (by omega))
    (cup_mul_jwAt_near q (m := α + 1) (s := 0) (n := α + 1) (by omega))
    (cap_mul_jwAt_far q (le_refl _) _) (cup_mul_jwAt_far q (le_refl _) _)
    (jwAt_comm_far q (by omega)) (cap_mul_e_succ q (α + 1)) (cap_succ_cup q (α + 1))
    (cap_mul_e_pred q α) (cap_cup_succ q α) (e_mul_cup_succ q (α + 1))
    (cap_mul_jwAt_far q (m := α) (s := α + 1) (by omega) _)
    (cup_mul_jwAt_near q (m := α + 2) (s := 0) (n := α + 1) (by omega)).symm (cap_cup_far_zero q α)
    p1.idem p2.idem (jwAt_comm_far q (by omega))

end Lightlike.TemperleyLieb
