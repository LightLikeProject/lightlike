module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfile

/-!
# Derivatives of the profile polynomials of the discrete series

The generating function `G_l(t, w) = (t + w)^l (1 + t w)^{-(n+l)}` satisfies, pointwise,
`t (1 - t²) ∂_t G_l + l (1 + t²) G_l - (1 - t²) w ∂_w G_l = 2 l t G_{l-1}` and
`t (1 - t²) ∂_t G_l + (1 - t²) w ∂_w G_l - (l (1 + t²) + 2 n t²) G_l = -2 (n + l) t G_{l+1}`
(`genFun_lower_eq`, `genFun_raise_eq`). Taking the `j`-th Taylor coefficient in `w` (where `w ∂_w` becomes the
multiplication by `j`, `discCoeff_mul_deriv`, and `∂_t` commutes with taking the coefficient,
`hasDerivAt_profPoly`) gives the same relations for the profile polynomials `P_{jl}` (`profPoly_lower`,
`profPoly_raise`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `∂_t` of the generating function. -/
def genFunT (n l : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  (l : ℂ) * ((t : ℂ) + w) ^ (l - 1) * ((1 + (t : ℂ) * w) ^ (n + l))⁻¹ -
    ((n + l : ℕ) : ℂ) * w * ((t : ℂ) + w) ^ l * ((1 + (t : ℂ) * w) ^ (n + l + 1))⁻¹

/-- `∂_w` of the generating function. -/
def genFunW (n l : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  (l : ℂ) * ((t : ℂ) + w) ^ (l - 1) * ((1 + (t : ℂ) * w) ^ (n + l))⁻¹ -
    ((n + l : ℕ) : ℂ) * t * ((t : ℂ) + w) ^ l * ((1 + (t : ℂ) * w) ^ (n + l + 1))⁻¹

lemma hasDerivAt_genFun_t (n l : ℕ) (hn : 1 ≤ n) (t : ℝ) (w : ℂ) (hV : 1 + (t : ℂ) * w ≠ 0) :
    HasDerivAt (fun t : ℝ => genFun n l t w) (genFunT n l t w) t := by
  obtain ⟨M, hM⟩ : ∃ M, n + l = M + 1 := ⟨n + l - 1, by omega⟩
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => ((t : ℂ) + w) ^ l) ((l : ℂ) * ((t : ℂ) + w) ^ (l - 1) * 1) t :=
    (h1.add_const w).pow l
  have h3 : HasDerivAt (fun t : ℝ => 1 + (t : ℂ) * w) (1 * w) t := (h1.mul_const w).const_add 1
  have h4 : HasDerivAt (fun t : ℝ => (1 + (t : ℂ) * w) ^ (M + 1))
      (((M + 1 : ℕ) : ℂ) * (1 + (t : ℂ) * w) ^ (M + 1 - 1) * (1 * w)) t := h3.pow (M + 1)
  simp only [Nat.add_sub_cancel] at h4
  have h5 := h4.inv (pow_ne_zero _ hV)
  have h6 := h2.mul h5
  unfold genFun
  rw [hM]
  refine h6.congr_deriv ?_
  unfold genFunT
  rw [hM]
  simp only [Pi.inv_apply, Nat.add_sub_cancel]
  have hx : (1 + (t : ℂ) * w) ^ (M + 1) = (1 + (t : ℂ) * w) ^ M * (1 + (t : ℂ) * w) := pow_succ _ _
  have hx' : (1 + (t : ℂ) * w) ^ (M + 1 + 1) = (1 + (t : ℂ) * w) ^ M * (1 + (t : ℂ) * w) *
      (1 + (t : ℂ) * w) := by rw [pow_succ, pow_succ]
  rw [hx, hx']
  have h7 : (1 + (t : ℂ) * w) ^ M ≠ 0 := pow_ne_zero _ hV
  field_simp
  ring

lemma hasDerivAt_genFun_w (n l : ℕ) (hn : 1 ≤ n) (t : ℝ) (w : ℂ) (hV : 1 + (t : ℂ) * w ≠ 0) :
    HasDerivAt (genFun n l t) (genFunW n l t w) w := by
  obtain ⟨M, hM⟩ : ∃ M, n + l = M + 1 := ⟨n + l - 1, by omega⟩
  have h1 : HasDerivAt (fun w : ℂ => ((t : ℂ) + w) ^ l) ((l : ℂ) * ((t : ℂ) + w) ^ (l - 1) * 1) w :=
    ((hasDerivAt_id w).const_add (t : ℂ)).pow l
  have h3 : HasDerivAt (fun w : ℂ => 1 + (t : ℂ) * w) ((t : ℂ) * 1) w :=
    ((hasDerivAt_id w).const_mul (t : ℂ)).const_add 1
  have h4 : HasDerivAt (fun w : ℂ => (1 + (t : ℂ) * w) ^ (M + 1))
      (((M + 1 : ℕ) : ℂ) * (1 + (t : ℂ) * w) ^ (M + 1 - 1) * ((t : ℂ) * 1)) w := h3.pow (M + 1)
  simp only [Nat.add_sub_cancel] at h4
  have h5 := h4.inv (pow_ne_zero _ hV)
  have h6 := h1.mul h5
  unfold genFun
  rw [hM]
  refine h6.congr_deriv ?_
  unfold genFunW
  rw [hM]
  simp only [Pi.inv_apply, Nat.add_sub_cancel]
  have hx : (1 + (t : ℂ) * w) ^ (M + 1) = (1 + (t : ℂ) * w) ^ M * (1 + (t : ℂ) * w) := pow_succ _ _
  have hx' : (1 + (t : ℂ) * w) ^ (M + 1 + 1) = (1 + (t : ℂ) * w) ^ M * (1 + (t : ℂ) * w) *
      (1 + (t : ℂ) * w) := by rw [pow_succ, pow_succ]
  rw [hx, hx']
  have h7 : (1 + (t : ℂ) * w) ^ M ≠ 0 := pow_ne_zero _ hV
  field_simp
  ring

/-- Pointwise, for `l = k + 1`: the lowering identity for the generating function. -/
lemma genFun_lower_eq (n k : ℕ) (t : ℝ) (w : ℂ) (hV : 1 + (t : ℂ) * w ≠ 0) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * genFunT n (k + 1) t w + ((k + 1 : ℕ) : ℂ) * (1 + (t : ℂ) ^ 2) * genFun n (k + 1) t w -
      (1 - (t : ℂ) ^ 2) * (w * genFunW n (k + 1) t w) = 2 * ((k + 1 : ℕ) : ℂ) * t * genFun n k t w := by
  unfold genFunT genFunW genFun
  have e1 : n + (k + 1) = n + k + 1 := by omega
  have e2 : n + (k + 1) + 1 = n + k + 1 + 1 := by omega
  simp only [e1, e2, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- Pointwise: the raising identity for the generating function. -/
lemma genFun_raise_eq (n l : ℕ) (t : ℝ) (w : ℂ) (hV : 1 + (t : ℂ) * w ≠ 0) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * genFunT n l t w + (1 - (t : ℂ) ^ 2) * (w * genFunW n l t w) -
      ((l : ℂ) * (1 + (t : ℂ) ^ 2) + 2 * (n : ℂ) * (t : ℂ) ^ 2) * genFun n l t w =
      -2 * ((n + l : ℕ) : ℂ) * t * genFun n (l + 1) t w := by
  unfold genFunT genFunW genFun
  have e1 : n + (l + 1) = n + l + 1 := by omega
  simp only [e1]
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    simp only [Nat.cast_zero, zero_mul, zero_sub, zero_add, pow_zero, Nat.zero_sub, mul_one, one_mul]
    push_cast
    field_simp
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- The unit `l = 0` case of the lowering identity. -/
lemma genFun_lower_zero (n : ℕ) (t : ℝ) (w : ℂ) (hV : 1 + (t : ℂ) * w ≠ 0) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * genFunT n 0 t w - (1 - (t : ℂ) ^ 2) * (w * genFunW n 0 t w) = 0 := by
  unfold genFunT genFunW
  simp only [Nat.cast_zero, zero_mul, zero_sub, Nat.zero_add, Nat.zero_sub, pow_zero, mul_one, one_mul]
  field_simp
  ring

end Lightlike.Lorentz.SL2RPlancherel
