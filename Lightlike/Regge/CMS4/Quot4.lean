import Lightlike.Regge.CMS4.Schur4

/-!
# Positivity of the plane quotient form in dimension 4

For a positive definite `G` and independent axis vectors `w₁, w₂` the Gram determinant `gramW` is
positive, the quotient form `bf2` is symmetric, and `bf2 u u` is the `G`-norm of the component of
`u` orthogonal to the axis, hence nonnegative, and positive when `det (w₁, w₂, u, v) ≠ 0`.

## Main results

* `bf2_symm`, `bf2_eq_quad`, `bf2_diag_nonneg`;
* `gramW_pos`: `0 < gramW G w₁ w₂` for independent `w₁, w₂`;
* `bf2_diag_pos`: `0 < bf2 G w₁ w₂ t t` when `det4 w₁ w₂ t v ≠ 0`.
-/

open Matrix

namespace Lightlike.Regge4

variable {G : Matrix (Fin 4) (Fin 4) ℝ}

theorem sym_pair (hs : Gᵀ = G) (a b : Fin 4 → ℝ) : a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]

/-- The quotient form is symmetric. -/
theorem bf2_symm (hs : Gᵀ = G) (w₁ w₂ u v : Fin 4 → ℝ) :
    bf2 G w₁ w₂ u v = bf2 G w₁ w₂ v u := by
  have e1 := sym_pair hs w₂ w₁
  have e2 := sym_pair hs u w₁
  have e3 := sym_pair hs u w₂
  have e4 := sym_pair hs v w₁
  have e5 := sym_pair hs v w₂
  have e6 := sym_pair hs v u
  unfold bf2 gramW
  simp only [e1, e2, e3, e4, e5, e6]
  ring

/-- The orthogonal component of `u` to the axis `(w₁, w₂)`, with the coefficients of the normal
equations written out. -/
noncomputable def perp (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  u - (((w₂ ⬝ᵥ (G *ᵥ w₂)) * (w₁ ⬝ᵥ (G *ᵥ u)) - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₂ ⬝ᵥ (G *ᵥ u)))
      / gramW G w₁ w₂) • w₁
    - (((w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ u)) - (w₂ ⬝ᵥ (G *ᵥ w₁)) * (w₁ ⬝ᵥ (G *ᵥ u)))
      / gramW G w₁ w₂) • w₂

/-- `bf2 u u` is the `G`-norm squared of the component of `u` orthogonal to the axis. -/
theorem bf2_eq_quad (hs : Gᵀ = G) (w₁ w₂ u : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ u u = perp G w₁ w₂ u ⬝ᵥ (G *ᵥ perp G w₁ w₂ u) := by
  have e1 := sym_pair hs w₂ w₁
  have e2 := sym_pair hs u w₁
  have e3 := sym_pair hs u w₂
  unfold perp
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  unfold bf2
  simp only [e1, e2, e3]
  have hDeq : gramW G w₁ w₂ = (w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ w₂))
      - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₁ ⬝ᵥ (G *ᵥ w₂)) := by unfold gramW; rw [e1]
  rw [hDeq] at hD ⊢
  clear hDeq e1 e2 e3 hs
  generalize w₁ ⬝ᵥ (G *ᵥ w₁) = A at *
  generalize w₂ ⬝ᵥ (G *ᵥ w₂) = B at *
  generalize w₁ ⬝ᵥ (G *ᵥ w₂) = c at *
  generalize w₁ ⬝ᵥ (G *ᵥ u) = p at *
  generalize w₂ ⬝ᵥ (G *ᵥ u) = q at *
  generalize u ⬝ᵥ (G *ᵥ u) = U at *
  have hD2 : B * A - c ^ 2 ≠ 0 := fun h => hD (by linear_combination h)
  field_simp
  ring

/-- `bf2 u u` is nonnegative for a positive definite `G` and a nondegenerate axis. -/
theorem bf2_diag_nonneg (hG : G.PosDef) (w₁ w₂ u : Fin 4 → ℝ) (hD : gramW G w₁ w₂ ≠ 0) :
    0 ≤ bf2 G w₁ w₂ u u := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  rw [bf2_eq_quad hs w₁ w₂ u hD]
  by_cases h0 : perp G w₁ w₂ u = 0
  · rw [h0, Matrix.mulVec_zero, dotProduct_zero]
  · simpa using (hG.dotProduct_mulVec_pos h0).le

/-- **The Gram determinant of two independent vectors is positive** for a positive definite
form. -/
theorem gramW_pos (hG : G.PosDef) (w₁ w₂ : Fin 4 → ℝ)
    (hi : ∀ c d : ℝ, c • w₁ + d • w₂ = 0 → c = 0 ∧ d = 0) : 0 < gramW G w₁ w₂ := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have hw1 : w₁ ≠ 0 := fun h => by simpa [h] using (hi 1 0 (by simp [h]))
  have ha : 0 < w₁ ⬝ᵥ (G *ᵥ w₁) := by simpa using hG.dotProduct_mulVec_pos hw1
  set a := w₁ ⬝ᵥ (G *ᵥ w₁) with hadef
  set c := w₁ ⬝ᵥ (G *ᵥ w₂) with hcdef
  set z : Fin 4 → ℝ := a • w₂ - c • w₁ with hz
  have hz0 : z ≠ 0 := by
    intro h
    have := hi (-c) a (by rw [hz] at h; rw [← h]; module)
    exact ha.ne' this.2
  have hq : 0 < z ⬝ᵥ (G *ᵥ z) := by simpa using hG.dotProduct_mulVec_pos hz0
  have e1 := sym_pair hs w₂ w₁
  have : z ⬝ᵥ (G *ᵥ z) = a * gramW G w₁ w₂ := by
    simp only [hz, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul, gramW, e1]
    rw [← hcdef, ← hadef]
    ring
  rw [this] at hq
  exact (pos_iff_pos_of_mul_pos hq).1 ha

/-- **The quotient norm of a vector off the axis plane is positive**: if `det (w₁, w₂, t, v) ≠ 0`
for some `v`, then `bf2 t t > 0`. -/
theorem bf2_diag_pos (hG : G.PosDef) (w₁ w₂ t v : Fin 4 → ℝ) (hD : 0 < gramW G w₁ w₂)
    (hd : det4 w₁ w₂ t v ≠ 0) : 0 < bf2 G w₁ w₂ t t := by
  have hs : Gᵀ = G := by simpa using hG.isHermitian.eq
  have h := bf2_gram G w₁ w₂ t v t v hD.ne'
  have hpos : 0 < G.det * det4 w₁ w₂ t v * det4 w₁ w₂ t v / gramW G w₁ w₂ := by
    have := hG.det_pos
    have h2 : 0 < det4 w₁ w₂ t v * det4 w₁ w₂ t v := mul_self_pos.2 hd
    have : 0 < G.det * (det4 w₁ w₂ t v * det4 w₁ w₂ t v) := mul_pos this h2
    rw [← mul_assoc] at this
    exact div_pos this hD
  rw [← h, bf2_symm hs w₁ w₂ v t] at hpos
  have hv := bf2_diag_nonneg hG w₁ w₂ v hD.ne'
  have ht := bf2_diag_nonneg hG w₁ w₂ t hD.ne'
  by_contra hn
  have h0 : bf2 G w₁ w₂ t t = 0 := le_antisymm (not_lt.1 hn) ht
  rw [h0] at hpos
  nlinarith [sq_nonneg (bf2 G w₁ w₂ t v)]

end Lightlike.Regge4
