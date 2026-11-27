import Mathlib

/-!
# The Gaussian integral on `ℝⁿ = Fin n → ℝ`

`∫ exp(−b Σᵢ yᵢ²) dy = (π/b)^{n/2}` for `b > 0` (`integral_exp_neg_mul_sum_sq`), with Lebesgue measure on
`Fin n → ℝ`; the integral of a product of functions of the coordinates is the product of the one-dimensional integrals
(`MeasureTheory.integral_fintype_prod_eq_prod`) and each factor is Mathlib's `integral_gaussian`. Translated to any
centre (`integral_exp_neg_mul_sum_sq_sub`). These normalize the Gaussian factor `(4πt)^{-n/2} e^{-|y−p|²/4t}` of the
heat-kernel parametrix: its integral is `1`.
-/

open MeasureTheory Real Matrix

noncomputable section

namespace Lightlike

/-- **The Gaussian integral on `ℝⁿ`**: `∫ exp(−b Σ yᵢ²) dy = (π/b)^{n/2}`. -/
theorem integral_exp_neg_mul_sum_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, y i ^ 2) = (π / b) ^ ((n : ℝ) / 2) := by
  have hprod : (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, y i ^ 2)) =
      fun y => ∏ i, Real.exp (-b * y i ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [hprod, volume_pi, integral_fintype_prod_eq_prod (f := fun _ x => Real.exp (-b * x ^ 2))]
  simp only [integral_gaussian, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- The same about any centre `p`. -/
theorem integral_exp_neg_mul_sum_sq_sub (n : ℕ) {b : ℝ} (hb : 0 < b) (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, (y i - p i) ^ 2) = (π / b) ^ ((n : ℝ) / 2) := by
  have := integral_sub_right_eq_self (μ := volume) (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, y i ^ 2)) p
  simp only [Pi.sub_apply] at this
  rw [this, integral_exp_neg_mul_sum_sq n hb]

/-- The Gaussian is integrable. -/
theorem integrable_exp_neg_mul_sum_sq_sub (n : ℕ) {b : ℝ} (hb : 0 < b) (p : Fin n → ℝ) :
    Integrable (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, (y i - p i) ^ 2)) := by
  have hprod : (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, (y i - p i) ^ 2)) =
      fun y => ∏ i, Real.exp (-b * (y i - p i) ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [hprod, volume_pi]
  exact Integrable.fintype_prod (f := fun i x => Real.exp (-b * (x - p i) ^ 2)) fun i =>
    (integrable_exp_neg_mul_sq hb).comp_sub_right (p i)

/-- The product form: `∫ exp(−b Σ λᵢ yᵢ²) dy = Π √(π/(bλᵢ))` for `λᵢ > 0`. -/
theorem integral_exp_neg_mul_sum_mul_sq (n : ℕ) {b : ℝ} (hb : 0 < b) {lam : Fin n → ℝ} (hl : ∀ i, 0 < lam i) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, lam i * y i ^ 2) = ∏ i, √(π / (b * lam i)) := by
  have hprod : (fun y : Fin n → ℝ => Real.exp (-b * ∑ i, lam i * y i ^ 2)) =
      fun y => ∏ i, Real.exp (-(b * lam i) * y i ^ 2) := by
    funext y
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, volume_pi, integral_fintype_prod_eq_prod (f := fun i x => Real.exp (-(b * lam i) * x ^ 2))]
  simp only [integral_gaussian]

/-- A linear map with determinant `±1` preserves the integral. -/
theorem integral_comp_mulVec_of_abs_det_eq_one {n : ℕ} {L : Matrix (Fin n) (Fin n) ℝ} (hL : |L.det| = 1)
    (g : (Fin n → ℝ) → ℝ) : ∫ z, g (L *ᵥ z) = ∫ w, g w := by
  have hdet : LinearMap.det (Matrix.toLin' L) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h, abs_zero] at hL; exact zero_ne_one hL
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin n → ℝ))) hdet
  rw [LinearMap.det_toLin', abs_inv, hL, inv_one, ENNReal.ofReal_one, one_smul] at hmap
  set e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero (Matrix.toLin' L) hdet).toContinuousLinearEquiv with he
  have hmp : MeasurePreserving (fun z : Fin n → ℝ => L *ᵥ z) volume volume :=
    ⟨(Matrix.toLin' L).continuous_of_finiteDimensional.measurable, hmap⟩
  have hemb : MeasurableEmbedding (fun z : Fin n → ℝ => L *ᵥ z) := by
    have : (fun z : Fin n → ℝ => L *ᵥ z) = e := by
      funext z; simp [he, LinearMap.equivOfDetNeZero]
    rw [this]
    exact e.toHomeomorph.measurableEmbedding
  exact hmp.integral_comp hemb g

/-- **The Gaussian integral of a positive definite form**:
`∫ exp(−b (y − p)·G(y − p)) dy = (π/b)^{n/2} / √(det G)`. -/
theorem integral_exp_neg_mul_quadForm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {b : ℝ} (hb : 0 < b)
    (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, Real.exp (-b * ((y - p) ⬝ᵥ (G *ᵥ (y - p)))) = (π / b) ^ ((n : ℝ) / 2) / √G.det := by
  have hH := hG.isHermitian
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set lam := hH.eigenvalues with hlam
  have hpos : ∀ i, 0 < lam i := hG.eigenvalues_pos
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hspec : G = U * diagonal lam * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Function.comp_def] using this
  -- `z·Gz = Σ λᵢ ((Uᵀ z)ᵢ)²`
  have hquad : ∀ z : Fin n → ℝ, z ⬝ᵥ (G *ᵥ z) = ∑ i, lam i * (star U *ᵥ z) i ^ 2 := by
    intro z
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    have hvt : z ᵥ* U = star U *ᵥ z := by
      rw [show star U = Uᵀ from by ext i j; simp [Matrix.star_apply, Matrix.transpose_apply], mulVec_transpose]
    rw [hvt]
    simp only [dotProduct, mulVec_diagonal, sq]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- `|det Uᵀ| = 1`
  have hdet : |(star U).det| = 1 := by
    have h1 : (star U).det * U.det = 1 := by rw [← det_mul, hUU, det_one]
    have h2 : (star U).det = U.det := by
      rw [show star U = Uᵀ from by ext i j; simp [Matrix.star_apply, Matrix.transpose_apply], det_transpose]
    rw [h2] at h1
    have h3 : |U.det| ^ 2 = 1 := by rw [sq_abs, sq]; exact h1
    rw [h2]
    exact (pow_left_inj₀ (abs_nonneg _) zero_le_one two_ne_zero).1 (by rw [h3, one_pow])
  have hdetG : G.det = ∏ i, lam i := by
    have := hH.det_eq_prod_eigenvalues
    simpa using this
  calc ∫ y : Fin n → ℝ, Real.exp (-b * ((y - p) ⬝ᵥ (G *ᵥ (y - p))))
      = ∫ y : Fin n → ℝ, Real.exp (-b * ∑ i, lam i * (star U *ᵥ (y - p)) i ^ 2) := by
        simp only [hquad]
    _ = ∫ z : Fin n → ℝ, Real.exp (-b * ∑ i, lam i * (star U *ᵥ z) i ^ 2) :=
        integral_sub_right_eq_self (μ := volume)
          (fun z : Fin n → ℝ => Real.exp (-b * ∑ i, lam i * (star U *ᵥ z) i ^ 2)) p
    _ = ∫ w : Fin n → ℝ, Real.exp (-b * ∑ i, lam i * w i ^ 2) :=
        integral_comp_mulVec_of_abs_det_eq_one hdet (fun w => Real.exp (-b * ∑ i, lam i * w i ^ 2))
    _ = ∏ i, √(π / (b * lam i)) := integral_exp_neg_mul_sum_mul_sq n hb hpos
    _ = (π / b) ^ ((n : ℝ) / 2) / √G.det := by
        have hsplit : ∀ i, √(π / (b * lam i)) = √(π / b) / √(lam i) := fun i => by
          rw [show π / (b * lam i) = (π / b) / lam i by field_simp, Real.sqrt_div' _ (hpos i).le]
        simp only [hsplit, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [hdetG, ← Real.sqrt_prod _ fun i _ => (hpos i).le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        ring_nf

end Lightlike
