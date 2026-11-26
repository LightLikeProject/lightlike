module

public import Mathlib
public import Lightlike.Lorentz.SL2R
public import Lightlike.Lorentz.SL2RPlancherel.HyperbolicPolar

/-!
# The polar (KAK) integration formula for the Haar measure of `SL(2,ℝ)`

With `a(ξ) = diag(e^{ξ/2}, e^{-ξ/2})`, for measurable `F : SL(2,ℝ) → [0,∞]`,
`∫ F d haarR = 2 ∫_{-π/2}^{π/2} ∫_0^∞ sinh ξ ∫_0^{2π} F(k_α a(ξ) k_θ) dθ dξ dα`
(`lintegral_haarR_polar`).  The proof takes the Iwasawa form of `haarR`
(`lintegral_haarR`), the hyperbolic polar coordinates of `ℍ` (`lintegral_upperHalfPlane_polar`),
the identity `k_α a(ξ) · i = c(tanh(ξ/2) e^{2iα})` (`smul_I_polar`), and the rotation invariance
`lintegral_rot_add`.  Layer 2a of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real UpperHalfPlane Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

lemma cayleyInv_rot_diag (c s e : ℝ) (hcs : c^2 + s^2 = 1) (he : 0 < e)
    (hD : (-(s:ℂ) * e * Complex.I + c / e) ≠ 0) (h1 : 1 - (((e^2-1)/(e^2+1) : ℝ) * (((c^2 - s^2 : ℝ) : ℂ) + ((2*c*s : ℝ) : ℂ) * Complex.I)) ≠ 0) :
    cayleyInv (((e^2-1)/(e^2+1) : ℝ) * (((c^2 - s^2 : ℝ) : ℂ) + ((2*c*s : ℝ) : ℂ) * Complex.I)) = (c*e*Complex.I + s/e)/(-(s:ℂ)*e*Complex.I + c/e) := by
  unfold cayleyInv
  have hcs' : (c:ℂ)^2 + s^2 = 1 := by exact_mod_cast hcs
  have he0 : (e:ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have he1 : (e:ℂ)^2 + 1 ≠ 0 := by exact_mod_cast (by positivity : e^2+1 ≠ 0)
  rw [div_eq_div_iff h1 hD]
  push_cast at h1 ⊢
  field_simp
  have hI : (Complex.I:ℂ)^2 = -1 := Complex.I_sq
  linear_combination ((c:ℂ)^2*(e:ℂ)^4*(s:ℂ) + (c:ℂ)^2*(e:ℂ)^2*(s:ℂ) - 2*(c:ℂ)^2*(s:ℂ) - 2*(c:ℂ)*(e:ℂ)^4*Complex.I*(s:ℂ)^2 + 2*(c:ℂ)*(e:ℂ)^2*Complex.I*(s:ℂ)^2 + (e:ℂ)^4*(s:ℂ)^3 - (e:ℂ)^4*(s:ℂ) - (e:ℂ)^2*(s:ℂ)^3 - (e:ℂ)^2*(s:ℂ)) * hI + ((c:ℂ)*(e:ℂ)^4*Complex.I - (c:ℂ)*Complex.I - (e:ℂ)^4*(s:ℂ) + (s:ℂ)) * hcs'

/-- The diagonal element `a(ξ) = diag(e^{ξ/2}, e^{-ξ/2})`. -/
def aR (ξ : ℝ) : SL2R := diagSL (Real.exp (ξ / 2)) (Real.exp_pos _).ne'

lemma tanh_half_eq (ξ : ℝ) :
    Real.tanh (ξ / 2) = ((Real.exp (ξ / 2)) ^ 2 - 1) / ((Real.exp (ξ / 2)) ^ 2 + 1) := by
  have h := Real.exp_pos (ξ / 2)
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  field_simp

/-- **The point `k_α a(ξ) · i` in the disc picture**: it is the inverse Cayley transform of
`tanh(ξ/2) e^{2iα}`. -/
lemma smul_I_polar (α ξ : ℝ) :
    (((rot α * aR ξ) • UpperHalfPlane.I : ℍ) : ℂ) =
      cayleyInv (((Real.tanh (ξ / 2) : ℝ) : ℂ) *
        ((Real.cos (2 * α) : ℝ) + (Real.sin (2 * α) : ℝ) * Complex.I)) := by
  set e := Real.exp (ξ / 2) with he
  have hepos : 0 < e := Real.exp_pos _
  have hcs : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq α
  have hD := denom_ne_zero' (rot α * aR ξ) UpperHalfPlane.I
  have hu : ‖((Real.cos (2 * α) : ℝ) + (Real.sin (2 * α) : ℝ) * Complex.I : ℂ)‖ = 1 := by
    have : ((Real.cos (2 * α) : ℝ) + (Real.sin (2 * α) : ℝ) * Complex.I : ℂ) =
        Complex.exp (((2 * α : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I]; push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have ht : |Real.tanh (ξ / 2)| < 1 := by
    rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hball : (((Real.tanh (ξ / 2) : ℝ) : ℂ) *
      ((Real.cos (2 * α) : ℝ) + (Real.sin (2 * α) : ℝ) * Complex.I)) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact ht
  have h1 := one_sub_ne_zero hball
  rw [coe_smul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_rot, aR,
    diagSL, coe_mk, UpperHalfPlane.coe_I, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at hD ⊢
  rw [tanh_half_eq, Real.cos_two_mul, Real.sin_two_mul] at h1 ⊢
  have hc2 : 2 * Real.cos α ^ 2 - 1 = Real.cos α ^ 2 - Real.sin α ^ 2 := by nlinarith
  have hs2 : 2 * Real.sin α * Real.cos α = 2 * Real.cos α * Real.sin α := by ring
  rw [hc2, hs2] at h1 ⊢
  have key := cayleyInv_rot_diag (Real.cos α) (Real.sin α) e hcs hepos ?_ h1
  · rw [key]
    push_cast
    simp only [mul_zero, add_zero, zero_add]
    simp only [he]
    push_cast
    ring_nf
  · intro h
    apply hD
    rw [← h]
    simp only [he]
    push_cast
    ring

/-- Replacing the Iwasawa `A N`-part of `g` by `g` itself does not change the circle integral. -/
lemma lintegral_toSL2R_smul_I (F : SL2R → ENNReal) (g : SL2R) :
    ∫⁻ θ in Ioc 0 (2 * π), F ((g • UpperHalfPlane.I).toSL2R * rot θ) =
      ∫⁻ θ in Ioc 0 (2 * π), F (g * rot θ) := by
  obtain ⟨β, hβ⟩ := exists_iwasawa g
  have h : (g • UpperHalfPlane.I).toSL2R = g * rot (-β) := by
    conv_rhs => rw [hβ]
    rw [mul_assoc, ← rot_add]; simp
  simp_rw [h, mul_assoc, ← rot_add]
  exact lintegral_rot_add (fun h => F (g * h)) (-β)

/-- **Polar (KAK) integration formula for the Haar measure of `SL(2,ℝ)`.** -/
theorem lintegral_haarR_polar {F : SL2R → ENNReal} (hF : Measurable F) :
    ∫⁻ g, F g ∂haarR =
      2 * ∫⁻ α in Ioo (-(π / 2)) (π / 2), ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
        ∫⁻ θ in Ioc 0 (2 * π), F (rot α * aR ξ * rot θ) := by
  set Gz : ℍ → ENNReal := fun z => ∫⁻ θ in Ioc 0 (2 * π), F (z.toSL2R * rot θ) with hGz
  have hGm : Measurable Gz := by
    have : Measurable fun p : ℍ × ℝ => F (iwasawa p) := hF.comp measurable_iwasawa
    exact this.lintegral_prod_right'
  rw [lintegral_haarR hF, lintegral_upperHalfPlane_polar hGm]
  have himg : (fun φ : ℝ => 2 * φ) '' Ioo (-(π / 2)) (π / 2) = Ioo (-π) π := by
    ext x
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; exact ⟨x / 2, ⟨by linarith, by linarith⟩, by ring⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun φ : ℝ => 2 * φ)
    (f' := fun _ => 2) (s := Ioo (-(π / 2)) (π / 2)) measurableSet_Ioo
    (fun x _ => ((hasDerivAt_id x).const_mul 2).hasDerivWithinAt.congr_deriv (by simp))
    (fun x _ y _ h => by simpa using h)
    (fun φ => ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
      Gz (UpperHalfPlane.ofComplex (cayleyInv ((Real.tanh (ξ / 2) : ℝ) *
        (Real.cos φ + Real.sin φ * Complex.I)))))
  rw [himg] at key
  rw [key, ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun α _ => ?_)
  simp only [abs_two, ENNReal.ofReal_ofNat]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ξ _ => ?_)
  congr 1
  have h1 : UpperHalfPlane.ofComplex (cayleyInv ((Real.tanh (ξ / 2) : ℝ) *
      (Real.cos (2 * α) + Real.sin (2 * α) * Complex.I))) = (rot α * aR ξ) • UpperHalfPlane.I := by
    rw [← smul_I_polar]; exact UpperHalfPlane.ofComplex_apply _
  simp only [hGz]
  rw [h1, lintegral_toSL2R_smul_I]

end Lightlike.Lorentz.SL2R
