module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteMinus

/-!
# The radial profile of the matrix coefficients of the holomorphic discrete series

For `n ≥ 2` the matrix coefficient `ψ_{jl}(ξ) = ⟨e_j, D_n(a(ξ)) e_l⟩` of the `K`-weight vectors of `D_n⁺` at the
diagonal element `a(ξ) = diag(e^{ξ/2}, e^{-ξ/2})` is explicit:
`ψ_{jl}(ξ) = κ_{n,j} cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))`, where `κ_{n,j} = ‖e_j‖²` and `P_{jl}(t)` is the `j`-th Taylor
coefficient at `0` of the generating function `w ↦ (t + w)^l (1 + t w)^{-(n+l)}` (`mcoef_aR`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The generating function of the profile polynomials**, `w ↦ (t + w)^l (1 + t w)^{-(n+l)}`. -/
def genFun (n l : ℕ) (t : ℝ) (w : ℂ) : ℂ := ((t : ℂ) + w) ^ l * ((1 + (t : ℂ) * w) ^ (n + l))⁻¹

/-- **The profile polynomial `P_{jl}(t)`**: the `j`-th Taylor coefficient at `0` of `genFun n l t`. -/
def profPoly (n l j : ℕ) (t : ℝ) : ℂ := discCoeff (genFun n l t) j

lemma one_add_mul_ne_zero {t : ℝ} (ht : |t| < 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    1 + (t : ℂ) * w ≠ 0 := by
  intro h
  have h1 : (t : ℂ) * w = -1 := by linear_combination h
  have h2 : ‖(t : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hw' : ‖w‖ < 1 := by simpa using hw
    nlinarith [abs_nonneg t, norm_nonneg w]
  rw [h1] at h2
  simp at h2

lemma differentiableOn_genFun (n l : ℕ) {t : ℝ} (ht : |t| < 1) :
    DifferentiableOn ℂ (genFun n l t) (ball (0 : ℂ) 1) := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold genFun
  refine DifferentiableAt.mul (by fun_prop) ?_
  exact (DifferentiableAt.inv (by fun_prop) (pow_ne_zero _ (one_add_mul_ne_zero ht hw)))

/-- `a(ξ)` has entries `e^{ξ/2}`, `0`, `0`, `e^{-ξ/2}`. -/
lemma jac_aR (ξ : ℝ) (z : ℂ) : jac (aR ξ) z = ((Real.exp (ξ / 2) : ℝ) : ℂ)⁻¹ := by
  simp [jac, aR, diagSL]

lemma coe_tsmul_aR (ξ : ℝ) (z : ℍ) :
    ((tsmul (aR ξ) z : ℍ) : ℂ) = ((Real.exp (ξ / 2) : ℝ) : ℂ) * ((Real.exp (ξ / 2) : ℝ) : ℂ) * (z : ℂ) := by
  rw [coe_tsmul, jac_aR]
  simp only [aR, diagSL]
  have h0 : (Real.exp (ξ / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  simp
  field_simp

/-- The holomorphic function of `z` representing `D_n(a(ξ)) e_l`, with `s = e^{ξ/2}`. -/
def aRFun (n l : ℕ) (s : ℝ) (z : ℂ) : ℂ :=
  (s : ℂ) ^ n * (((s : ℂ) * s * z - Complex.I) ^ l * (((s : ℂ) * s * z + Complex.I) ^ (n + l))⁻¹)

lemma mul_add_I_ne_zero (s : ℝ) (hs : 0 < s) (z : ℍ) : (s : ℂ) * s * (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  have h1 := z.im_pos
  nlinarith [mul_pos hs hs]

lemma mdifferentiable_aRFun (n l : ℕ) {s : ℝ} (hs : 0 < s) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => aRFun n l s (z : ℂ)) := by
  intro z
  have hz : DifferentiableAt ℂ (aRFun n l s) (z : ℂ) := by
    unfold aRFun
    refine DifferentiableAt.mul (by fun_prop) (DifferentiableAt.mul (by fun_prop) ?_)
    exact DifferentiableAt.inv (by fun_prop) (pow_ne_zero _ (mul_add_I_ne_zero s hs z))
  exact (hz.mdifferentiableAt).comp z (UpperHalfPlane.mdifferentiable_coe z)

/-- `D_n(a(ξ)) e_l` is represented by the holomorphic function `aRFun`, almost everywhere. -/
lemma coeFn_aR_kClass {n : ℕ} (hn : 2 ≤ n) (l : ℕ) (ξ : ℝ) :
    (discreteAction n (aR ξ) (kClass hn l) : ℍ → ℂ) =ᵐ[μn n]
      fun z : ℍ => aRFun n l (Real.exp (ξ / 2)) (z : ℂ) := by
  have h1 := coeFn_discreteAction n (aR ξ) (kClass hn l)
  have h2 := (quasiMeasurePreserving_tsmul n (aR ξ)).ae_eq_comp (coeFn_kClass hn l)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1]
  simp only [Function.comp_apply] at hz2
  rw [hz2]
  simp only [kVec, aRFun, jac_aR, coe_tsmul_aR, zpow_neg, zpow_natCast]
  have h0 : (Real.exp (ξ / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  rw [inv_pow, inv_inv]

/-- The constant of the disc function of `D_n(a(ξ)) e_l`. -/
lemma const_aR (n : ℕ) (s : ℝ) (hs : 0 < s) :
    (4 * ((-2 * Complex.I) ^ n)⁻¹ * (s : ℂ) ^ n * ((Complex.I * ((s : ℂ) ^ 2 + 1)) ^ n)⁻¹ : ℂ) =
      (((4 / 4 ^ n : ℝ) : ℂ)) * ((((s + s⁻¹) / 2 : ℝ) : ℂ) ^ n)⁻¹ := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcosh : (((s + s⁻¹) / 2 : ℝ) : ℂ) = ((s : ℂ) ^ 2 + 1) / (2 * s) := by
    push_cast
    field_simp
  have h2I : (-2 * Complex.I) * Complex.I = 2 := by linear_combination (-2) * Complex.I_sq
  have hs2 : (s : ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((s ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : s ^ 2 + 1 ≠ 0)
    simpa using this
  have hI : Complex.I ^ n ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hs2n : ((s : ℂ) ^ 2 + 1) ^ n ≠ 0 := pow_ne_zero _ hs2
  have hsn : (s : ℂ) ^ n ≠ 0 := pow_ne_zero _ hs0
  have hneg : (-2 * Complex.I) ^ n ≠ 0 := pow_ne_zero _ (by simp [Complex.I_ne_zero])
  have hprod : (-2 * Complex.I) ^ n * Complex.I ^ n = 2 ^ n := by rw [← mul_pow, h2I]
  have h42 : (4 : ℂ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  rw [hcosh]
  push_cast
  rw [mul_pow Complex.I ((s : ℂ) ^ 2 + 1), div_pow, mul_pow 2 (s : ℂ), h42, ← hprod]
  field_simp

lemma abs_tanh_param_lt_one {s : ℝ} (hs : 0 < s) : |(s ^ 2 - 1) / (s ^ 2 + 1)| < 1 := by
  have h1 : 0 < s ^ 2 + 1 := by positivity
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ h1]; nlinarith [sq_nonneg s]
  · rw [div_lt_one h1]; linarith

lemma key_alg (n l : ℕ) (K S c A V u : ℂ) (hK : K ≠ 0) (hc : c ≠ 0) (hV : V ≠ 0) (hu : u ≠ 0) :
    4 * K⁻¹ * (S ^ n * ((c * A / u) ^ l * ((c * V / u) ^ (n + l))⁻¹) * (u ^ n)⁻¹) =
      (4 * K⁻¹ * S ^ n * (c ^ n)⁻¹) * (A ^ l * (V ^ (n + l))⁻¹) := by
  rw [div_pow, div_pow, mul_pow, mul_pow, pow_add c n l, pow_add u n l]
  have h1 : c ^ n ≠ 0 := pow_ne_zero _ hc
  have h2 : c ^ l ≠ 0 := pow_ne_zero _ hc
  have h3 : u ^ n ≠ 0 := pow_ne_zero _ hu
  have h4 : u ^ l ≠ 0 := pow_ne_zero _ hu
  have h5 : V ^ (n + l) ≠ 0 := pow_ne_zero _ hV
  first | (field_simp; ring) | field_simp

/-- **The disc function of `D_n(a(ξ)) e_l`** is `4 4^{-n} cosh(ξ/2)^{-n}` times the generating function, with
`s = e^{ξ/2}`, `cosh(ξ/2) = (s + 1/s)/2`, `tanh(ξ/2) = (s² - 1)/(s² + 1)`. -/
lemma bergmanDisc_aRFun (n l : ℕ) {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    bergmanDisc n (fun w => aRFun n l s ((UpperHalfPlane.ofComplex w : ℍ) : ℂ)) w =
      ((4 / 4 ^ n : ℝ) : ℂ) * ((((s + s⁻¹) / 2 : ℝ) : ℂ) ^ n)⁻¹ * genFun n l ((s ^ 2 - 1) / (s ^ 2 + 1)) w := by
  have hu := one_sub_ne_zero hw
  have hz : ((UpperHalfPlane.ofComplex (cayleyInv w) : ℍ) : ℂ) = cayleyInv w := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (cayleyInv_mem hw)]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2 : (s : ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((s ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : s ^ 2 + 1 ≠ 0)
    simpa using this
  set T : ℝ := (s ^ 2 - 1) / (s ^ 2 + 1) with hTdef
  have hT : (T : ℂ) = ((s : ℂ) ^ 2 - 1) / ((s : ℂ) ^ 2 + 1) := by
    rw [hTdef]; push_cast; ring
  have hV : 1 + (T : ℂ) * w ≠ 0 := one_add_mul_ne_zero (abs_tanh_param_lt_one hs) hw
  have hA : (s : ℂ) * s * cayleyInv w - Complex.I =
      Complex.I * ((s : ℂ) ^ 2 + 1) * ((T : ℂ) + w) / (1 - w) := by
    rw [hT]; unfold cayleyInv; field_simp; ring
  have hB : (s : ℂ) * s * cayleyInv w + Complex.I =
      Complex.I * ((s : ℂ) ^ 2 + 1) * (1 + (T : ℂ) * w) / (1 - w) := by
    rw [hT]; unfold cayleyInv; field_simp; ring
  have hc : Complex.I * ((s : ℂ) ^ 2 + 1) ≠ 0 := mul_ne_zero Complex.I_ne_zero hs2
  have hneg : (-2 * Complex.I) ^ n ≠ 0 := pow_ne_zero _ (by simp [Complex.I_ne_zero])
  unfold bergmanDisc
  simp only [aRFun, hz]
  rw [hA, hB]
  have key := key_alg n l ((-2 * Complex.I) ^ n) (s : ℂ) (Complex.I * ((s : ℂ) ^ 2 + 1)) ((T : ℂ) + w)
    (1 + (T : ℂ) * w) (1 - w) hneg hc hV hu
  rw [key, const_aR n s hs]
  rfl

lemma discCoeff_const_mul {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) (c : ℂ) (m : ℕ) :
    discCoeff (fun w => c * h w) m = c * discCoeff h m := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := integral_circleMap_mode hh m hs
  have h2 := integral_circleMap_mode (hh.const_mul c) m hs
  have h3 : ∫ θ in (0 : ℝ)..2 * π, c * h (circleMap 0 (1 / 2) θ) *
      Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
      c * ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 (1 / 2) θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [mul_assoc]
  rw [h3, h1] at h2
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by norm_num)))
  have : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * discCoeff (fun w => c * h w) m =
      (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ m) * (c * discCoeff h m) := by
    linear_combination (-1 : ℂ) * h2
  exact mul_left_cancel₀ hne this

/-- **The matrix coefficient of `D_n⁺` at `a(ξ)` in closed form**:
`⟨e_j, D_n(a(ξ)) e_l⟩ = ‖e_j‖² cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))`. -/
theorem mcoef_aR {n : ℕ} (hn : 2 ≤ n) (j l : ℕ) (ξ : ℝ) :
    mcoef n (kClass hn j) (kClass hn l) (aR ξ) =
      ((‖kClass hn j‖ ^ 2 : ℝ) : ℂ) * (((Real.cosh (ξ / 2) : ℝ) : ℂ) ^ n)⁻¹ *
        profPoly n l j (Real.tanh (ξ / 2)) := by
  have hs : 0 < Real.exp (ξ / 2) := Real.exp_pos _
  have hcosh : Real.cosh (ξ / 2) = (Real.exp (ξ / 2) + (Real.exp (ξ / 2))⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg]
  have htanh : Real.tanh (ξ / 2) =
      ((Real.exp (ξ / 2)) ^ 2 - 1) / ((Real.exp (ξ / 2)) ^ 2 + 1) := tanh_half_eq ξ
  have h := inner_kClass_holo hn j (mdifferentiable_aRFun n l hs) (coeFn_aR_kClass hn l ξ)
  have hc : discCoeff (bergmanDisc n (fun w => aRFun n l (Real.exp (ξ / 2))
      ((UpperHalfPlane.ofComplex w : ℍ) : ℂ))) j =
      (((4 / 4 ^ n : ℝ) : ℂ) * (((Real.cosh (ξ / 2) : ℝ) : ℂ) ^ n)⁻¹) * profPoly n l j (Real.tanh (ξ / 2)) := by
    rw [discCoeff_congr (h' := fun w => (((4 / 4 ^ n : ℝ) : ℂ) * ((((Real.exp (ξ / 2) +
      (Real.exp (ξ / 2))⁻¹) / 2 : ℝ) : ℂ) ^ n)⁻¹) *
      genFun n l ((Real.exp (ξ / 2) ^ 2 - 1) / (Real.exp (ξ / 2) ^ 2 + 1)) w)
      (fun w hw => bergmanDisc_aRFun n l hs hw) j, hcosh, htanh]
    exact discCoeff_const_mul (differentiableOn_genFun n l (abs_tanh_param_lt_one hs)) _ j
  have hn2 := norm_sq_kClass hn j
  unfold mcoef
  show ⟪kClass hn j, discreteAction n (aR ξ) (kClass hn l)⟫_ℂ = _
  rw [h, hc, hn2]
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
