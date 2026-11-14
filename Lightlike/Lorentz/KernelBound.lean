module

public import Lightlike.Lorentz.Spherical
public import Lightlike.Lorentz.SU2Decomposition
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The kernel bound for matrix coefficients of the principal series

A vector `f ∈ L²(ℂ)` *decays with constant `C`* if `|f(z)| ≤ C (1 + |z|²)⁻¹` almost everywhere.
Every SU(2)-finite vector of the principal series decays (`exists_decaysWith_suV`), and the matrix
coefficients of decaying vectors are bounded by the kernel

  `I(g) = ∫_ℂ d²z / ((1 + |z|²) ‖gᵀ(z, 1)‖²) = π r / sinh r`

of `Spherical.lean`, uniformly in the labels `(n, ρ)` of the representation:

  `|⟨f₁, π_{n,ρ}(g) f₂⟩| ≤ C₁ C₂ I(g)`   (`norm_inner_principalSeries_le`).

This is the estimate behind the finiteness of the Lorentzian EPRL vertex amplitude (Engle and
Pereira 2009, where the corresponding bound (42) is `|K| ≤ C e^{-(1-ε) r}`). The kernel is in
`L^{5/2}` of the Haar measure (`lintegral_kernelE_rpow_lt_top`) but not in `L²`
(`lintegral_kernelE_sq_eq_top`): in the radial formula `dg = 4π³ sinh² r dr`, so `I^p` is
integrable exactly when `p > 2`. The exponent `5/2` is what the star Hölder inequality of
`StarBound.lean` needs for the ten links of the 4-simplex graph, each vertex meeting four.

## Main results

* `one_add_sq_le_normT`: `1 + |z|² ≤ 2 cosh r(g) · ‖gᵀ(z, 1)‖²`.
* `integrable_kernel`: the integrand of `I(g)` is integrable, for every `g`.
* `norm_inner_principalSeries_le`: the matrix-coefficient bound above.
* `exists_decaysWith_suV`: the SU(2)-finite vectors decay.
* `kernelI_inv`, `kernelI_pos`, `kernelI_le`: `I(g⁻¹) = I(g)` and `0 < I(g) ≤ π`.
* `lintegral_kernelE_rpow_lt_top`, `lintegral_kernelE_sq_eq_top`: `I ∈ L^{5/2}`, `I ∉ L²`.

## References

* J. Engle and R. Pereira, *Regularization and finiteness of the Lorentzian loop quantum gravity
  vertices*, Phys. Rev. D 79 (2009) 084034, arXiv:0805.4696, sec. 4 and appendix A.
* J. C. Baez and J. W. Barrett, *Integrability for relativistic spin networks*, Class. Quantum
  Grav. 18 (2001) 4683, arXiv:gr-qc/0101107.
-/

@[expose] public section

open MeasureTheory Complex Set Filter
open scoped ComplexConjugate InnerProductSpace ENNReal

namespace Lightlike.Lorentz

/-! ## Decaying vectors -/

/-- `f ∈ L²(ℂ)` **decays with constant `C`**: `|f(z)| ≤ C (1 + |z|²)⁻¹` almost everywhere. -/
def DecaysWith (C : ℝ) (f : L2C) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹

/-- **The SU(2)-finite vectors decay**: every vector in the image of `suV n ρ ℓ` decays. -/
theorem exists_decaysWith_suV (n : ℤ) (ρ : ℝ) (ℓ : ℕ) (x : Espace (dsp n ℓ)) :
    ∃ C, DecaysWith C (suV n ρ ℓ x) := by
  set A := tlin (ℓ + p0 n) (ℓ + q0 n) ρ
  refine ⟨‖((nrmA A)⁻¹ : ℂ)‖ * ∑ t, ‖((Lightlike.SU2.emb (ℓ + p0 n + (ℓ + q0 n))).mulVec x.ofLp) t‖,
    ?_⟩
  have h := coeFn_tlin (ℓ + p0 n) (ℓ + q0 n) ρ x.ofLp
  have hs := Lp.coeFn_smul ((nrmA A)⁻¹ : ℂ) (A x.ofLp)
  have e : suV n ρ ℓ x = ((nrmA A)⁻¹ : ℂ) • A x.ofLp := rfl
  unfold DecaysWith
  filter_upwards [h, hs] with z hz hz'
  rw [e, hz', Pi.smul_apply, hz, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_tfun_le _ _ ρ _ z) (norm_nonneg _)

/-! ## The lower bound for `‖gᵀ(z, 1)‖²` -/

/-- Cauchy–Schwarz for two terms: `|a x + b y|² ≤ (|a|² + |b|²)(|x|² + |y|²)`. -/
lemma norm_mul_add_mul_sq_le (a b x y : ℂ) :
    ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := norm_add_le (a * x) (b * y)
  rw [norm_mul, norm_mul] at h
  have h1 : ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ * ‖y‖ - ‖b‖ * ‖x‖)]

/-- Inverting `gᵀ`, first row: `z = g₁₁ num - g₁₀ den`. -/
lemma eq_num_den (g : SL2C) (z : ℂ) : z = g 1 1 * num g z + (-g 1 0) * den g z := by
  have := SL2C.det_eq g
  simp only [num, den]
  linear_combination (-z) * this

/-- Inverting `gᵀ`, second row: `1 = -g₀₁ num + g₀₀ den`. -/
lemma one_eq_num_den (g : SL2C) (z : ℂ) : (1 : ℂ) = (-g 0 1) * num g z + g 0 0 * den g z := by
  have := SL2C.det_eq g
  simp only [num, den]
  linear_combination (-1 : ℂ) * this

/-- **`1 + |z|² ≤ 2 cosh r(g) · ‖gᵀ(z, 1)‖²`**, from `‖(gᵀ)⁻¹‖²_F = ‖g‖²_F = 2 cosh r(g)`. -/
lemma one_add_sq_le_normT (g : SL2C) (z : ℂ) : 1 + ‖z‖ ^ 2 ≤ 2 * coshDist g * normT g z := by
  have h1 := norm_mul_add_mul_sq_le (g 1 1) (-g 1 0) (num g z) (den g z)
  have h2 := norm_mul_add_mul_sq_le (-g 0 1) (g 0 0) (num g z) (den g z)
  rw [← eq_num_den] at h1
  rw [← one_eq_num_den, norm_one] at h2
  simp only [norm_neg] at h1 h2
  simp only [coshDist, normT]
  nlinarith [h1, h2]

/-- `cosh r(g) ≥ 1`: `‖g‖²_F ≥ 2 |det g| = 2`. -/
lemma one_le_coshDist (g : SL2C) : 1 ≤ coshDist g := by
  have h : (1 : ℝ) ≤ ‖g 0 0‖ * ‖g 1 1‖ + ‖g 0 1‖ * ‖g 1 0‖ := by
    have := norm_sub_le (g 0 0 * g 1 1) (g 0 1 * g 1 0)
    rwa [SL2C.det_eq g, norm_one, norm_mul, norm_mul] at this
  unfold coshDist
  nlinarith [sq_nonneg (‖g 0 0‖ - ‖g 1 1‖), sq_nonneg (‖g 0 1‖ - ‖g 1 0‖)]

/-- `‖gᵀ(z, 1)‖² > 0`. -/
lemma normT_pos (g : SL2C) (z : ℂ) : 0 < normT g z := by
  have h := one_add_sq_le_normT g z
  have h0 : 0 ≤ normT g z := by unfold normT; positivity
  rcases h0.lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0, mul_zero] at h; nlinarith [sq_nonneg ‖z‖]

/-! ## The kernel -/

/-- The integrand of `I(g)` is at most `2 cosh r(g) (1 + |z|²)⁻²`. -/
lemma kernel_integrand_le (g : SL2C) (z : ℂ) :
    ((1 + ‖z‖ ^ 2) * normT g z)⁻¹ ≤ 2 * coshDist g * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
  have ha : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hN := normT_pos g z
  have h := one_add_sq_le_normT g z
  rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h ha.le]

lemma continuous_kernel_integrand (g : SL2C) :
    Continuous fun z : ℂ => ((1 + ‖z‖ ^ 2) * normT g z)⁻¹ := by
  refine Continuous.inv₀ ?_ fun z => (mul_pos (by positivity) (normT_pos g z)).ne'
  have := continuous_num g
  have := continuous_den g
  unfold normT; fun_prop

/-- **The integrand of `I(g)` is integrable**, for every `g`. -/
theorem integrable_kernel (g : SL2C) :
    Integrable fun z : ℂ => ((1 + ‖z‖ ^ 2) * normT g z)⁻¹ := by
  have hint : Integrable fun z : ℂ => 2 * coshDist g * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    have := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)
    refine (this.const_mul (2 * coshDist g)).congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [show (-4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  refine hint.mono' (continuous_kernel_integrand g).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (inv_nonneg.2 (mul_pos (by positivity) (normT_pos g z)).le)]
  exact kernel_integrand_le g z

/-- **The matrix-coefficient bound**: for vectors decaying with constants `C₁`, `C₂`,
`|⟨f₁, π_{n,ρ}(g) f₂⟩| ≤ C₁ C₂ I(g)`, for every `(n, ρ)` and `g`. -/
theorem norm_inner_principalSeries_le {C₁ C₂ : ℝ} {f₁ f₂ : L2C} (h₁ : DecaysWith C₁ f₁)
    (h₂ : DecaysWith C₂ f₂) (n : ℤ) (ρ : ℝ) (g : SL2C) :
    ‖⟪f₁, principalSeries n ρ g f₂⟫_ℂ‖ ≤ C₁ * C₂ * kernelI g := by
  rw [MeasureTheory.L2.inner_def, kernelI, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrable_kernel g).const_mul _) ?_
  filter_upwards [h₁, coeFn_principalSeries n ρ g f₂, ae_den_ne_zero g,
    (quasiMeasurePreserving_mob g).ae h₂] with z hz1 hz2 hden hz3
  rw [hz2]
  have hd : 0 < ‖den g z‖ := norm_pos_iff.2 hden
  calc ‖⟪f₁ z, mult n ρ (den g z) * f₂ (mob g z)⟫_ℂ‖
      ≤ ‖f₁ z‖ * ‖mult n ρ (den g z) * f₂ (mob g z)‖ := norm_inner_le_norm _ _
    _ ≤ (C₁ * (1 + ‖z‖ ^ 2)⁻¹) * ((‖den g z‖ ^ 2)⁻¹ * (C₂ * (1 + ‖mob g z‖ ^ 2)⁻¹)) := by
        rw [norm_mul, norm_mult n ρ hden]
        exact mul_le_mul hz1 (mul_le_mul_of_nonneg_left hz3 (by positivity)) (by positivity)
          ((norm_nonneg _).trans hz1)
    _ = C₁ * C₂ * ((1 + ‖z‖ ^ 2) * normT g z)⁻¹ := by
        rw [mob_def, norm_div, normT]
        field_simp
        ring

/-- `cosh r(g⁻¹) = cosh r(g)`. -/
lemma coshDist_inv (g : SL2C) : coshDist g⁻¹ = coshDist g := by
  simp only [coshDist, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, norm_neg]
  ring

/-- **`I(g⁻¹) = I(g)`.** -/
theorem kernelI_inv (g : SL2C) : kernelI g⁻¹ = kernelI g := by
  rw [kernelI_eq, kernelI_eq, coshDist_inv]

/-- `φ₀(r) = r / sinh r`, with the value `1` at `r = 0`. -/
lemma sphericalFn_zero_eq : sphericalFn 0 = fun r => if r = 0 then 1 else r / Real.sinh r := by
  funext r; simp [sphericalFn]

/-- `r / sinh r ≤ 1`, the spherical function `φ₀`. -/
lemma sphericalFn_zero_le_one (r : ℝ) : sphericalFn 0 r ≤ 1 := by
  rw [sphericalFn_zero_eq]
  dsimp only
  split_ifs with h
  · exact le_rfl
  · rcases lt_or_gt_of_ne h with h | h
    · have hs : Real.sinh r < 0 := Real.sinh_neg_iff.2 h
      rw [div_le_one_of_neg hs]
      have : Real.sinh (-r) ≥ -r := Real.self_le_sinh_iff.2 (by linarith)
      rw [Real.sinh_neg] at this; linarith
    · rw [div_le_one (Real.sinh_pos_iff.2 h)]
      exact Real.self_le_sinh_iff.2 h.le

/-- `r / sinh r > 0`. -/
lemma sphericalFn_zero_pos (r : ℝ) : 0 < sphericalFn 0 r := by
  rw [sphericalFn_zero_eq]
  dsimp only
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with h | h
    · exact div_pos_of_neg_of_neg h (Real.sinh_neg_iff.2 h)
    · exact div_pos h (Real.sinh_pos_iff.2 h)

/-- `I(g) > 0`. -/
lemma kernelI_pos (g : SL2C) : 0 < kernelI g := by
  rw [kernelI_eq]; exact mul_pos Real.pi_pos (sphericalFn_zero_pos _)

/-- `I(g) ≤ π`. -/
lemma kernelI_le (g : SL2C) : kernelI g ≤ Real.pi := by
  rw [kernelI_eq]
  nlinarith [sphericalFn_zero_le_one (Real.arcosh (coshDist g)), Real.pi_pos]

/-- The kernel as an extended nonnegative real, the form used in lower integrals. -/
noncomputable def kernelE (g : SL2C) : ℝ≥0∞ := ENNReal.ofReal (kernelI g)

lemma kernelE_inv (g : SL2C) : kernelE g⁻¹ = kernelE g := by rw [kernelE, kernelE, kernelI_inv]

lemma kernelE_ne_top (g : SL2C) : kernelE g ≠ ∞ := ENNReal.ofReal_ne_top

lemma kernelE_pos (g : SL2C) : 0 < kernelE g := ENNReal.ofReal_pos.2 (kernelI_pos g)

/-- The radial profile `t ↦ π φ₀(arcosh t)` of the kernel. -/
noncomputable def kernelProfile (t : ℝ) : ℝ := Real.pi * sphericalFn 0 (Real.arcosh t)

lemma measurable_sphericalFn_zero : Measurable (sphericalFn 0) := by
  rw [sphericalFn_zero_eq]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

lemma measurable_kernelProfile : Measurable kernelProfile := by
  have : Measurable Real.arcosh := by unfold Real.arcosh; fun_prop
  exact measurable_const.mul (measurable_sphericalFn_zero.comp this)

lemma kernelI_eq_profile (g : SL2C) : kernelI g = kernelProfile (coshDist g) := kernelI_eq g

lemma measurable_kernelE : Measurable kernelE := by
  have e : kernelE = fun g => ENNReal.ofReal (kernelProfile (coshDist g)) := by
    funext g; rw [kernelE, kernelI_eq_profile]
  rw [e]
  exact ENNReal.measurable_ofReal.comp
    (measurable_kernelProfile.comp continuous_coshDist.measurable)

lemma kernelProfile_cosh {r : ℝ} (hr : 0 < r) :
    kernelProfile (Real.cosh r) = Real.pi * (r / Real.sinh r) := by
  rw [kernelProfile, Real.arcosh_cosh hr.le, sphericalFn_zero_eq]
  simp [hr.ne']

/-- `r e^{r/2} ≤ 2 sinh r` for `r ≥ 0`. -/
lemma mul_exp_half_le_two_sinh {r : ℝ} (hr : 0 ≤ r) : r * Real.exp (r / 2) ≤ 2 * Real.sinh r := by
  have h2 : Real.sinh r = 2 * Real.sinh (r / 2) * Real.cosh (r / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have hs : r / 2 ≤ Real.sinh (r / 2) := Real.self_le_sinh_iff.2 (by linarith)
  have hc : Real.exp (r / 2) ≤ 2 * Real.cosh (r / 2) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(r / 2))]
  have hc0 : 0 ≤ Real.exp (r / 2) := (Real.exp_pos _).le
  rw [h2]
  nlinarith [mul_le_mul hs hc hc0 (by linarith)]

/-- **The radial integrand of `I^{5/2}`**: `sinh² r · (π r / sinh r)^{5/2} ≤ π² √(2π) r² e^{-r/4}`
for `r > 0`. -/
lemma sinh_sq_mul_rpow_le {r : ℝ} (hr : 0 < r) :
    Real.sinh r ^ 2 * (Real.pi * (r / Real.sinh r)) ^ (5 / 2 : ℝ) ≤
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) * (r ^ 2 * Real.exp (-(1 / 4) * r)) := by
  have hs : 0 < Real.sinh r := Real.sinh_pos_iff.2 hr
  set x := Real.pi * (r / Real.sinh r) with hx
  have hx0 : 0 < x := by positivity
  have hpow : x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hx0, Real.sqrt_eq_rpow,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsq : Real.sinh r ^ 2 * x ^ 2 = Real.pi ^ 2 * r ^ 2 := by
    rw [hx]; field_simp
  have hle : x ≤ 2 * Real.pi * Real.exp (-(1 / 2) * r) := by
    have h := mul_exp_half_le_two_sinh hr.le
    have he : Real.exp (-(1 / 2) * r) = (Real.exp (r / 2))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hx, he, div_eq_mul_inv]
    have hpos : 0 < Real.exp (r / 2) := Real.exp_pos _
    rw [show Real.pi * (r * (Real.sinh r)⁻¹) = Real.pi * r / Real.sinh r by ring,
      show 2 * Real.pi * (Real.exp (r / 2))⁻¹ = 2 * Real.pi / Real.exp (r / 2) by ring,
      div_le_div_iff₀ hs hpos]
    nlinarith [Real.pi_pos]
  have hsqrt : Real.sqrt x ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(1 / 4) * r) := by
    have he : Real.exp (-(1 / 2) * r) = Real.exp (-(1 / 4) * r) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc Real.sqrt x ≤ Real.sqrt (2 * Real.pi * Real.exp (-(1 / 2) * r)) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (2 * Real.pi) * Real.exp (-(1 / 4) * r) := by
        rw [Real.sqrt_mul (by positivity), he, Real.sqrt_sq (Real.exp_pos _).le]
  rw [hpow, ← mul_assoc, hsq]
  have : 0 ≤ Real.pi ^ 2 * r ^ 2 := by positivity
  calc Real.pi ^ 2 * r ^ 2 * Real.sqrt x
      ≤ Real.pi ^ 2 * r ^ 2 * (Real.sqrt (2 * Real.pi) * Real.exp (-(1 / 4) * r)) :=
        mul_le_mul_of_nonneg_left hsqrt this
    _ = _ := by ring

/-- **The kernel is in `L^{5/2}` of the Haar measure**: `∫ I(g)^{5/2} dg < ∞`. -/
theorem lintegral_kernelE_rpow_lt_top : ∫⁻ g, kernelE g ^ (5 / 2 : ℝ) ∂haarC < ∞ := by
  have hΦ : Measurable fun t => ENNReal.ofReal (kernelProfile t) ^ (5 / 2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp measurable_kernelProfile).pow_const _
  have e : (fun g => kernelE g ^ (5 / 2 : ℝ)) =
      fun g => (fun t => ENNReal.ofReal (kernelProfile t) ^ (5 / 2 : ℝ)) (coshDist g) := by
    funext g; rw [kernelE, kernelI_eq_profile]
  rw [e, lintegral_coshDist_sinh hΦ]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hint : IntegrableOn (fun r : ℝ =>
      Real.pi ^ 2 * Real.sqrt (2 * Real.pi) * (r ^ 2 * Real.exp (-(1 / 4) * r))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := 1 / 4)
      (by norm_num) one_pos (by norm_num)
    refine IntegrableOn.congr_fun (h.const_mul (Real.pi ^ 2 * Real.sqrt (2 * Real.pi)))
      (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun r hr => ?_)
    hint.setLIntegral_lt_top
  have hr' : (0 : ℝ) < r := hr
  rw [kernelProfile_cosh hr', ENNReal.ofReal_rpow_of_nonneg (by
      have := (Real.sinh_pos_iff.2 hr').le; positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (sinh_sq_mul_rpow_le hr')

/-- **The kernel is not in `L²`**: `∫ I(g)² dg = ∞`, since `sinh² r · (π r / sinh r)² = π² r²`.
So a Cauchy–Schwarz argument on the links cannot bound the amplitude. -/
theorem lintegral_kernelE_sq_eq_top : ∫⁻ g, kernelE g ^ (2 : ℝ) ∂haarC = ∞ := by
  have hΦ : Measurable fun t => ENNReal.ofReal (kernelProfile t) ^ (2 : ℝ) :=
    (ENNReal.measurable_ofReal.comp measurable_kernelProfile).pow_const _
  have e : (fun g => kernelE g ^ (2 : ℝ)) =
      fun g => (fun t => ENNReal.ofReal (kernelProfile t) ^ (2 : ℝ)) (coshDist g) := by
    funext g; rw [kernelE, kernelI_eq_profile]
  rw [e, lintegral_coshDist_sinh hΦ]
  refine ENNReal.mul_eq_top.2 (Or.inl ⟨(ENNReal.ofReal_pos.2 (by positivity)).ne', ?_⟩)
  have hlow : ∫⁻ _ in Ioi (1 : ℝ), ENNReal.ofReal (Real.pi ^ 2) ≤
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh r ^ 2) *
        (fun t => ENNReal.ofReal (kernelProfile t) ^ (2 : ℝ)) (Real.cosh r) := by
    refine le_trans (setLIntegral_mono' measurableSet_Ioi fun r hr => ?_)
      (lintegral_mono_set (Ioi_subset_Ioi zero_le_one))
    have hr' : (1 : ℝ) < r := hr
    have hr0 : (0 : ℝ) < r := by linarith
    have hs : 0 < Real.sinh r := Real.sinh_pos_iff.2 hr0
    dsimp only
    rw [kernelProfile_cosh hr0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : Real.sinh r ^ 2 * (Real.pi * (r / Real.sinh r)) ^ 2 = Real.pi ^ 2 * r ^ 2 := by
      field_simp
    rw [this]
    have h1 : 1 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg Real.pi)]
  rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top
    (ENNReal.ofReal_pos.2 (by positivity)).ne'] at hlow
  exact top_le_iff.1 hlow

end Lightlike.Lorentz
