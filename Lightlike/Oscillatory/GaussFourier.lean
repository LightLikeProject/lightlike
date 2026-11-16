module

public import Lightlike.Oscillatory.Gaussian

/-!
# The Fourier transform of a complex Gaussian

For a complex symmetric `n × n` matrix `B` whose quadratic form has positive real part on
nonzero real vectors, and any `c ∈ ℂⁿ`,

  `∫_{ℝⁿ} e^{-⟨B x, x⟩/2 + ⟨c, x⟩} dx = G(B) · e^{⟨B⁻¹ c, c⟩/2}`,   `G(B) = ∫_{ℝⁿ} e^{-⟨B x, x⟩/2} dx`

(`integral_gaussLin`). With `c = 2πiξ` this is the Fourier transform of the Gaussian,
Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.6, Theorem 7.6.1.
Stationary phase uses it to write `∫ v(x) e^{-⟨B x, x⟩/2} dx` through the Fourier transform of
`v`.

## Implementation notes

Hörmander proves Theorem 7.6.1 by analytic continuation in `B`. Here the proof is an ODE in
the linear term instead, which needs no holomorphy in several matrix variables:

* `integral_mulVec_mul_gaussLin`: integration by parts along `e_l` gives
  `∫ (B x)_l g = c_l ∫ g` for `g = e^{-⟨B x, x⟩/2 + ⟨c, x⟩}`, since `∂_l g = (c_l - (B x)_l) g`;
* `integral_coord_mul_gaussLin`: hence `∫ x_k g = (B⁻¹ c)_k ∫ g`, using `det B ≠ 0`
  (`det_ne_zero_of_re_pos`, from `G(B)² det B = (2π)ⁿ`);
* `hasDerivAt_integral_gaussLin_smul`: `F(t) = ∫ e^{-⟨B x, x⟩/2 + t⟨c, x⟩} dx` is differentiable
  under the integral sign, with `F'(t) = t ⟨B⁻¹ c, c⟩ F(t)`;
* `integral_gaussLin`: so `F(t) e^{-t² ⟨B⁻¹ c, c⟩/2}` is constant, and `t = 0, 1` give the formula.

All integrability comes from one bound (`integrable_of_norm_le_exp`): a continuous function
dominated by `C e^{a ∑ |xᵢ| - μ ∑ xᵢ²}` with `μ > 0` is integrable.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset
open scoped Real

namespace Lightlike.Oscillatory

variable {n : ℕ}

/-- The complex linear form `x ↦ ∑ᵢ cᵢ xᵢ` on `ℝⁿ`. -/
def linForm (c : Fin n → ℂ) (x : Fin n → ℝ) : ℂ := ∑ i, c i * (x i : ℂ)

/-- A real vector viewed as a vector in `ℂⁿ`. -/
def cvec (x : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ)

/-- The Gaussian with a complex linear term, `e^{-⟨B x, x⟩/2 + ⟨c, x⟩}`. -/
noncomputable def gaussLin (B : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) (x : Fin n → ℝ) : ℂ :=
  cexp (-qform B x / 2 + linForm c x)

/-- `a |y| ≤ μ y² / 4 + a² / μ`. -/
theorem mul_abs_le_sq (a y : ℝ) {μ : ℝ} (hμ : 0 < μ) : a * |y| ≤ μ / 4 * y ^ 2 + a ^ 2 / μ := by
  rw [div_mul_eq_mul_div, div_add_div _ _ (by norm_num) hμ.ne', le_div_iff₀ (by positivity)]
  have h1 : (μ * |y| - 2 * a) ^ 2 = μ ^ 2 * y ^ 2 - 4 * a * μ * |y| + 4 * a ^ 2 := by
    rw [← sq_abs y]; ring
  nlinarith [h1, sq_nonneg (μ * |y| - 2 * a)]

/-- `∑ᵢ aᵢ |xᵢ| ≤ (μ/4) ∑ᵢ xᵢ² + ∑ᵢ aᵢ² / μ`. -/
theorem sum_mul_abs_le (a x : Fin n → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    ∑ i, a i * |x i| ≤ μ / 4 * ∑ i, x i ^ 2 + ∑ i, a i ^ 2 / μ := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => mul_abs_le_sq (a i) (x i) hμ

/-- The real Gaussian `e^{-μ ∑ xᵢ²}` is integrable on `ℝⁿ`. -/
theorem integrable_exp_neg_mul_sum_sq {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-(μ * ∑ i, x i ^ 2))) := by
  have h := (GaussianFourier.integrable_cexp_neg_sum_mul_add (ι := Fin n)
    (b := fun _ => (μ : ℂ)) (fun _ => by rw [ofReal_re]; exact hμ) 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [Finset.mul_sum, ← ofReal_pow, re_sum]

/-- `e^{a ∑ |xᵢ| - μ ∑ xᵢ²}` is integrable on `ℝⁿ` for `μ > 0`. -/
theorem integrable_exp_abs_sub_sq (a : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (a * ∑ i, |x i| - μ * ∑ i, x i ^ 2)) := by
  have hint := (integrable_exp_neg_mul_sum_sq (n := n) (half_pos hμ)).const_mul
    (Real.exp (∑ _i : Fin n, a ^ 2 / (2 * μ)))
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  gcongr
  have h := sum_mul_abs_le (fun _ => a) x (μ := 2 * μ) (by positivity)
  rw [← Finset.mul_sum] at h
  have : 2 * μ / 4 = μ / 2 := by ring
  rw [this] at h
  linarith

/-- An integrability criterion: a continuous function bounded by `C e^{a ∑ |xᵢ| - μ ∑ xᵢ²}`,
`μ > 0`, is integrable on `ℝⁿ`. -/
theorem integrable_of_norm_le_exp {f : (Fin n → ℝ) → ℂ} (hf : Continuous f) {a μ C : ℝ}
    (hμ : 0 < μ) (h : ∀ x, ‖f x‖ ≤ C * Real.exp (a * ∑ i, |x i| - μ * ∑ i, x i ^ 2)) :
    Integrable f :=
  ((integrable_exp_abs_sub_sq a hμ).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

/-- `Re ⟨c, x⟩ ≤ (∑ⱼ |cⱼ|) ∑ᵢ |xᵢ|`. -/
theorem re_linForm_le (c : Fin n → ℂ) (x : Fin n → ℝ) :
    (linForm c x).re ≤ (∑ j, ‖c j‖) * ∑ i, |x i| := by
  rw [linForm, re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [re_mul_ofReal]
  calc (c i).re * x i ≤ |(c i).re * x i| := le_abs_self _
    _ = |(c i).re| * |x i| := abs_mul _ _
    _ ≤ ‖c i‖ * |x i| := by gcongr; exact abs_re_le_norm _
    _ ≤ (∑ j, ‖c j‖) * |x i| := by
        gcongr
        exact Finset.single_le_sum (f := fun j => ‖c j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ i)

/-- `|⟨c, x⟩| ≤ (∑ⱼ |cⱼ|) ∑ᵢ |xᵢ|`. -/
theorem norm_linForm_le (c : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖linForm c x‖ ≤ (∑ j, ‖c j‖) * ∑ i, |x i| := by
  rw [linForm, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  gcongr
  exact Finset.single_le_sum (f := fun j => ‖c j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-- The linear form `x ↦ ⟨c, x⟩` is continuous. -/
theorem continuous_linForm (c : Fin n → ℂ) : Continuous (linForm c) := by
  unfold linForm
  fun_prop

/-- The Gaussian with linear term is continuous. -/
theorem continuous_gaussLin (B : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) :
    Continuous (gaussLin B c) := by
  unfold gaussLin
  exact (((continuous_qform B).neg.div_const 2).add (continuous_linForm c)).cexp

/-- The Gaussian bound: `|e^{-⟨B x, x⟩/2 + ⟨c, x⟩}| ≤ e^{S ∑ |xᵢ| - (μ/2) ∑ xᵢ²}`. -/
theorem norm_gaussLin_le (B : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) {μ : ℝ}
    (hcoer : ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform B x).re) (x : Fin n → ℝ) :
    ‖gaussLin B c x‖ ≤ Real.exp ((∑ j, ‖c j‖) * ∑ i, |x i| - μ / 2 * ∑ i, x i ^ 2) := by
  rw [gaussLin, Complex.norm_exp]
  gcongr
  have h1 := re_linForm_le c x
  have h2 := hcoer x
  simp only [add_re, neg_re, div_ofNat_re]
  linarith

/-- The line derivative of the quadratic form. -/
theorem hasDerivAt_qform_line (B : Matrix (Fin n) (Fin n) ℂ) (x v : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => qform B (x + t • v))
      (∑ i, ∑ j, B i j * ((v i : ℂ) * x j + x i * v j)) 0 := by
  unfold qform
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  have hk : ∀ k, HasDerivAt (fun t : ℝ => (((x + t • v) k : ℝ) : ℂ)) (v k : ℂ) 0 := by
    intro k
    have : HasDerivAt (fun t : ℝ => x k + t * v k) (v k) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v k)).const_add (x k)
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this.ofReal_comp
  have := ((hk i).const_mul (B i j)).mul (hk j)
  convert this using 1
  simp only [zero_smul, add_zero]
  ring

/-- The line derivative of a linear form. -/
theorem hasDerivAt_linForm_line (c : Fin n → ℂ) (x v : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => linForm c (x + t • v)) (linForm c v) 0 := by
  unfold linForm
  refine HasDerivAt.fun_sum fun i _ => ?_
  have : HasDerivAt (fun t : ℝ => x i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
  have h2 := this.ofReal_comp.const_mul (c i)
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h2

/-- For symmetric `B`, the derivative of `⟨B x, x⟩` along the `l`-th coordinate is `2 (B x)ₗ`. -/
theorem sum_qform_line_single {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm) (x : Fin n → ℝ)
    (l : Fin n) :
    ∑ i, ∑ j, B i j * (((Pi.single l 1 : Fin n → ℝ) i : ℂ) * x j + x i *
      ((Pi.single l 1 : Fin n → ℝ) j : ℂ)) = 2 * (B *ᵥ cvec x) l := by
  simp only [mul_add, Finset.sum_add_distrib, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ)),
    ofReal_one, ofReal_zero, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h1 : (∑ i, ∑ j, if i = l then B i j * (x j : ℂ) else 0) = ∑ j, B l j * x j := by
    rw [Fintype.sum_eq_single l (fun i hi => by simp [hi])]
    simp
  have h2 : ∑ i, B i l * (x i : ℂ) = ∑ j, B l j * x j :=
    Finset.sum_congr rfl fun i _ => by rw [hB.apply l i]
  rw [h1, h2]
  simp only [mulVec, dotProduct, cvec]
  ring

/-- `⟨c, e_l⟩ = c_l`. -/
theorem linForm_single (c : Fin n → ℂ) (l : Fin n) : linForm c (Pi.single l 1) = c l := by
  simp only [linForm, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ)), ofReal_one, ofReal_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The coordinate `x_k` as a linear form. -/
theorem linForm_single_left (x : Fin n → ℝ) (k : Fin n) :
    linForm (Pi.single k 1) x = (x k : ℂ) := by
  simp [linForm, Pi.single_apply]

/-- `(B x)_l = ⟨B_l, x⟩`. -/
theorem mulVec_cvec (B : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) (l : Fin n) :
    (B *ᵥ cvec x) l = linForm (B l) x := rfl

/-- `⟨t c, x⟩ = t ⟨c, x⟩`. -/
theorem linForm_smul (t : ℂ) (c : Fin n → ℂ) (x : Fin n → ℝ) :
    linForm (t • c) x = t * linForm c x := by
  simp [linForm, Finset.mul_sum, mul_assoc]

/-- The line derivative of the Gaussian with linear term along the coordinate `e_l`. -/
theorem hasLineDerivAt_gaussLin {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm) (c : Fin n → ℂ)
    (x : Fin n → ℝ) (l : Fin n) :
    HasLineDerivAt ℝ (gaussLin B c) ((-(B *ᵥ cvec x) l + c l) * gaussLin B c x) x
      (Pi.single l 1) := by
  have hq := hasDerivAt_qform_line B x (Pi.single l 1)
  rw [sum_qform_line_single hB] at hq
  have hL := hasDerivAt_linForm_line c x (Pi.single l 1)
  have h := ((hq.neg.div_const 2).add hL).cexp
  unfold HasLineDerivAt gaussLin
  convert h using 1
  simp only [Pi.add_apply, Pi.neg_apply, zero_smul, add_zero, linForm_single]
  ring

/-- Pointwise bound for `⟨d, x⟩ e^{-⟨B x, x⟩/2 + ⟨c, x⟩}`. -/
theorem norm_linForm_mul_gaussLin_le (B : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n → ℂ) {μ : ℝ}
    (hcoer : ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform B x).re) (x : Fin n → ℝ) :
    ‖linForm d x * gaussLin B c x‖ ≤
      Real.exp ((∑ j, ‖d j‖ + ∑ j, ‖c j‖) * ∑ i, |x i| - μ / 2 * ∑ i, x i ^ 2) := by
  rw [norm_mul, add_mul, add_sub_assoc, Real.exp_add]
  have h1 : ‖linForm d x‖ ≤ Real.exp ((∑ j, ‖d j‖) * ∑ i, |x i|) :=
    (norm_linForm_le d x).trans ((le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp _))
  exact mul_le_mul h1 (norm_gaussLin_le B c hcoer x) (norm_nonneg _) (Real.exp_pos _).le

/-- `⟨d, x⟩ e^{-⟨B x, x⟩/2 + ⟨c, x⟩}` is integrable. -/
theorem integrable_linForm_mul_gaussLin (B : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n → ℂ)
    {μ : ℝ} (hμ : 0 < μ) (hcoer : ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform B x).re) :
    Integrable (fun x => linForm d x * gaussLin B c x) :=
  integrable_of_norm_le_exp ((continuous_linForm d).mul (continuous_gaussLin B c))
    (half_pos hμ) (C := 1) fun x => by
      rw [one_mul]; exact norm_linForm_mul_gaussLin_le B c d hcoer x

/-- The Gaussian with linear term is integrable. -/
theorem integrable_gaussLin (B : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    {μ : ℝ} (hμ : 0 < μ) (hcoer : ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform B x).re) :
    Integrable (gaussLin B c) :=
  integrable_of_norm_le_exp (continuous_gaussLin B c) (half_pos hμ) (C := 1) fun x => by
    rw [one_mul]; exact norm_gaussLin_le B c hcoer x

/-- **Integration by parts against the Gaussian**: `∫ (B x)_l e^{-⟨Bx,x⟩/2 + ⟨c,x⟩} dx =
c_l ∫ e^{-⟨Bx,x⟩/2 + ⟨c,x⟩} dx`, since the integral of the derivative along `e_l` vanishes. -/
theorem integral_mulVec_mul_gaussLin {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (c : Fin n → ℂ) (l : Fin n) :
    ∫ x, (B *ᵥ cvec x) l * gaussLin B c x = c l * ∫ x, gaussLin B c x := by
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive B hpos
  have hg := integrable_gaussLin B c hμ hcoer
  have hBg : Integrable (fun x => (B *ᵥ cvec x) l * gaussLin B c x) := by
    simpa only [mulVec_cvec] using integrable_linForm_mul_gaussLin B c (B l) hμ hcoer
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ => (1 : ℂ)) (f' := fun _ => 0) (g := gaussLin B c)
    (g' := fun x => (-(B *ᵥ cvec x) l + c l) * gaussLin B c x) (v := Pi.single l 1)
    (B := ContinuousLinearMap.mul ℝ ℂ) (by simp) ?_ (by simpa using hg)
    (fun x _ => hasDerivAt_const _ _) (fun x _ => hasLineDerivAt_gaussLin hB c x l)
  · simp only [ContinuousLinearMap.mul_apply', one_mul, zero_mul, integral_zero, neg_zero] at key
    have hsplit : ∫ x, (-((B *ᵥ cvec x) l * gaussLin B c x) + c l * gaussLin B c x) =
        -(∫ x, (B *ᵥ cvec x) l * gaussLin B c x) + c l * ∫ x, gaussLin B c x := by
      have e1 : ∫ x, (-((B *ᵥ cvec x) l * gaussLin B c x) + c l * gaussLin B c x) =
          (∫ x, -((B *ᵥ cvec x) l * gaussLin B c x)) + ∫ x, c l * gaussLin B c x :=
        integral_add hBg.neg (hg.const_mul _)
      rw [e1, integral_neg, integral_const_mul]
    have key' : ∫ x, (-((B *ᵥ cvec x) l * gaussLin B c x) + c l * gaussLin B c x) = 0 := by
      rw [← key]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [hsplit] at key'
    linear_combination -key'
  · simp only [ContinuousLinearMap.mul_apply', one_mul]
    refine (hBg.neg.add (hg.const_mul (c l))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.neg_apply]
    ring

/-- A complex symmetric matrix with positive definite real part is invertible. -/
theorem det_ne_zero_of_re_pos {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) : B.det ≠ 0 := by
  intro h
  have := integral_gauss_sq_mul_det B hB hpos
  rw [h, mul_zero] at this
  exact pow_ne_zero n (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) this.symm

/-- The first moments: `∫ x_k e^{-⟨Bx,x⟩/2 + ⟨c,x⟩} dx = (B⁻¹ c)_k ∫ e^{-⟨Bx,x⟩/2 + ⟨c,x⟩} dx`. -/
theorem integral_coord_mul_gaussLin {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (c : Fin n → ℂ) (k : Fin n) :
    ∫ x, (x k : ℂ) * gaussLin B c x = (B⁻¹ *ᵥ c) k * ∫ x, gaussLin B c x := by
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive B hpos
  have hU : IsUnit B.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_re_pos hB hpos)
  have hx : ∀ x : Fin n → ℝ, (x k : ℂ) = ∑ l, B⁻¹ k l * (B *ᵥ cvec x) l := by
    intro x
    have : cvec x = B⁻¹ *ᵥ (B *ᵥ cvec x) := by
      rw [mulVec_mulVec, nonsing_inv_mul B hU, one_mulVec]
    exact (congrFun this k).trans rfl
  have hint : ∀ l, Integrable (fun x => B⁻¹ k l * ((B *ᵥ cvec x) l * gaussLin B c x)) := by
    intro l
    refine Integrable.const_mul ?_ _
    simpa only [mulVec_cvec] using integrable_linForm_mul_gaussLin B c (B l) hμ hcoer
  calc ∫ x, (x k : ℂ) * gaussLin B c x
      = ∫ x, ∑ l, B⁻¹ k l * ((B *ᵥ cvec x) l * gaussLin B c x) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hx x, Finset.sum_mul, mul_assoc]
    _ = ∑ l, B⁻¹ k l * (c l * ∫ x, gaussLin B c x) := by
        rw [integral_finsetSum _ fun l _ => hint l]
        simp only [integral_const_mul, integral_mulVec_mul_gaussLin hB hpos]
    _ = (B⁻¹ *ᵥ c) k * ∫ x, gaussLin B c x := by
        simp only [mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- `t ↦ ∫ e^{-⟨Bx,x⟩/2 + t⟨c,x⟩} dx` is differentiable, with derivative
`∫ ⟨c,x⟩ e^{-⟨Bx,x⟩/2 + t⟨c,x⟩} dx` (differentiation under the integral sign). -/
theorem hasDerivAt_integral_gaussLin_smul (B : Matrix (Fin n) (Fin n) ℂ)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (c : Fin n → ℂ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, gaussLin B ((t : ℂ) • c) x)
      (∫ x, linForm c x * gaussLin B ((t₀ : ℂ) • c) x) t₀ := by
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive B hpos
  set S := ∑ j, ‖c j‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hsmul : ∀ t : ℝ, ∑ j, ‖((t : ℂ) • c) j‖ = |t| * S := by
    intro t
    simp [hS, Finset.mul_sum]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t : ℝ) x => gaussLin B ((t : ℂ) • c) x)
    (F' := fun (t : ℝ) x => linForm c x * gaussLin B ((t : ℂ) • c) x)
    (bound := fun x => Real.exp ((S + (|t₀| + 1) * S) * ∑ i, |x i| - μ / 2 * ∑ i, x i ^ 2))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (continuous_gaussLin B _).aestronglyMeasurable)
    (integrable_gaussLin B _ hμ hcoer)
    ((continuous_linForm c).mul (continuous_gaussLin B _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => ?_) (integrable_exp_abs_sub_sq _ (half_pos hμ))
    (Filter.Eventually.of_forall fun x t _ => ?_)).2
  · refine (norm_linForm_mul_gaussLin_le B _ c hcoer x).trans ?_
    have hx0 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have ht1 : |t - t₀| < 1 := by simpa [Real.dist_eq] using ht
    have ht2 := abs_sub_abs_le_abs_sub t t₀
    have h3 : ∑ j, ‖((t : ℂ) • c) j‖ ≤ (|t₀| + 1) * S := by
      rw [hsmul]; exact mul_le_mul_of_nonneg_right (by linarith) hS0
    refine Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_right ?_ hx0) _)
    rw [← hS]
    linarith
  · have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * linForm c x) (1 * linForm c x) t :=
      (hasDerivAt_id t).ofReal_comp.mul_const _
    have h2 := (h1.const_add (-qform B x / 2)).cexp
    simp only [gaussLin, linForm_smul]
    convert h2 using 1
    ring

/-- **Fourier transform of a complex Gaussian** (Hörmander, *ALPDO I*, §7.6, Theorem 7.6.1, in
the form with a complex linear term): for a complex symmetric `B` with positive definite real
part and any `c ∈ ℂⁿ`,
`∫_{ℝⁿ} e^{-⟨B x, x⟩/2 + ⟨c, x⟩} dx = (∫_{ℝⁿ} e^{-⟨B x, x⟩/2} dx) · e^{⟨B⁻¹ c, c⟩/2}`.

The proof solves an ODE: `F(t) = ∫ e^{-⟨Bx,x⟩/2 + t⟨c,x⟩}` satisfies `F' = t ⟨B⁻¹c, c⟩ F` by
differentiation under the integral sign and integration by parts
(`integral_coord_mul_gaussLin`), so `F(t) e^{-t² ⟨B⁻¹c, c⟩/2}` is constant. -/
theorem integral_gaussLin {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (c : Fin n → ℂ) :
    ∫ x, gaussLin B c x = (∫ x, cexp (-qform B x / 2)) * cexp ((c ⬝ᵥ (B⁻¹ *ᵥ c)) / 2) := by
  set q := c ⬝ᵥ (B⁻¹ *ᵥ c) with hq
  set F : ℝ → ℂ := fun t => ∫ x, gaussLin B ((t : ℂ) • c) x with hF
  have hF' : ∀ t : ℝ, HasDerivAt F (t * q * F t) t := by
    intro t
    have h := hasDerivAt_integral_gaussLin_smul B hpos c t
    convert h using 1
    have hsum : ∀ x : Fin n → ℝ, linForm c x * gaussLin B ((t : ℂ) • c) x =
        ∑ k, c k * ((x k : ℂ) * gaussLin B ((t : ℂ) • c) x) := by
      intro x
      simp only [linForm, Finset.sum_mul, mul_assoc]
    obtain ⟨μ, hμ, hcoer⟩ := exists_coercive B hpos
    have hint : ∀ k, Integrable (fun x => c k * ((x k : ℂ) * gaussLin B ((t : ℂ) • c) x)) := by
      intro k
      refine Integrable.const_mul ?_ _
      simpa only [linForm_single_left] using
        integrable_linForm_mul_gaussLin B ((t : ℂ) • c) (Pi.single k 1) hμ hcoer
    simp_rw [hsum]
    rw [integral_finsetSum _ fun k _ => hint k]
    simp only [integral_const_mul, integral_coord_mul_gaussLin hB hpos, mulVec_smul,
      Pi.smul_apply, smul_eq_mul, hq, hF, dotProduct]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  set φ : ℝ → ℂ := fun t => F t * cexp (-((t : ℂ) ^ 2 * q / 2)) with hφ
  have hφ' : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) ^ 2 * q / 2)) (-((2 * (t : ℂ)) * q / 2)) t := by
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
      have := (((h0.pow 2).mul_const q).div_const 2).neg
      convert this using 1
      norm_num
    have := (hF' t).mul h1.cexp
    convert this using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφ' t).differentiableAt)
    (fun t => (hφ' t).deriv) 1 0
  have h0 : F 0 = ∫ x, cexp (-qform B x / 2) := by
    simp [hF, gaussLin, linForm]
  have h1 : F 1 = ∫ x, gaussLin B c x := by simp [hF]
  simp only [hφ, ofReal_one, ofReal_zero, one_pow, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero, Complex.exp_zero, mul_one]
    at hconst
  rw [← h1, ← h0, ← hconst, mul_assoc, ← Complex.exp_add]
  simp

/-- `integral_gaussLin` with the Gaussian evaluated by `integral_gauss_eq_invSqrtDet`:
`∫_{ℝⁿ} e^{-⟨B x, x⟩/2 + ⟨c, x⟩} dx = (2π)^{n/2} invSqrtDet B · e^{⟨B⁻¹ c, c⟩/2}`
(Hörmander, *ALPDO I*, §7.6, Theorem 7.6.1). -/
theorem integral_gaussLin_eq_invSqrtDet {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (c : Fin n → ℂ) :
    ∫ x, gaussLin B c x =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet B * cexp ((c ⬝ᵥ (B⁻¹ *ᵥ c)) / 2) := by
  rw [integral_gaussLin hB hpos, integral_gauss_eq_invSqrtDet B hB hpos]

end Lightlike.Oscillatory
