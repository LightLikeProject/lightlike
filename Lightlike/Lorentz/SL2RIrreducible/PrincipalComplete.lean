module

public import Lightlike.Lorentz.SL2RIrreducible.PrincipalWeights

/-!
# Completeness of the weight vectors of the principal series in `L²(ℝ)`

If `f ∈ L²(ℝ)` is orthogonal to every weight vector `e_k` (`PrincipalWeights.lean`), then `f = 0`
(`weightL2_complete`).

The proof is the classical one that `L²(ℝ) ≅ L²(circle)`: substitute `x = tan φ`, `φ ∈ (-π/2, π/2)`
(`integral_tan_subst`, `lintegral_tan_subst`, Mathlib's one-dimensional change of variables). Since
`e_k = e_0 · ((x - i)/(x + i))^k` (`weightVec_eq_zero_mul`) and `(tan φ - i)/(tan φ + i) = -e^{2iφ}`
(`ratio_tan`), the pairing `⟪e_k, f⟫` is `(-1)^k` times the `k`-th Fourier coefficient on the circle
`ℝ/πℤ` of the function `H(φ) = conj(e_0(tan φ)) f(tan φ) / cos² φ` (`circleFun`), which is square
integrable with `∫ |H|² = ∫ |f|²` (`norm_circleFun_sq`). Parseval on an interval
(`hasSum_sq_fourierCoeffOn`) gives `∫ |f|² = 0`.

No source is needed beyond Mathlib's Fourier analysis on `AddCircle`; the statement is the
completeness of the `K`-types used in Kitaev, arXiv:1711.08169, §3.1 ("any invariant subspace has a
homogeneous basis"), for the unitary principal series.
-/

@[expose] public section

open MeasureTheory Set Complex Filter
open scoped InnerProductSpace ComplexConjugate ENNReal Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

lemma tan_image : Real.tan '' Ioo (-(π / 2)) (π / 2) = univ := by
  refine eq_univ_of_forall fun y => ⟨Real.arctan y, ⟨Real.neg_pi_div_two_lt_arctan y,
    Real.arctan_lt_pi_div_two y⟩, Real.tan_arctan y⟩

lemma cos_ne_zero_of_mem {φ : ℝ} (hφ : φ ∈ Ioo (-(π / 2)) (π / 2)) : Real.cos φ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo hφ).ne'

/-- Change of variables `x = tan φ`. -/
theorem integral_tan_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E) :
    ∫ x, F x = ∫ φ in Ioo (-(π / 2)) (π / 2), (1 / Real.cos φ ^ 2) • F (Real.tan φ) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioo (-(π / 2)) (π / 2))
    (f := Real.tan) (f' := fun x => 1 / Real.cos x ^ 2) measurableSet_Ioo
    (fun x hx => (Real.hasDerivAt_tan (cos_ne_zero_of_mem hx)).hasDerivWithinAt)
    Real.injOn_tan F
  rw [tan_image, Measure.restrict_univ] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  rw [abs_of_pos (one_div_pos.mpr (pow_pos (Real.cos_pos_of_mem_Ioo hφ) 2))]

theorem lintegral_tan_subst (F : ℝ → ℝ≥0∞) :
    ∫⁻ x, F x = ∫⁻ φ in Ioo (-(π / 2)) (π / 2), ENNReal.ofReal (1 / Real.cos φ ^ 2) * F (Real.tan φ) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioo (-(π / 2)) (π / 2))
    (f := Real.tan) (f' := fun x => 1 / Real.cos x ^ 2) measurableSet_Ioo
    (fun x hx => (Real.hasDerivAt_tan (cos_ne_zero_of_mem hx)).hasDerivWithinAt)
    Real.injOn_tan F
  rw [tan_image, Measure.restrict_univ] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  rw [abs_of_pos (one_div_pos.mpr (pow_pos (Real.cos_pos_of_mem_Ioo hφ) 2))]

/-- `(tan φ - i)/(tan φ + i) = -e^{2iφ}`. -/
lemma ratio_tan {φ : ℝ} (h : Real.cos φ ≠ 0) :
    (((Real.tan φ : ℝ) : ℂ) - Complex.I) / (((Real.tan φ : ℝ) : ℂ) + Complex.I) =
      -Complex.exp (2 * (φ : ℂ) * Complex.I) := by
  have hc : (Real.cos φ : ℂ) ≠ 0 := by exact_mod_cast h
  have hden : ((Real.tan φ : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this
  have e1 : Complex.exp (2 * (φ : ℂ) * Complex.I) =
      (2 * (Real.cos φ : ℂ) ^ 2 - 1) + (2 * (Real.sin φ : ℂ) * (Real.cos φ : ℂ)) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.cos_two_mul, Complex.sin_two_mul, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have htan : ((Real.tan φ : ℝ) : ℂ) = (Real.sin φ : ℂ) / (Real.cos φ : ℂ) := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  have hs : (Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq φ
  rw [htan] at hden
  rw [e1, htan]
  generalize (Real.sin φ : ℂ) = s at hden hs hc ⊢
  generalize (Real.cos φ : ℂ) = c at hden hs hc ⊢
  have key : s - Complex.I * c = -((2 * c ^ 2 - 1) + (2 * s * c) * Complex.I) * (s + Complex.I * c) := by
    linear_combination (2 * c ^ 2 * s) * Complex.I_sq + (2 * Complex.I * c) * hs
  rw [div_eq_iff hden]
  calc s / c - Complex.I = (s - Complex.I * c) / c := by field_simp
    _ = (-((2 * c ^ 2 - 1) + (2 * s * c) * Complex.I) * (s + Complex.I * c)) / c := by rw [key]
    _ = _ := by field_simp

variable (ε : ℤ) (ν : ℝ) (k : ℤ)

/-- `e_k = e_0 · ((x - i)/(x + i))^k`. -/
lemma weightVec_eq_zero_mul (x : ℝ) :
    weightVec ε ν k x = weightVec ε ν 0 x * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ k := by
  have h1 := ofReal_sub_I_ne_zero' x
  unfold weightVec
  rw [zpow_add₀ h1 k ε, zero_add, neg_zero, zpow_zero, zpow_neg, div_zpow]
  ring

/-- The function on the circle whose Fourier coefficients are the pairings with the weight vectors:
`H(φ) = conj(e_0(tan φ)) g(tan φ) / cos² φ`. -/
def circleFun (ε : ℤ) (ν : ℝ) (g : ℝ → ℂ) (φ : ℝ) : ℂ :=
  conj (weightVec ε ν 0 (Real.tan φ)) * g (Real.tan φ) / (((Real.cos φ) ^ 2 : ℝ) : ℂ)

/-- **`‖H(φ)‖² = ‖g(tan φ)‖² / cos² φ`**: the substitution `x = tan φ` is an isometry. -/
lemma norm_circleFun_sq (g : ℝ → ℂ) {φ : ℝ} (hφ : φ ∈ Ioo (-(π / 2)) (π / 2)) :
    ‖circleFun ε ν g φ‖ ^ 2 = 1 / Real.cos φ ^ 2 * ‖g (Real.tan φ)‖ ^ 2 := by
  have hc := Real.cos_pos_of_mem_Ioo hφ
  have hinv := Real.inv_one_add_tan_sq hc.ne'
  unfold circleFun
  rw [norm_div, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_pow, mul_pow, norm_weightVec_sq, hinv]
  field_simp

/-- The conjugate of `e_k(tan φ)`: `conj(e_0(tan φ)) · (-1)^k e^{-2ikφ}`. -/
lemma conj_weightVec_tan {φ : ℝ} (hφ : φ ∈ Ioo (-(π / 2)) (π / 2)) :
    conj (weightVec ε ν k (Real.tan φ)) = conj (weightVec ε ν 0 (Real.tan φ)) *
      ((-1) ^ k * Complex.exp (-(2 * (k : ℂ) * (φ : ℂ) * I))) := by
  rw [weightVec_eq_zero_mul ε ν k (Real.tan φ), map_mul, map_zpow₀, ratio_tan (cos_ne_zero_of_mem hφ)]
  congr 1
  have hconj : conj (-Complex.exp (2 * (φ : ℂ) * I)) = -Complex.exp (-(2 * (φ : ℂ) * I)) := by
    rw [map_neg, ← Complex.exp_conj]
    congr 2
    simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [hconj, neg_eq_neg_one_mul, mul_zpow, ← Complex.exp_int_mul]
  congr 2
  ring

/-- `fourier (-k)` on the circle `ℝ/πℤ` in the coordinates of the interval `(-π/2, π/2]`. -/
lemma fourier_neg_coe (x : ℝ) :
    fourier (-k) (x : AddCircle (π / 2 - -(π / 2))) = Complex.exp (-(2 * (k : ℂ) * (x : ℂ) * I)) := by
  rw [fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Int.cast_neg]
  field_simp
  ring

lemma measurable_tan' : Measurable Real.tan := by
  have : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [this]
  exact Real.measurable_sin.div Real.measurable_cos

lemma measurable_circleFun {g : ℝ → ℂ} (hg : Measurable g) : Measurable (circleFun ε ν g) := by
  unfold circleFun
  refine Measurable.div ((Complex.continuous_conj.measurable.comp
    ((continuous_weightVec ε ν 0).measurable.comp measurable_tan')).mul
      (hg.comp measurable_tan')) ?_
  exact Complex.measurable_ofReal.comp (Real.measurable_cos.pow_const 2)

/-- **The weight vectors are complete in `L²(ℝ)`**: a function orthogonal to every `e_k` is zero. -/
theorem weightL2_complete {f : L2R} (h : ∀ k : ℤ, ⟪weightL2 ε ν k, f⟫_ℂ = 0) : f = 0 := by
  have hg : StronglyMeasurable (f : ℝ → ℂ) := Lp.stronglyMeasurable f
  have hmem : MemLp (f : ℝ → ℂ) 2 volume := Lp.memLp f
  have hgm : Measurable (f : ℝ → ℂ) := hg.measurable
  have hsqint : Integrable (fun x => ‖(f : ℝ → ℂ) x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hmem
  have hab : -(π / 2) < π / 2 := by linarith [Real.pi_pos]
  have hpair : ∀ k : ℤ, ⟪weightL2 ε ν k, f⟫_ℂ =
      ∫ x, conj (weightVec ε ν k x) * (f : ℝ → ℂ) x := by
    intro k
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [weightL2_ae ε ν k] with x e1
    rw [e1, RCLike.inner_apply']
  set H : ℝ → ℂ := circleFun ε ν (f : ℝ → ℂ) with hH
  have hHm : Measurable H := measurable_circleFun ε ν hgm
  -- the Fourier coefficients of `H` vanish
  have hcoef : ∀ k : ℤ, fourierCoeffOn hab H k = 0 := by
    intro k
    rw [fourierCoeffOn_eq_integral H k hab, intervalIntegral.integral_of_le hab.le,
      integral_Ioc_eq_integral_Ioo]
    have key : ∀ x ∈ Ioo (-(π / 2)) (π / 2), fourier (-k) (x : AddCircle (π / 2 - -(π / 2))) • H x =
        (-1 : ℂ) ^ k * ((1 / Real.cos x ^ 2) •
          (conj (weightVec ε ν k (Real.tan x)) * (f : ℝ → ℂ) (Real.tan x))) := by
      intro x hx
      rw [fourier_neg_coe, conj_weightVec_tan ε ν k hx, smul_eq_mul, Complex.real_smul, hH, circleFun]
      simp only [Complex.ofReal_div, Complex.ofReal_one]
      have hpm : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by
        rw [← mul_zpow]; norm_num
      linear_combination (-(Complex.exp (-(2 * (k : ℂ) * (x : ℂ) * I)) *
        conj (weightVec ε ν 0 (Real.tan x)) * (f : ℝ → ℂ) (Real.tan x) /
          (((Real.cos x) ^ 2 : ℝ) : ℂ))) * hpm
    have hsub := integral_tan_subst (fun x => conj (weightVec ε ν k x) * (f : ℝ → ℂ) x)
    rw [setIntegral_congr_fun measurableSet_Ioo key, integral_const_mul, ← hsub, ← hpair k, h k,
      mul_zero, smul_zero]
  -- `H` is square integrable on the interval
  have hHint : IntegrableOn (fun φ => ‖H φ‖ ^ 2) (Ioo (-(π / 2)) (π / 2)) := by
    refine ⟨(hHm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun φ => by positivity)]
    have hcv := lintegral_tan_subst (fun x => ENNReal.ofReal (‖(f : ℝ → ℂ) x‖ ^ 2))
    have hfin : ∫⁻ x, ENNReal.ofReal (‖(f : ℝ → ℂ) x‖ ^ 2) < ⊤ := hsqint.lintegral_lt_top
    rw [hcv] at hfin
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine setLIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
    rw [hH, norm_circleFun_sq ε ν _ hφ,
      ENNReal.ofReal_mul (by have := Real.cos_pos_of_mem_Ioo hφ; positivity)]
  have hHL2 : MemLp H 2 (volume.restrict (Ioc (-(π / 2)) (π / 2))) := by
    rw [memLp_two_iff_integrable_sq_norm hHm.aestronglyMeasurable]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hHint
  -- Parseval
  have hP := hasSum_sq_fourierCoeffOn hab hHL2
  have hzero : HasSum (fun i : ℤ => ‖fourierCoeffOn hab H i‖ ^ 2) 0 := by
    simp only [hcoef, norm_zero]
    simp
  have hP0 := hP.unique hzero
  have hint0 : ∫ x in (-(π / 2))..(π / 2), ‖H x‖ ^ 2 = 0 := by
    have hne : (π / 2 - -(π / 2))⁻¹ ≠ 0 := by
      have : 0 < π / 2 - -(π / 2) := by linarith [Real.pi_pos]
      exact inv_ne_zero this.ne'
    rw [smul_eq_zero] at hP0
    exact hP0.resolve_left hne
  have h0 : ∫ x, ‖(f : ℝ → ℂ) x‖ ^ 2 = 0 := by
    rw [integral_tan_subst (fun x => ‖(f : ℝ → ℂ) x‖ ^ 2)]
    rw [setIntegral_congr_fun measurableSet_Ioo (g := fun φ => ‖H φ‖ ^ 2) (fun φ hφ => by
      simp only [smul_eq_mul]
      rw [hH, norm_circleFun_sq ε ν _ hφ])]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    exact hint0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hsqint).mp h0
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hae] with x hx
  have : ‖(f : ℝ → ℂ) x‖ ^ 2 = 0 := hx
  simpa using this

end Lightlike.Lorentz.SL2R
