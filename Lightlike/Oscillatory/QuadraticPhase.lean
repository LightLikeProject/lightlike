module

public import Lightlike.Oscillatory.GaussFourier
public import Lightlike.Oscillatory.LaplaceRay

/-!
# The quadratic-phase lemma

Let `A` be a complex symmetric `n × n` matrix with `det A ≠ 0` and `Im ⟨A x, x⟩ ≥ 0` for real
`x`, and let `u` be smooth with compact support. Then, as `τ → ∞`,

  `∫_{ℝⁿ} u(x) e^{iτ⟨A x, x⟩/2} dx = (2π/τ)^{n/2} invSqrtDet(-iA) u(0) + O(τ^{-n/2-1})`

(`quadratic_phase`), and the integral is `O(τ^{-n/2})` (`quadratic_phase_base`). This is the case
`k = 1` of Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.7,
Lemma 7.7.3, the model case of stationary phase (Theorem 7.7.5). The coefficient
`invSqrtDet(-iA)` is Hörmander's branch of `(det(-iA))^{-1/2}`: the product of the principal
roots `λ^{-1/2}` over the eigenvalues `λ` of `-iA`, all of which lie in the closed right
half-plane.

Hörmander bounds the error by Sobolev norms of `u`. Here the error is
`C (|u(0)| + ∫ |ξ|² |𝓕(u e^{|x|²/2})(ξ)| dξ) τ^{-n/2-1}` with `C` depending only on `A`
(`quadratic_phase_uniform`, and `quadratic_phase_base_uniform` for the base bound). The
reduction of a general phase to its quadratic part needs this uniformity in the amplitude.

## Method

* Damping (`integral_eq_integral_dampMat`): `u e^{iτ⟨A x, x⟩/2} = v e^{-⟨B_τ x, x⟩/2}` with
  `v = u e^{|x|²/2}` (`gaussWeighted`), still smooth with compact support, and
  `B_τ = 1 - iτA` (`dampMat`), whose quadratic form has positive real part
  (`re_qform_dampMat_pos`). The integral is now a Gaussian integral as in `Gaussian.lean`.
* Fourier representation (`integral_mul_gauss_eq_fourier`): Fourier inversion for `v` and the
  Fourier transform of the Gaussian (`integral_gaussLin`) give
  `∫ v e^{-⟨B x, x⟩/2} = G(B) ∫ 𝓕v(ξ) e^{-2π² ⟨ξ, B⁻¹ ξ⟩} dξ`.
* Leading term (`norm_integral_mul_gauss_sub_le`): `Re ⟨ξ, B⁻¹ ξ⟩ ≥ 0`, so
  `|e^{-z} - 1| ≤ |z|`, and with `∫ 𝓕v = v(0)` the error is at most
  `|G(B)| 2π² κ ∫ |ξ|² |𝓕v|` whenever `|⟨ξ, B⁻¹ ξ⟩| ≤ κ |ξ|²`.
* `κ = O(1/τ)` (`norm_dampMat_inv_mulVec_le`): from `B_τ η = ζ`,
  `η = (i/τ) A⁻¹ (ζ - η)`, so `|η| ≤ (2K/τ) |ζ|` once `τ ≥ 2K`, `K = ∑ |(A⁻¹)ᵢⱼ|`.
* The determinant factor (`invSqrtDet_dampMat`, `eigProd_inv_sub`): the eigenvalues of `B_τ`
  are `1 - iτμ` over the eigenvalues `μ` of `A`, and `Im μ ≥ 0` (`im_nonneg_of_mem_roots`).
  Hence `invSqrtDet B_τ = τ^{-n/2} ∏ (1/τ - iμ)^{-1/2}`. The product (`eigProd`) is
  differentiable at `0`, where each `-iμ` lies in the slit plane, so it is
  `invSqrtDet(-iA) + O(1/τ)`.

The proof uses no Morse lemma. Stationary phase with a complex phase cannot rest on one: for
`φ(x) = i x²/2 + x³` there is no real change of variables `y(x)` near `0` with
`φ = i y²/2`, since `y² = x² - 2i x³` is not real for real `x ≠ 0`.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset
open scoped Real FourierTransform ContDiff

namespace Lightlike.Oscillatory

variable {n : ℕ}

/-- A function on `ℝⁿ = Fin n → ℝ` transported to the Euclidean space, where Mathlib's Fourier
transform lives. -/
noncomputable def toEuc (v : (Fin n → ℝ) → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun y => v (WithLp.ofLp y)

/-- `toEuc v` agrees with `v` under the identification `WithLp.toLp 2`. -/
theorem toEuc_toLp (v : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : toEuc v (WithLp.toLp 2 x) = v x := rfl

/-- `toEuc` preserves smoothness. -/
theorem contDiff_toEuc {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (toEuc v) :=
  hv.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff

/-- `toEuc` preserves compact support. -/
theorem hasCompactSupport_toEuc {v : (Fin n → ℝ) → ℂ} (hv : HasCompactSupport v) :
    HasCompactSupport (toEuc v) :=
  hv.comp_homeomorph (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toHomeomorph

/-- Fourier inversion for a smooth compactly supported `v`, at `x ∈ ℝⁿ`. -/
theorem fourier_inversion_toEuc {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) (x : Fin n → ℝ) :
    v x = ∫ ξ, 𝐞 (inner ℝ ξ (WithLp.toLp 2 x)) • 𝓕 (toEuc v) ξ := by
  set S := (hasCompactSupport_toEuc hvs).toSchwartzMap (contDiff_toEuc hv)
  have hS : (S : EuclideanSpace ℝ (Fin n) → ℂ) = toEuc v := rfl
  have h := Continuous.fourierInv_fourier_eq (f := toEuc v) (contDiff_toEuc hv).continuous
    (hS ▸ S.integrable) (by rw [← hS, ← SchwartzMap.fourier_coe]; exact (𝓕 S).integrable)
  rw [← toEuc_toLp v x, ← h, Real.fourierInv_eq]
  simp only [h]

/-- The Fourier transform of `toEuc v` is integrable and continuous. -/
theorem fourier_toEuc_props {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) :
    Integrable (𝓕 (toEuc v)) ∧ Continuous (𝓕 (toEuc v)) ∧
      ∀ k : ℕ, Integrable (fun ξ => ‖ξ‖ ^ k * ‖𝓕 (toEuc v) ξ‖) := by
  set S := (hasCompactSupport_toEuc hvs).toSchwartzMap (contDiff_toEuc hv)
  have hS : 𝓕 (toEuc v) = ⇑(𝓕 S : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) := by
    rw [SchwartzMap.fourier_coe]; rfl
  rw [hS]
  exact ⟨(𝓕 S).integrable, (𝓕 S).continuous, fun k => (𝓕 S).integrable_pow_mul volume k⟩

/-- The character `𝐞 ⟨ξ, x⟩` as a Gaussian linear term: `𝐞 ⟨ξ, x⟩ = e^{⟨2πi ξ, x⟩}`. -/
theorem fourierChar_inner_eq (ξ : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) :
    ((𝐞 (inner ℝ ξ (WithLp.toLp 2 x)) : ℂ)) =
      cexp (linForm ((2 * π * I : ℂ) • cvec (WithLp.ofLp ξ)) x) := by
  have h : inner ℝ ξ (WithLp.toLp 2 x) = ∑ i, x i * ξ.ofLp i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Real.ringHom_apply]
  rw [Real.fourierChar_apply, h]
  congr 1
  simp only [linForm, cvec, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Fourier representation of a Gaussian integral.** For complex symmetric `B` with positive
definite real part and smooth compactly supported `v`,
`∫ v(x) e^{-⟨B x, x⟩/2} dx = G(B) ∫ 𝓕v(ξ) e^{-2π² ⟨B⁻¹ ξ, ξ⟩} dξ`, `G(B) = ∫ e^{-⟨B x, x⟩/2} dx`.
This is the Parseval step in the proof of Hörmander, *ALPDO I*, Lemma 7.7.3. -/
theorem integral_mul_gauss_eq_fourier {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) :
    ∫ x, v x * cexp (-qform B x / 2) =
      (∫ x, cexp (-qform B x / 2)) *
        ∫ ξ, 𝓕 (toEuc v) ξ *
          cexp (-(2 * (π : ℂ) ^ 2) * (cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ)))) := by
  obtain ⟨hFi, hFc, -⟩ := fourier_toEuc_props hv hvs
  set Fv := 𝓕 (toEuc v) with hFv
  set g : (Fin n → ℝ) → ℂ := fun x => cexp (-qform B x / 2) with hg
  have hgi : Integrable g := integrable_gauss B hpos
  set F : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x ξ => (𝐞 (inner ℝ ξ (WithLp.toLp 2 x)) • Fv ξ) * g x with hF
  have hprod : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hdom := hgi.norm.mul_prod hFi.norm
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      refine Continuous.mul (Continuous.smul ?_ (hFc.comp continuous_snd))
        ((continuous_qform B).neg.div_const 2 |>.cexp |>.comp continuous_fst)
      exact continuous_induced_dom.comp (Real.continuous_fourierChar.comp (continuous_snd.inner
        ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp continuous_fst)))
    · simp only [hF, Function.uncurry, norm_mul, Circle.norm_smul]
      exact le_of_eq (mul_comm _ _)
  have hinner : ∀ ξ : EuclideanSpace ℝ (Fin n), ∫ x, F x ξ =
      Fv ξ * ((∫ x, cexp (-qform B x / 2)) *
        cexp (-(2 * (π : ℂ) ^ 2) * (cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ))))) := by
    intro ξ
    have hpt : ∀ x, F x ξ = Fv ξ * gaussLin B ((2 * π * I : ℂ) • cvec (WithLp.ofLp ξ)) x := by
      intro x
      simp only [hF, hg, Circle.smul_def, fourierChar_inner_eq, gaussLin, Complex.exp_add,
        smul_eq_mul]
      ring
    simp only [hpt, integral_const_mul, integral_gaussLin hB hpos, smul_dotProduct, mulVec_smul,
      dotProduct_smul, smul_eq_mul]
    congr 3
    ring_nf
    rw [I_sq]
    ring
  calc ∫ x, v x * cexp (-qform B x / 2) = ∫ x, ∫ ξ, F x ξ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hF]
        rw [integral_mul_const, ← fourier_inversion_toEuc hv hvs x]
    _ = ∫ ξ, ∫ x, F x ξ := integral_integral_swap hprod
    _ = _ := by
        simp only [hinner]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only
        ring

/-! ### Bounds from the Fourier representation -/

/-- The complexified coordinate vector of `ξ ∈ EuclideanSpace ℝ (Fin n)` is continuous in `ξ`. -/
theorem continuous_cvec_ofLp :
    Continuous fun ξ : EuclideanSpace ℝ (Fin n) => cvec (WithLp.ofLp ξ) :=
  continuous_pi fun i => continuous_ofReal.comp
    ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)))

/-- For real `ξ`, `Re ⟨ξ, B⁻¹ ξ⟩ ≥ 0` when `B` is symmetric with positive definite real part. -/
theorem re_dotProduct_inv_mulVec_nonneg {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (ξ : Fin n → ℝ) :
    0 ≤ (cvec ξ ⬝ᵥ (B⁻¹ *ᵥ cvec ξ)).re := by
  have hdet := det_ne_zero_of_re_pos hB hpos
  set η := B⁻¹ *ᵥ cvec ξ with hη
  have hBη : B *ᵥ η = cvec ξ := by
    rw [hη, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have hsum := sum_star_mul_mulVec hB (fun i => (η i).re) (fun i => (η i).im)
  simp only [re_add_im] at hsum
  rw [hBη] at hsum
  have hre : (cvec ξ ⬝ᵥ η).re = (∑ i, star (η i) * cvec ξ i).re := by
    simp only [dotProduct, re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [cvec, mul_comm]
  rw [hre, hsum, add_re]
  exact add_nonneg (re_qform_nonneg hpos _) (re_qform_nonneg hpos _)

/-- The exponent `-2π² ⟨ξ, B⁻¹ ξ⟩` of the Fourier-side Gaussian has nonpositive real part. -/
theorem re_fourierGauss_exponent_nonpos {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (ξ : Fin n → ℝ) :
    (-(2 * (π : ℂ) ^ 2) * (cvec ξ ⬝ᵥ (B⁻¹ *ᵥ cvec ξ))).re ≤ 0 := by
  have hc : (-(2 * (π : ℂ) ^ 2)) = ((-(2 * π ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, re_ofReal_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [Real.pi_pos])
    (re_dotProduct_inv_mulVec_nonneg hB hpos ξ)

/-- The Fourier-side Gaussian `e^{-2π² ⟨ξ, B⁻¹ ξ⟩}` has modulus at most `1`. -/
theorem norm_fourierGauss_le_one {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖cexp (-(2 * (π : ℂ) ^ 2) * (cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ))))‖ ≤ 1 := by
  rw [norm_exp, Real.exp_le_one_iff]
  exact re_fourierGauss_exponent_nonpos hB hpos _

/-- The Fourier-side Gaussian `e^{-2π² ⟨ξ, B⁻¹ ξ⟩}` is continuous in `ξ`. -/
theorem continuous_fourierGauss (B : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun ξ : EuclideanSpace ℝ (Fin n) =>
      cexp (-(2 * (π : ℂ) ^ 2) * (cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ)))) :=
  (continuous_const.mul (continuous_cvec_ofLp.dotProduct
    (continuous_const.matrix_mulVec continuous_cvec_ofLp))).cexp

/-- Fourier inversion at the origin: `v 0 = ∫ 𝓕v`. -/
theorem integral_fourier_toEuc {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) : ∫ ξ, 𝓕 (toEuc v) ξ = v 0 := by
  rw [fourier_inversion_toEuc hv hvs 0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp [WithLp.toLp_zero]

/-- **Leading term of a Gaussian integral.** If `|⟨ξ, B⁻¹ ξ⟩| ≤ κ |ξ|²`, then
`|∫ v e^{-⟨Bx,x⟩/2} - v(0) G(B)| ≤ |G(B)| · 2π² κ ∫ |ξ|² |𝓕v(ξ)| dξ`. -/
theorem norm_integral_mul_gauss_sub_le {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) {κ : ℝ}
    (hκ : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ))‖ ≤ κ * ‖ξ‖ ^ 2) :
    ‖(∫ x, v x * cexp (-qform B x / 2)) - v 0 * ∫ x, cexp (-qform B x / 2)‖ ≤
      ‖∫ x, cexp (-qform B x / 2)‖ * (2 * π ^ 2 * κ * ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc v) ξ‖) := by
  obtain ⟨hFi, -, hFk⟩ := fourier_toEuc_props hv hvs
  have hFe : Integrable fun ξ => 𝓕 (toEuc v) ξ *
      cexp (-(2 * (π : ℂ) ^ 2) * (cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ)))) :=
    hFi.norm.mono' (hFi.aestronglyMeasurable.mul (continuous_fourierGauss B).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_fourierGauss_le_one hB hpos ξ))
  rw [integral_mul_gauss_eq_fourier hB hpos hv hvs, ← integral_fourier_toEuc hv hvs,
    mul_comm (∫ ξ, 𝓕 (toEuc v) ξ), ← mul_sub, norm_mul, ← integral_sub hFe hFi]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hFk 2).const_mul _) (Filter.Eventually.of_forall fun ξ => ?_)
  set w := cvec (WithLp.ofLp ξ) ⬝ᵥ (B⁻¹ *ᵥ cvec (WithLp.ofLp ξ))
  have hu := re_fourierGauss_exponent_nonpos hB hpos (WithLp.ofLp ξ)
  have he : ‖cexp (-(2 * (π : ℂ) ^ 2) * w) - 1‖ ≤ 2 * π ^ 2 * ‖w‖ := by
    have h := norm_cexp_sub_le (-(2 * (π : ℂ) ^ 2) * w) 0
    rw [Complex.exp_zero, sub_zero, zero_re, max_eq_right hu, Real.exp_zero, one_mul, norm_mul,
      norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_two] at h
    exact h
  calc ‖𝓕 (toEuc v) ξ * cexp (-(2 * (π : ℂ) ^ 2) * w) - 𝓕 (toEuc v) ξ‖
      = ‖𝓕 (toEuc v) ξ‖ * ‖cexp (-(2 * (π : ℂ) ^ 2) * w) - 1‖ := by
        rw [← norm_mul, mul_sub, mul_one]
    _ ≤ ‖𝓕 (toEuc v) ξ‖ * (2 * π ^ 2 * (κ * ‖ξ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left (hκ ξ)
          (by positivity))) (norm_nonneg _)
    _ = 2 * π ^ 2 * κ * (‖ξ‖ ^ 2 * ‖𝓕 (toEuc v) ξ‖) := by ring

/-- **Base bound for a Gaussian integral:** `|∫ v e^{-⟨Bx,x⟩/2}| ≤ |G(B)| ∫ |𝓕v|`. -/
theorem norm_integral_mul_gauss_le {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform B x).re) {v : (Fin n → ℝ) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvs : HasCompactSupport v) :
    ‖∫ x, v x * cexp (-qform B x / 2)‖ ≤
      ‖∫ x, cexp (-qform B x / 2)‖ * ∫ ξ, ‖𝓕 (toEuc v) ξ‖ := by
  obtain ⟨hFi, -, -⟩ := fourier_toEuc_props hv hvs
  rw [integral_mul_gauss_eq_fourier hB hpos hv hvs, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine norm_integral_le_of_norm_le hFi.norm (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_fourierGauss_le_one hB hpos ξ)

/-! ### The damped matrix `1 - iτA` -/

/-- Sum of the absolute values of the entries; it bounds `M` as an operator on the sup norm. -/
noncomputable def entrySum (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

/-- `entrySum` is nonnegative. -/
theorem entrySum_nonneg (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ entrySum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `entrySum M` bounds `M` as an operator on `Fin n → ℂ` with the sup norm. -/
theorem norm_mulVec_le (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖M *ᵥ v‖ ≤ entrySum M * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (entrySum_nonneg M) (norm_nonneg v))).mpr
    fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ j, M i j * v j‖ := rfl
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ entrySum M * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
        (norm_nonneg v)

/-- `|a ⬝ᵥ b| ≤ n |a| |b|` in the sup norm. -/
theorem norm_dotProduct_le (a b : Fin n → ℂ) : ‖a ⬝ᵥ b‖ ≤ n * (‖a‖ * ‖b‖) := by
  calc ‖a ⬝ᵥ b‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
    _ ≤ ∑ _i : Fin n, ‖a‖ * ‖b‖ := Finset.sum_le_sum fun i _ =>
        mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i) (norm_nonneg _) (norm_nonneg _)
    _ = n * (‖a‖ * ‖b‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The sup norm of the coordinate vector is at most the Euclidean norm. -/
theorem norm_cvec_ofLp_le (ξ : EuclideanSpace ℝ (Fin n)) : ‖cvec (WithLp.ofLp ξ)‖ ≤ ‖ξ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg ξ)).mpr fun i => ?_
  simp only [cvec, Complex.norm_real]
  exact PiLp.norm_apply_le ξ i

/-- The damped matrix `B_τ = 1 - iτA`. -/
noncomputable def dampMat (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (-(I * τ)) • A

/-- `1 - iτA` is symmetric when `A` is. -/
theorem dampMat_isSymm {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm) (τ : ℝ) :
    (dampMat A τ).IsSymm :=
  (isSymm_one.smul _).add (hA.smul _)

/-- `⟨(1 - iτA) x, x⟩ = |x|² - iτ ⟨A x, x⟩`. -/
theorem qform_dampMat (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) (x : Fin n → ℝ) :
    qform (dampMat A τ) x = ∑ i, (x i : ℂ) ^ 2 - I * τ * qform A x := by
  rw [dampMat, qform_smul_one_add_smul]; ring

/-- `Re ⟨(1 - iτA) x, x⟩ = |x|² + τ Im ⟨A x, x⟩`. -/
theorem re_qform_dampMat (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℝ) (x : Fin n → ℝ) :
    (qform (dampMat A τ) x).re = ∑ i, x i ^ 2 + τ * (qform A x).im := by
  rw [qform_dampMat]
  simp only [sub_re, re_sum, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  have h : ∀ i, ((x i : ℂ) ^ 2).re = x i ^ 2 := fun i => by rw [← ofReal_pow, ofReal_re]
  simp only [h, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

/-- If `Im ⟨A x, x⟩ ≥ 0` and `τ ≥ 0`, the quadratic form of `1 - iτA` has positive real part on
nonzero real vectors. -/
theorem re_qform_dampMat_pos {A : Matrix (Fin n) (Fin n) ℂ} (hIm : ∀ x, 0 ≤ (qform A x).im)
    {τ : ℝ} (hτ : 0 ≤ τ) : ∀ x ≠ 0, 0 < (qform (dampMat A τ) x).re := by
  intro x hx
  rw [re_qform_dampMat]
  linarith [mul_nonneg hτ (hIm x), sum_sq_pos hx]

/-- If `Im ⟨Ax, x⟩ ≥ 0` for real `x`, every eigenvalue of the symmetric matrix `A` has
`Im μ ≥ 0`. -/
theorem im_nonneg_of_mem_roots {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) {μ : ℂ} (hμ : μ ∈ A.charpoly.roots) : 0 ≤ μ.im := by
  by_contra h
  have h' : μ.im < 0 := not_le.mp h
  set τ : ℝ := -1 / μ.im with hτ
  have hτ0 : 0 ≤ τ := div_nonneg_of_nonpos (by norm_num) h'.le
  have hmem : 1 + (-(I * τ)) * μ ∈ (dampMat A τ).charpoly.roots := by
    rw [dampMat, roots_charpoly_smul_one_add_smul]
    exact Multiset.mem_map_of_mem _ hμ
  have := re_pos_of_mem_roots (dampMat_isSymm hA τ) (re_qform_dampMat_pos hIm hτ0) hmem
  have hre : (1 + (-(I * τ)) * μ).re = 1 + τ * μ.im := by simp [mul_re]
  rw [hre, hτ, div_mul_cancel₀ _ h'.ne] at this
  norm_num at this

/-- `‖(1 - iτA)⁻¹ ζ‖ ≤ (2K/τ) ‖ζ‖` for `τ ≥ 2K`, `K = entrySum A⁻¹` (sup norms). -/
theorem norm_dampMat_inv_mulVec_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : 2 * entrySum A⁻¹ ≤ τ) (ζ : Fin n → ℂ) :
    ‖(dampMat A τ)⁻¹ *ᵥ ζ‖ ≤ 2 * entrySum A⁻¹ / τ * ‖ζ‖ := by
  have hdetB := det_ne_zero_of_re_pos (dampMat_isSymm hA τ) (re_qform_dampMat_pos hIm hτ0.le)
  set η := (dampMat A τ)⁻¹ *ᵥ ζ with hη
  set K := entrySum A⁻¹
  have hBη : dampMat A τ *ᵥ η = ζ := by
    rw [hη, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetB), one_mulVec]
  have h1 : (-(I * τ)) • (A *ᵥ η) = ζ - η := by
    rw [dampMat, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, one_smul] at hBη
    rw [← hBη]; abel
  have h2 : (-(I * τ)) • η = A⁻¹ *ᵥ (ζ - η) := by
    rw [← h1, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      one_mulVec]
  have h3 : τ * ‖η‖ ≤ K * (‖ζ‖ + ‖η‖) := by
    have h := norm_mulVec_le A⁻¹ (ζ - η)
    rw [← h2, norm_smul] at h
    have hn : ‖-(I * (τ : ℂ))‖ = τ := by
      rw [norm_neg, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
    rw [hn] at h
    exact h.trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (entrySum_nonneg _))
  rw [div_mul_eq_mul_div, le_div_iff₀ hτ0]
  nlinarith [norm_nonneg η, norm_nonneg ζ, entrySum_nonneg A⁻¹,
    mul_nonneg (sub_nonneg.mpr hτ) (norm_nonneg η)]

/-- The constant `κ` of `norm_integral_mul_gauss_sub_le` for `B = 1 - iτA` is `O(1/τ)`. -/
theorem norm_dotProduct_dampMat_inv_le {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) {τ : ℝ} (hτ0 : 0 < τ)
    (hτ : 2 * entrySum A⁻¹ ≤ τ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖cvec (WithLp.ofLp ξ) ⬝ᵥ ((dampMat A τ)⁻¹ *ᵥ cvec (WithLp.ofLp ξ))‖ ≤
      n * (2 * entrySum A⁻¹ / τ) * ‖ξ‖ ^ 2 := by
  have h := norm_dampMat_inv_mulVec_le hA hIm hdet hτ0 hτ (cvec (WithLp.ofLp ξ))
  have hc := norm_cvec_ofLp_le ξ
  have hK : 0 ≤ 2 * entrySum A⁻¹ / τ := div_nonneg (by linarith [entrySum_nonneg A⁻¹]) hτ0.le
  calc _ ≤ n * (‖cvec (WithLp.ofLp ξ)‖ * ‖(dampMat A τ)⁻¹ *ᵥ cvec (WithLp.ofLp ξ)‖) :=
        norm_dotProduct_le _ _
    _ ≤ n * (‖ξ‖ * (2 * entrySum A⁻¹ / τ * ‖ξ‖)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hc (h.trans ?_) (norm_nonneg _)
          (norm_nonneg _)) (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_left hc hK
    _ = _ := by ring

/-! ### Asymptotics of `invSqrtDet (1 - iτA)` -/

/-- A nonzero complex number with nonnegative real part lies in the slit plane. -/
theorem mem_slitPlane_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  rw [not_or, not_lt, not_not] at h
  exact hw0 (Complex.ext (le_antisymm h.1 hw) h.2)

/-- `(r z)^c = r^c z^c` for real `r > 0` and `z ≠ 0`. -/
theorem cpow_ofReal_mul {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (c : ℂ) :
    ((r : ℂ) * z) ^ c = (r : ℂ) ^ c * z ^ c := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') hz),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), cpow_def_of_ne_zero hz, log_ofReal_mul hr hz,
    ← Complex.exp_add, ofReal_log hr.le]
  ring_nf

/-- The function `s ↦ ∏_w (s + w)^{-1/2}` is differentiable at `0` when every `w` lies in the
slit plane. -/
theorem differentiableAt_prod_cpow (s : Multiset ℂ) (hs : ∀ w ∈ s, w ∈ slitPlane) :
    DifferentiableAt ℝ (fun t : ℝ => (s.map fun w => ((t : ℂ) + w) ^ (-(1 / 2 : ℂ))).prod) 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine DifferentiableAt.mul ?_ (ih fun w hw => hs w (Multiset.mem_cons_of_mem hw))
    have ha : ((0 : ℝ) : ℂ) + a ∈ slitPlane := by
      rw [ofReal_zero, zero_add]; exact hs a (Multiset.mem_cons_self a s)
    exact (((hasDerivAt_id _).add_const a).cpow_const (c := -(1 / 2 : ℂ)) ha).comp_ofReal
      |>.differentiableAt

/-- The eigenvalue function `f_A(s) = ∏_μ (s - iμ)^{-1/2}` over the eigenvalues `μ` of `A`. -/
noncomputable def eigProd (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) : ℂ :=
  (A.charpoly.roots.map fun μ => ((s : ℂ) + -I * μ) ^ (-(1 / 2 : ℂ))).prod

/-- At `s = 0`, `eigProd A 0 = invSqrtDet(-iA)`. -/
theorem eigProd_zero (A : Matrix (Fin n) (Fin n) ℂ) : eigProd A 0 = invSqrtDet (-I • A) := by
  have h := invSqrtDet_smul_one_add_smul A 0 (-I)
  rw [zero_smul, zero_add] at h
  rw [h, eigProd]
  simp

/-- The characteristic polynomial of an `n × n` complex matrix has `n` roots with multiplicity. -/
theorem card_roots_charpoly (A : Matrix (Fin n) (Fin n) ℂ) : A.charpoly.roots.card = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- A matrix with nonzero determinant has no zero eigenvalue. -/
theorem ne_zero_of_mem_roots {A : Matrix (Fin n) (Fin n) ℂ} (hdet : A.det ≠ 0) {μ : ℂ}
    (hμ : μ ∈ A.charpoly.roots) : μ ≠ 0 := by
  rintro rfl
  exact hdet (by rw [det_eq_prod_roots_charpoly]; exact Multiset.prod_eq_zero hμ)

/-- `invSqrtDet (1 - iτA) = τ^{-n/2} f_A(1/τ)`. -/
theorem invSqrtDet_dampMat {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) {τ : ℝ} (hτ : 0 < τ) :
    invSqrtDet (dampMat A τ) = ((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) * eigProd A τ⁻¹ := by
  rw [dampMat, invSqrtDet_smul_one_add_smul, eigProd]
  have hfac : ∀ μ ∈ A.charpoly.roots, (1 + -(I * τ) * μ) ^ (-(1 / 2 : ℂ)) =
      (τ : ℂ) ^ (-(1 / 2 : ℂ)) * (((τ⁻¹ : ℝ) : ℂ) + -I * μ) ^ (-(1 / 2 : ℂ)) := by
    intro μ hμ
    have hne : ((τ⁻¹ : ℝ) : ℂ) + -I * μ ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp [mul_re] at this
      linarith [inv_pos.mpr hτ, im_nonneg_of_mem_roots hA hIm hμ]
    rw [← cpow_ofReal_mul hτ hne]
    congr 1
    have hτc : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ.ne'
    push_cast
    rw [mul_add, mul_inv_cancel₀ hτc]
    ring
  rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, Multiset.map_const',
    Multiset.prod_replicate, card_roots_charpoly]
  congr 1
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hτ.le,
    ← Complex.ofReal_pow, ← Real.rpow_mul_natCast hτ.le]
  congr 2
  ring

/-- `f_A(1/τ) = f_A(0) + O(1/τ)`. -/
theorem eigProd_inv_sub {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀, ‖eigProd A τ⁻¹ - eigProd A 0‖ ≤ C * τ⁻¹ := by
  have hd : DifferentiableAt ℝ (eigProd A) 0 := by
    have := differentiableAt_prod_cpow (A.charpoly.roots.map fun μ => -I * μ) (by
      intro w hw
      obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hw
      refine mem_slitPlane_of_re_nonneg ?_ ?_
      · simpa [mul_re] using im_nonneg_of_mem_roots hA hIm hμ
      · exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (ne_zero_of_mem_roots hdet hμ))
    have heq : eigProd A = fun t : ℝ => ((A.charpoly.roots.map fun μ => -I * μ).map
        fun w => ((t : ℂ) + w) ^ (-(1 / 2 : ℂ))).prod := by
      funext t; rw [eigProd, Multiset.map_map]; rfl
    rw [heq]; exact this
  obtain ⟨c, hc⟩ := hd.hasDerivAt.isBigO_sub.bound
  obtain ⟨τ₁, hτ₁⟩ := Filter.eventually_atTop.mp (tendsto_inv_atTop_zero.eventually hc)
  refine ⟨c, max τ₁ 1, by positivity, fun τ hτ => ?_⟩
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hτ)
  have h := hτ₁ τ (le_trans (le_max_left _ _) hτ)
  rwa [sub_zero, Real.norm_of_nonneg (inv_nonneg.mpr hτ0.le)] at h

/-! ### The quadratic-phase lemma -/

/-- The weight `e^{|x|²/2}` is smooth. -/
theorem contDiff_gaussWeight :
    ContDiff ℝ ∞ fun x : Fin n → ℝ => cexp ((∑ i, (x i : ℂ) ^ 2) / 2) := by
  refine ContDiff.cexp (ContDiff.div_const (ContDiff.sum fun i _ => ?_) 2)
  exact (ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)).pow 2

/-- `u(x) e^{|x|²/2}`: with this amplitude, `u e^{iτ⟨Ax,x⟩/2}` becomes the Gaussian integrand
`e^{-⟨(1 - iτA)x, x⟩/2}`. -/
noncomputable def gaussWeighted (u : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  u x * cexp ((∑ i, (x i : ℂ) ^ 2) / 2)

/-- `u e^{|x|²/2}` is smooth when `u` is. -/
theorem contDiff_gaussWeighted {u : (Fin n → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gaussWeighted u) :=
  hu.mul contDiff_gaussWeight

/-- `u e^{|x|²/2}` has compact support when `u` has. -/
theorem hasCompactSupport_gaussWeighted {u : (Fin n → ℝ) → ℂ} (hus : HasCompactSupport u) :
    HasCompactSupport (gaussWeighted u) :=
  hus.mul_right (f' := fun x : Fin n → ℝ => cexp ((∑ i, (x i : ℂ) ^ 2) / 2))

/-- `u e^{|x|²/2}` equals `u` at the origin. -/
theorem gaussWeighted_zero (u : (Fin n → ℝ) → ℂ) : gaussWeighted u 0 = u 0 := by
  simp [gaussWeighted]

/-- **Damping.** `∫ u e^{iτ⟨A x, x⟩/2} = ∫ (u e^{|x|²/2}) e^{-⟨(1 - iτA) x, x⟩/2}`. -/
theorem integral_eq_integral_dampMat (A : Matrix (Fin n) (Fin n) ℂ) (u : (Fin n → ℝ) → ℂ) (τ : ℝ) :
    ∫ x, u x * cexp (I * τ * qform A x / 2) =
      ∫ x, gaussWeighted u x * cexp (-qform (dampMat A τ) x / 2) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [gaussWeighted, qform_dampMat, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- For `τ ≥ max τ₁ 1`, a bound `|eigProd A (1/τ) - eigProd A 0| ≤ C₁/τ` gives `|eigProd A (1/τ)| ≤
|eigProd A 0| + C₁`. -/
theorem norm_eigProd_inv_le {A : Matrix (Fin n) (Fin n) ℂ} {C₁ τ₁ τ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ τ ≥ τ₁, ‖eigProd A τ⁻¹ - eigProd A 0‖ ≤ C₁ * τ⁻¹) (hττ₁ : τ₁ ≤ τ) (hτ1 : 1 ≤ τ) :
    ‖eigProd A τ⁻¹‖ ≤ ‖eigProd A 0‖ + C₁ := by
  have h3 : ‖eigProd A τ⁻¹‖ ≤ ‖eigProd A 0‖ + ‖eigProd A τ⁻¹ - eigProd A 0‖ := by
    simpa using norm_add_le (eigProd A 0) (eigProd A τ⁻¹ - eigProd A 0)
  have h2 : C₁ * τ⁻¹ ≤ C₁ := mul_le_of_le_one_right hC₁0 (inv_le_one_of_one_le₀ hτ1)
  linarith [hC₁ τ hττ₁]

/-- `eigProd_inv_sub` with a nonnegative constant. -/
theorem exists_eigProd_inv_sub {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) :
    ∃ C₁ τ₁ : ℝ, 0 ≤ C₁ ∧ 0 < τ₁ ∧ ∀ τ ≥ τ₁, ‖eigProd A τ⁻¹ - eigProd A 0‖ ≤ C₁ * τ⁻¹ := by
  obtain ⟨C₁, τ₁, hτ₁, hC₁⟩ := eigProd_inv_sub hA hIm hdet
  refine ⟨C₁, τ₁, ?_, hτ₁, hC₁⟩
  by_contra hneg
  have := mul_neg_of_neg_of_pos (not_le.mp hneg) (inv_pos.mpr hτ₁)
  linarith [(norm_nonneg _).trans (hC₁ τ₁ le_rfl)]

/-- **Quadratic-phase lemma, leading term, uniform in the amplitude.** Let `A` be complex
symmetric with `det A ≠ 0` and `Im ⟨A x, x⟩ ≥ 0` for real `x`. There are `C` and `τ₀ > 0`,
depending only on `A`, such that for every smooth compactly supported `u` and every `τ ≥ τ₀`,

  `|∫ u e^{iτ⟨A x, x⟩/2} - (2π/τ)^{n/2} invSqrtDet(-iA) u(0)|
    ≤ C (|u(0)| + ∫ |ξ|² |𝓕(u e^{|x|²/2})(ξ)| dξ) τ^{-n/2-1}`.

Source: Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.7,
Lemma 7.7.3 with `k = 1`, where `(det(τA/2πi))^{-1/2} = (2π/τ)^{n/2} (det(-iA))^{-1/2}`. The
error is measured by a Fourier norm of `u e^{|x|²/2}` in place of Hörmander's Sobolev norms. -/
theorem quadratic_phase_uniform {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      ∀ τ ≥ τ₀,
        ‖(∫ x, u x * cexp (I * τ * qform A x / 2)) -
          ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • A) * u 0‖ ≤
          C * (‖u 0‖ + ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) *
            τ ^ (-((n : ℝ) / 2) - 1) := by
  obtain ⟨C₁, τ₁, hC₁0, hτ₁, hC₁⟩ := exists_eigProd_inv_sub hA hIm hdet
  set α : ℝ := (‖eigProd A 0‖ + C₁) * (2 * π ^ 2 * (n * (2 * entrySum A⁻¹))) with hα
  have hα0 : 0 ≤ α := mul_nonneg (by positivity) (mul_nonneg (by positivity)
    (mul_nonneg (Nat.cast_nonneg _) (by linarith [entrySum_nonneg A⁻¹])))
  refine ⟨(2 * π) ^ ((n : ℝ) / 2) * (α + C₁), max τ₁ (max 1 (2 * entrySum A⁻¹)),
    lt_max_of_lt_left hτ₁, fun u hu hus τ hτ => ?_⟩
  have hv := contDiff_gaussWeighted hu
  have hvs := hasCompactSupport_gaussWeighted hus
  have hτ1 : 1 ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
  have hτK : 2 * entrySum A⁻¹ ≤ τ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
  have hττ₁ : τ₁ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ1
  have hposB := re_qform_dampMat_pos hIm hτ0.le
  have hsymB := dampMat_isSymm hA τ
  have hG : ∫ x, cexp (-qform (dampMat A τ) x / 2) = (((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) *
      (((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) * eigProd A τ⁻¹) := by
    rw [integral_gauss_eq_invSqrtDet (dampMat A τ) hsymB hposB, invSqrtDet_dampMat hA hIm hτ0]
  have htgt : (((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (-I • A) * u 0 =
      u 0 * ((((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) *
        (((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) * eigProd A 0)) := by
    rw [← eigProd_zero, Real.div_rpow (by positivity) hτ0.le, Real.rpow_neg hτ0.le,
      div_eq_mul_inv ((2 * π) ^ ((n : ℝ) / 2))]
    push_cast
    ring
  have h1 := norm_integral_mul_gauss_sub_le hsymB hposB hv hvs
    (norm_dotProduct_dampMat_inv_le hA hIm hdet hτ0 hτK)
  rw [gaussWeighted_zero, ← integral_eq_integral_dampMat, hG] at h1
  have hf := hC₁ τ hττ₁
  have hfn := norm_eigProd_inv_le hC₁0 hC₁ hττ₁ hτ1
  have hP : 0 ≤ (2 * π) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have hR : 0 ≤ τ ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg hτ0.le _
  have hnorm : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ = r := fun r hr => by
    rw [Complex.norm_real, Real.norm_of_nonneg hr]
  have hI2 : 0 ≤ ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖ :=
    integral_nonneg fun ξ => by positivity
  have hκ0 : 0 ≤ 2 * π ^ 2 * (n * (2 * entrySum A⁻¹ / τ)) *
      ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖ :=
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by linarith [entrySum_nonneg A⁻¹]) hτ0.le))) hI2
  have hX : 0 ≤ (2 * π) ^ ((n : ℝ) / 2) * τ ^ (-((n : ℝ) / 2)) * τ⁻¹ :=
    mul_nonneg (mul_nonneg hP hR) (inv_nonneg.mpr hτ0.le)
  have hsplit : α * (∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) + C₁ * ‖u 0‖ ≤
      (α + C₁) * (‖u 0‖ + ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) := by
    have := mul_nonneg hα0 (norm_nonneg (u 0))
    have := mul_nonneg hC₁0 hI2
    nlinarith
  rw [htgt, Real.rpow_sub_one hτ0.ne', div_eq_mul_inv (τ ^ (-((n : ℝ) / 2))) τ]
  calc _ = ‖((∫ x, u x * cexp (I * τ * qform A x / 2)) - u 0 *
          ((((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * (((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) *
            eigProd A τ⁻¹))) +
        u 0 * ((((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ)) *
          (eigProd A τ⁻¹ - eigProd A 0)‖ := by congr 1; ring1
    _ ≤ ‖(∫ x, u x * cexp (I * τ * qform A x / 2)) - u 0 *
          ((((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * (((τ ^ (-((n : ℝ) / 2)) : ℝ) : ℂ) *
            eigProd A τ⁻¹))‖ +
        ‖u 0‖ * ((2 * π) ^ ((n : ℝ) / 2) * τ ^ (-((n : ℝ) / 2))) *
          ‖eigProd A τ⁻¹ - eigProd A 0‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul, hnorm _ hP, hnorm _ hR]
    _ ≤ ((2 * π) ^ ((n : ℝ) / 2) * (τ ^ (-((n : ℝ) / 2)) * (‖eigProd A 0‖ + C₁))) *
          (2 * π ^ 2 * (n * (2 * entrySum A⁻¹ / τ)) *
            ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) +
        ‖u 0‖ * ((2 * π) ^ ((n : ℝ) / 2) * τ ^ (-((n : ℝ) / 2))) * (C₁ * τ⁻¹) := by
        refine add_le_add (h1.trans ?_)
          (mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) (mul_nonneg hP hR)))
        rw [norm_mul, norm_mul, hnorm _ hP, hnorm _ hR]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfn hR) hP) hκ0
    _ = ((2 * π) ^ ((n : ℝ) / 2) * τ ^ (-((n : ℝ) / 2)) * τ⁻¹) *
          (α * (∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) + C₁ * ‖u 0‖) := by
        rw [hα]; ring1
    _ ≤ ((2 * π) ^ ((n : ℝ) / 2) * τ ^ (-((n : ℝ) / 2)) * τ⁻¹) *
          ((α + C₁) * (‖u 0‖ + ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖)) :=
        mul_le_mul_of_nonneg_left hsplit hX
    _ = _ := by ring1

/-- **Quadratic-phase lemma, leading term.** Let `A` be complex symmetric with `det A ≠ 0` and
`Im ⟨A x, x⟩ ≥ 0` for real `x`, and let `u` be smooth with compact support. Then

  `∫ u(x) e^{iτ⟨A x, x⟩/2} dx = (2π/τ)^{n/2} invSqrtDet(-iA) u(0) + O(τ^{-n/2-1})`

as `τ → ∞`. Source: Hörmander, *The Analysis of Linear Partial Differential Operators I*,
§7.7, Lemma 7.7.3 with `k = 1`; the branch of `(det(-iA))^{-1/2}` is the product of principal
roots over the eigenvalues of `-iA` (`invSqrtDet`). -/
theorem quadratic_phase {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, u x * cexp (I * τ * qform A x / 2)) -
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • A) * u 0‖ ≤
        C * τ ^ (-((n : ℝ) / 2) - 1) := by
  obtain ⟨C, τ₀, hτ₀, h⟩ := quadratic_phase_uniform hA hIm hdet
  exact ⟨C * (‖u 0‖ + ∫ ξ, ‖ξ‖ ^ 2 * ‖𝓕 (toEuc (gaussWeighted u)) ξ‖), τ₀, hτ₀, h u hu hus⟩

/-- **Quadratic-phase lemma, base bound, uniform in the amplitude.** Under the hypotheses of
`quadratic_phase_uniform`, there are `C` and `τ₀ > 0`, depending only on `A`, with
`|∫ u e^{iτ⟨A x, x⟩/2}| ≤ C (∫ |𝓕(u e^{|x|²/2})|) τ^{-n/2}` for every smooth compactly supported
`u` and every `τ ≥ τ₀`. Source: Hörmander, *ALPDO I*, §7.7, Lemma 7.7.3, the estimate with
`k = 0`. -/
theorem quadratic_phase_base_uniform {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      ∀ τ ≥ τ₀,
        ‖∫ x, u x * cexp (I * τ * qform A x / 2)‖ ≤
          C * (∫ ξ, ‖𝓕 (toEuc (gaussWeighted u)) ξ‖) * τ ^ (-((n : ℝ) / 2)) := by
  obtain ⟨C₁, τ₁, hC₁0, hτ₁, hC₁⟩ := exists_eigProd_inv_sub hA hIm hdet
  refine ⟨(2 * π) ^ ((n : ℝ) / 2) * (‖eigProd A 0‖ + C₁), max τ₁ 1, lt_max_of_lt_left hτ₁,
    fun u hu hus τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ := le_trans (le_max_right _ _) hτ
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ1
  have h1 := norm_integral_mul_gauss_le (dampMat_isSymm hA τ) (re_qform_dampMat_pos hIm hτ0.le)
    (contDiff_gaussWeighted hu) (hasCompactSupport_gaussWeighted hus)
  rw [← integral_eq_integral_dampMat,
    integral_gauss_eq_invSqrtDet (dampMat A τ) (dampMat_isSymm hA τ)
      (re_qform_dampMat_pos hIm hτ0.le), invSqrtDet_dampMat hA hIm hτ0] at h1
  have hfn := norm_eigProd_inv_le hC₁0 hC₁ (le_trans (le_max_left _ _) hτ) hτ1
  have hP : 0 ≤ (2 * π) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have hR : 0 ≤ τ ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg hτ0.le _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hP,
    Real.norm_of_nonneg hR] at h1
  refine h1.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfn hR) hP)
    (integral_nonneg fun ξ => norm_nonneg _)) (by ring1))

/-- **Quadratic-phase lemma, base bound.** Under the hypotheses of `quadratic_phase`,
`∫ u e^{iτ⟨A x, x⟩/2} = O(τ^{-n/2})`. Source: Hörmander, *ALPDO I*, §7.7, Lemma 7.7.3, the
estimate with `k = 0`. -/
theorem quadratic_phase_base {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) {u : (Fin n → ℝ) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖∫ x, u x * cexp (I * τ * qform A x / 2)‖ ≤ C * τ ^ (-((n : ℝ) / 2)) := by
  obtain ⟨C, τ₀, hτ₀, h⟩ := quadratic_phase_base_uniform hA hIm hdet
  exact ⟨C * ∫ ξ, ‖𝓕 (toEuc (gaussWeighted u)) ξ‖, τ₀, hτ₀, h u hu hus⟩

end Lightlike.Oscillatory
