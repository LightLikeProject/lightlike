import Lightlike.OperatorAlgebras.CCRJoint
import Lightlike.OperatorAlgebras.GaussKernel
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Gaussian average of the Weyl unitaries (von Neumann's projection)

For a representation `R` of the Weyl relations of a finite-dimensional `h` on a Hilbert space `K`,
`gaussAvg R y = ∫ e^{-‖z‖²/4} W z y dz` (Lebesgue measure of `h` as a real inner product space). After normalization by
`(4π)^{dim_ℂ h}` it is von Neumann's projection (Faulhuber, arXiv:2204.01596, §7.3.1, Lemma 7.34 and eq. (7.14)).
-/

open MeasureTheory GaussianFourier
open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The Gaussian weight `e^{-‖z‖²/4}`. -/
noncomputable def gaussW (z : h) : ℝ := Real.exp (-(1 / 4) * ‖z‖ ^ 2)

lemma gaussW_pos (z : h) : 0 < gaussW z := Real.exp_pos _

lemma integrable_gaussW : Integrable (gaussW (h := h)) := by
  have := integrable_cexp_neg_mul_sq_norm_add (V := h) (b := (1 / 4 : ℂ)) (by norm_num) 0 0
  refine (this.norm.congr ?_)
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [zero_mul, add_zero, Complex.norm_exp, gaussW]
  congr 1
  simp [← Complex.ofReal_pow]

lemma integrable_gaussW_smul_W (R : CCRRep h K) (y : K) :
    Integrable fun z : h => gaussW z • R.W z y := by
  refine Integrable.mono' (integrable_gaussW.mul_const ‖y‖) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).smul
      (R.continuous_W y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (gaussW_pos z).le]

/-- **The Gaussian average** `∫ e^{-‖z‖²/4} W z y dz`. -/
noncomputable def gaussAvg (R : CCRRep h K) (y : K) : K := ∫ z : h, gaussW z • R.W z y

lemma gaussAvg_add (R : CCRRep h K) (y y' : K) : gaussAvg R (y + y') = gaussAvg R y + gaussAvg R y' := by
  simp only [gaussAvg, map_add, smul_add]
  exact integral_add (integrable_gaussW_smul_W R y) (integrable_gaussW_smul_W R y')

lemma gaussAvg_smul (R : CCRRep h K) (c : ℂ) (y : K) : gaussAvg R (c • y) = c • gaussAvg R y := by
  simp only [gaussAvg, map_smul, smul_comm (gaussW _) c]
  exact integral_smul c _

lemma norm_gaussAvg_le (R : CCRRep h K) (y : K) : ‖gaussAvg R y‖ ≤ (∫ z : h, gaussW z) * ‖y‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (integrable_gaussW.mul_const _) (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (gaussW_pos z).le]

/-- The Gaussian average as a bounded operator. -/
noncomputable def gaussAvgCLM (R : CCRRep h K) : K →L[ℂ] K :=
  LinearMap.mkContinuous ⟨⟨gaussAvg R, gaussAvg_add R⟩, gaussAvg_smul R⟩ (∫ z : h, gaussW z) (norm_gaussAvg_le R)

lemma gaussAvgCLM_apply (R : CCRRep h K) (y : K) : gaussAvgCLM R y = gaussAvg R y := rfl

lemma gaussW_neg (z : h) : gaussW (-z) = gaussW z := by simp [gaussW]

/-- `⟪x, P y⟫ = ∫ e^{-‖z‖²/4} ⟪x, W z y⟫ dz`. -/
lemma inner_gaussAvg (R : CCRRep h K) (x y : K) :
    ⟪x, gaussAvg R y⟫_ℂ = ∫ z : h, (gaussW z : ℂ) * ⟪x, R.W z y⟫_ℂ := by
  rw [gaussAvg, ← integral_inner (integrable_gaussW_smul_W R y)]
  simp_rw [← Complex.coe_smul, inner_smul_right]

/-- **The Gaussian average is self-adjoint**: `⟪P x, y⟫ = ⟪x, P y⟫` (`W z* = W (-z)` and `z ↦ -z` preserves the measure). -/
lemma inner_gaussAvg_left (R : CCRRep h K) (x y : K) : ⟪gaussAvg R x, y⟫_ℂ = ⟪x, gaussAvg R y⟫_ℂ := by
  rw [← inner_conj_symm, inner_gaussAvg, inner_gaussAvg, ← integral_conj]
  rw [← integral_neg_eq_self (fun z : h => (gaussW z : ℂ) * ⟪x, R.W z y⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm, gaussW_neg]
  congr 1
  rw [show ⟪x, R.W (-z) y⟫_ℂ = ⟪R.W z x, R.W z (R.W (-z) y)⟫_ℂ from (LinearIsometryEquiv.inner_map_map _ _ _).symm,
    R.W_W_neg]

open MeasureTheory GaussianFourier
open scoped InnerProductSpace

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma gaussW_eq_cexp (z : h) : (gaussW z : ℂ) = Complex.exp (-(1 / 4 : ℂ) * ‖z‖ ^ 2) := by
  rw [gaussW, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The phase of a triple product: `W z (W f (W w y)) = e^{-i(σ(f, w) + σ(z, f + w))/2} W (z + f + w) y`. -/
lemma CCRRep.W_W_W (R : CCRRep h K) (z f w : h) (y : K) :
    R.W z (R.W f (R.W w y)) =
      Complex.exp (-(Complex.I * ((symp h f w + symp h z (f + w)) / 2 : ℝ))) • R.W (z + f + w) y := by
  rw [R.weyl f w, map_smul, R.weyl, smul_smul, ← Complex.exp_add, add_assoc]
  congr 2
  push_cast
  ring

/-- `⟪x, W f (P y)⟫ = ∫ e^{-‖w‖²/4} ⟪x, W f (W w y)⟫ dw`. -/
lemma inner_W_gaussAvg (R : CCRRep h K) (f : h) (x y : K) :
    ⟪x, R.W f (gaussAvg R y)⟫_ℂ = ∫ w : h, (gaussW w : ℂ) * ⟪x, R.W f (R.W w y)⟫_ℂ := by
  rw [show ⟪x, R.W f (gaussAvg R y)⟫_ℂ = ⟪R.W (-f) x, gaussAvg R y⟫_ℂ by
    rw [← LinearIsometryEquiv.inner_map_map (R.W (-f)), R.W_neg_W], inner_gaussAvg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [← LinearIsometryEquiv.inner_map_map (R.W f) (R.W (-f) x), R.W_W_neg]

/-- `⟪x, T (P y)⟫ = ∫ e^{-‖w‖²/4} ⟪x, T (W w y)⟫ dw` for a bounded `T`. -/
lemma inner_map_gaussAvg (R : CCRRep h K) (T : K →L[ℂ] K) (x y : K) :
    ⟪x, T (gaussAvg R y)⟫_ℂ = ∫ w : h, (gaussW w : ℂ) * ⟪x, T (R.W w y)⟫_ℂ := by
  have hi := integrable_gaussW_smul_W R y
  rw [gaussAvg, ← T.integral_comp_comm hi, ← integral_inner (T.integrable_comp hi)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [← Complex.coe_smul, map_smul, inner_smul_right]

lemma continuous_gaussW : Continuous (gaussW : h → ℝ) := by
  unfold gaussW; fun_prop

/-- `⟪x, W z (W f (P y))⟫ = ∫ e^{-‖w‖²/4} ⟪x, W z (W f (W w y))⟫ dw`. -/
lemma inner_WW_gaussAvg (R : CCRRep h K) (z f : h) (x y : K) :
    ⟪x, R.W z (R.W f (gaussAvg R y))⟫_ℂ = ∫ w : h, (gaussW w : ℂ) * ⟪x, R.W z (R.W f (R.W w y))⟫_ℂ := by
  rw [show ⟪x, R.W z (R.W f (gaussAvg R y))⟫_ℂ = ⟪R.W (-f) (R.W (-z) x), gaussAvg R y⟫_ℂ by
    rw [← LinearIsometryEquiv.inner_map_map (R.W (-z)), R.W_neg_W, ← LinearIsometryEquiv.inner_map_map (R.W (-f)),
      R.W_neg_W], inner_gaussAvg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [← LinearIsometryEquiv.inner_map_map (R.W f), R.W_W_neg, ← LinearIsometryEquiv.inner_map_map (R.W z), R.W_W_neg]

/-- The domination `e^{-‖z‖²/4} e^{-‖u - (z + f)‖²/4}` is integrable on `h × h`. -/
lemma integrable_gauss_shear (f : h) :
    Integrable (fun p : h × h => gaussW p.1 * gaussW (p.2 - (p.1 + f))) (volume.prod volume) := by
  have h1 : Integrable (fun p : h × h => gaussW p.1 * gaussW (p.2 - f)) (volume.prod volume) :=
    integrable_gaussW.mul_prod (integrable_gaussW.comp_sub_right f)
  have h2 := (measurePreserving_prod_sub (volume : Measure h) (volume : Measure h)).integrable_comp
    h1.aestronglyMeasurable
  refine (h2.mpr h1).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply]
  congr 1
  abel_nf

/-- The phase after the substitution `w = u - (z + f)`. -/
lemma phase_shear (z f u : h) :
    symp h f (u - (z + f)) + symp h z (f + (u - (z + f))) = symp h f u - (symp h f z - symp h z u) := by
  rw [show f + (u - (z + f)) = u - z by abel, symp_sub_right, symp_sub_right, symp_add_right, symp_self, symp_self]
  ring

/-- **von Neumann's identity** `P W f P = (2π)^d e^{-‖f‖²/4} P` (Faulhuber, eq. (7.14)). -/
theorem gaussAvg_W_gaussAvg (R : CCRRep h K) (f : h) (y : K) :
    gaussAvg R (R.W f (gaussAvg R y)) = (vnConst h * gaussW f) • gaussAvg R y := by
  refine ext_inner_left ℂ fun x => ?_
  set F : h → h → ℂ := fun z u => (gaussW z : ℂ) * (gaussW (u - (z + f)) : ℂ) *
    Complex.exp (-(Complex.I * ((symp h f (u - (z + f)) + symp h z (f + (u - (z + f)))) / 2 : ℝ))) *
      ⟪x, R.W u y⟫_ℂ with hF
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono' ((integrable_gauss_shear f).mul_const (‖x‖ * ‖y‖)) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF, Function.uncurry_def]
      have hW : Continuous fun p : h × h => R.W p.2 y := (R.continuous_W y).comp continuous_snd
      have hs : Continuous fun p : h × h => symp h f (p.2 - (p.1 + f)) + symp h p.1 (f + (p.2 - (p.1 + f))) :=
        (continuous_symp.comp (continuous_const.prodMk (continuous_snd.sub (continuous_fst.add continuous_const)))).add
          (continuous_symp.comp (continuous_fst.prodMk (continuous_const.add
            (continuous_snd.sub (continuous_fst.add continuous_const)))))
      refine ((((Complex.continuous_ofReal.comp (continuous_gaussW.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp (continuous_gaussW.comp (continuous_snd.sub
          (continuous_fst.add continuous_const))))).mul ?_).mul (continuous_const.inner hW))
      exact Complex.continuous_exp.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hs.div_const 2))).neg)
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussW_pos _).le]
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * (((symp h f (p.2 - (p.1 + f)) + symp h p.1 (f + (p.2 - (p.1 + f)))) / 2 : ℝ) : ℂ))).re
          = 0 := by simp
      have hin : ‖⟪x, R.W p.2 y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ :=
        (norm_inner_le_norm (𝕜 := ℂ) x (R.W p.2 y)).trans (le_of_eq (by rw [LinearIsometryEquiv.norm_map]))
      rw [hre, Real.exp_zero, mul_one]
      exact mul_le_mul_of_nonneg_left hin (mul_nonneg (gaussW_pos _).le (gaussW_pos _).le)
  calc ⟪x, gaussAvg R (R.W f (gaussAvg R y))⟫_ℂ
      = ∫ z : h, (gaussW z : ℂ) * ⟪x, R.W z (R.W f (gaussAvg R y))⟫_ℂ := inner_gaussAvg R x _
    _ = ∫ z : h, ∫ u : h, F z u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [inner_WW_gaussAvg, ← integral_const_mul, ← integral_sub_right_eq_self _ (z + f)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hF]
        rw [R.W_W_W, inner_smul_right, show z + f + (u - (z + f)) = u by abel]
        ring
    _ = ∫ u : h, ∫ z : h, F z u := integral_integral_swap hFi
    _ = ∫ u : h, (vnConst h * gaussW f : ℂ) * ((gaussW u : ℂ) * ⟪x, R.W u y⟫_ℂ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        beta_reduce
        have hpt : ∀ z, F z u = (Complex.exp (-(Complex.I * (symp h f u / 2 : ℝ))) * ⟪x, R.W u y⟫_ℂ) *
            (Complex.exp (-(1 / 4 : ℂ) * ‖z‖ ^ 2) * Complex.exp (-(1 / 4 : ℂ) * ‖u - f - z‖ ^ 2) *
              Complex.exp (Complex.I * ((symp h f z - symp h z u) / 2 : ℝ))) := by
          intro z
          simp only [hF, gaussW_eq_cexp, phase_shear, show u - (z + f) = u - f - z by abel]
          have he : -(Complex.I * (((symp h f u - (symp h f z - symp h z u)) / 2 : ℝ) : ℂ)) =
              -(Complex.I * ((symp h f u / 2 : ℝ) : ℂ)) + Complex.I * (((symp h f z - symp h z u) / 2 : ℝ) : ℂ) := by
            push_cast; ring
          rw [he, Complex.exp_add]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, integral_gauss_kernel,
          gaussW_eq_cexp, gaussW_eq_cexp]
        have h1 : Complex.exp (-(Complex.I * (symp h f u / 2 : ℝ))) * Complex.exp (Complex.I * (symp h f u / 2 : ℝ)) = 1 := by
          rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
        linear_combination (vnConst h * Complex.exp (-(1 / 4 : ℂ) * ‖u‖ ^ 2) * Complex.exp (-(1 / 4 : ℂ) * ‖f‖ ^ 2) *
          ⟪x, R.W u y⟫_ℂ) * h1
    _ = ⟪x, (vnConst h * gaussW f) • gaussAvg R y⟫_ℂ := by
        rw [integral_const_mul, inner_smul_right, inner_gaussAvg]

open MeasureTheory FourierTransform GaussianFourier
open scoped InnerProductSpace Real

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `W (-f) W z W f = e^{iσ(f, z)} W z`. -/
lemma CCRRep.W_conj (R : CCRRep h K) (f z : h) (ψ : K) :
    R.W (-f) (R.W z (R.W f ψ)) = Complex.exp (Complex.I * (symp h f z : ℝ)) • R.W z ψ := by
  rw [R.weyl z f, map_smul, R.weyl, smul_smul, ← Complex.exp_add, show -f + (z + f) = z by abel]
  congr 2
  rw [symp_add_right, symp_neg_self, symp_antisymm z f]
  have : symp h (-f) z = -symp h f z := by simp [symp, inner_neg_left]
  rw [this]
  push_cast
  ring

lemma inner_conj_gaussAvg (R : CCRRep h K) (f : h) (x : K) :
    ⟪R.W f x, gaussAvg R (R.W f x)⟫_ℂ =
      ∫ z : h, Complex.exp (Complex.I * (symp h f z : ℝ)) * ((gaussW z : ℂ) * ⟪x, R.W z x⟫_ℂ) := by
  rw [inner_gaussAvg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← LinearIsometryEquiv.inner_map_map (R.W (-f)), R.W_neg_W, R.W_conj, inner_smul_right]
  ring

/-- **The Gaussian average is nonzero** on a nonzero space (Faulhuber, Theorem 7.31(ii), by Fourier inversion). -/
theorem exists_gaussAvg_ne_zero [Nontrivial K] (R : CCRRep h K) : ∃ y : K, gaussAvg R y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx⟩ := exists_ne (0 : K)
  set φ : h → ℂ := fun z => (gaussW z : ℂ) * ⟪x, R.W z x⟫_ℂ with hφ
  have hφc : Continuous φ :=
    (Complex.continuous_ofReal.comp continuous_gaussW).mul (continuous_const.inner (R.continuous_W x))
  have hφi : Integrable φ := by
    refine Integrable.mono' (integrable_gaussW.mul_const (‖x‖ * ‖x‖)) hφc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [hφ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussW_pos _).le]
    gcongr
    all_goals first
      | exact (gaussW_pos _).le
      | (refine (norm_inner_le_norm (𝕜 := ℂ) x (R.W z x)).trans (le_of_eq ?_)
         rw [LinearIsometryEquiv.norm_map])
  have hF : 𝓕 φ = 0 := by
    funext w
    set f : h := ((2 * π : ℝ) : ℂ) • (Complex.I • w) with hf
    have h0 := inner_conj_gaussAvg R f x
    rw [hcon, inner_zero_right] at h0
    rw [Real.fourier_eq', Pi.zero_apply]
    refine Eq.trans ?_ h0.symm
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, hφ]
    congr 1
    congr 1
    have : Complex.I * ((2 * π : ℝ) : ℂ) * Complex.I = ((-(2 * π) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [symp_eq_real_inner, hf, smul_smul, smul_smul, this, Complex.coe_smul,
      real_inner_smul_left, real_inner_comm]
    push_cast
    ring
  have hinv := hφc.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  have h0 := congrFun hinv 0
  rw [hF, Real.fourierInv_eq] at h0
  simp only [Pi.zero_apply, smul_zero, integral_zero, hφ, gaussW, norm_zero] at h0
  simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, Real.exp_zero, Complex.ofReal_one,
    one_mul] at h0
  rw [R.W_zero_apply] at h0
  exact hx (inner_self_eq_zero.mp h0.symm)

end Lightlike.OperatorAlgebras
