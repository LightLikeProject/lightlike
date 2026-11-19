import Lightlike.Asymptotics.Tauberian.Box
import Mathlib.Analysis.Convolution

/-!
# The Fourier transform of a convolution

`∫ (f ⋆ h)(t) e^{-i t x} dt = (∫ f e^{-i t x}) (∫ h e^{-i t x})` for integrable `f`, `h`.
-/

open MeasureTheory Set Complex
open scoped Convolution

noncomputable section

namespace Lightlike.Tauberian

/-- The character `t ↦ e^{-i t x}`. -/
def char (x t : ℝ) : ℂ := Complex.exp (-(t * x * Complex.I))

lemma norm_char (x t : ℝ) : ‖char x t‖ = 1 := by
  unfold char; rw [Complex.norm_exp]; simp

lemma char_add (x s t : ℝ) : char x (s + t) = char x s * char x t := by
  unfold char; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma continuous_char (x : ℝ) : Continuous (char x) := by
  unfold char; fun_prop

lemma integrable_mul_char {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun t => f t * char x t) := by
  refine hf.mul_bdd (continuous_char x).aestronglyMeasurable (c := 1) ?_
  exact Filter.Eventually.of_forall fun t => (norm_char x t).le

/-- **Fourier transform of a convolution.** -/
theorem integral_convolution_char {f h : ℝ → ℂ} (hf : Integrable f) (hh : Integrable h) (x : ℝ) :
    ∫ t, (f ⋆[ContinuousLinearMap.mul ℂ ℂ] h) t * char x t =
      (∫ t, f t * char x t) * ∫ t, h t * char x t := by
  have h1 := integral_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
    (μ := (volume : Measure ℝ)) (ν := volume) (integrable_mul_char hf x) (integrable_mul_char hh x)
  simp only [ContinuousLinearMap.mul_apply'] at h1
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have : char x t = char x s * char x (t - s) := by
    rw [← char_add]; congr 1; ring
  simp only [this]
  ring

/-- The real box `1_{[-b, b]}`. -/
def boxR (b t : ℝ) : ℝ := (Icc (-b) b).indicator (fun _ => (1 : ℝ)) t

lemma box_eq (b t : ℝ) : box b t = (boxR b t : ℂ) := by
  unfold box boxR
  by_cases h : t ∈ Icc (-b) b <;> simp [h]

lemma integrable_boxR (b : ℝ) : Integrable (boxR b) := by
  unfold boxR
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

lemma convolution_ofReal {f h : ℝ → ℝ} (t : ℝ) :
    (((f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) t : ℝ) : ℂ) =
      ((fun s => (f s : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun s => (h s : ℂ))) t := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal]
  simp

/-- The four-fold convolution of the box. -/
def kernelR (b : ℝ) : ℝ → ℝ :=
  ((boxR b) ⋆[ContinuousLinearMap.mul ℝ ℝ] (boxR b)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
    ((boxR b) ⋆[ContinuousLinearMap.mul ℝ ℝ] (boxR b))

lemma boxR_nonneg (b t : ℝ) : 0 ≤ boxR b t := by
  unfold boxR; exact Set.indicator_nonneg (fun _ _ => zero_le_one) t

lemma convolution_nonneg {f h : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t) (hh : ∀ t, 0 ≤ h t) (t : ℝ) :
    0 ≤ (f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) t := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  exact integral_nonneg fun s => mul_nonneg (hf s) (hh _)

lemma integrable_conv {f h : ℝ → ℝ} (hf : Integrable f) (hh : Integrable h) :
    Integrable (f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hh

lemma support_boxR (b : ℝ) : Function.support (boxR b) ⊆ Icc (-b) b := by
  intro t ht
  by_contra h
  exact ht (by unfold boxR; rw [Set.indicator_of_notMem h])

lemma support_conv_box {f h : ℝ → ℝ} {a c : ℝ} (hf : Function.support f ⊆ Icc (-a) a)
    (hh : Function.support h ⊆ Icc (-c) c) :
    Function.support (f ⋆[ContinuousLinearMap.mul ℝ ℝ] h) ⊆ Icc (-(a + c)) (a + c) := by
  intro t ht
  obtain ⟨u, hu, v, hv, rfl⟩ := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) ht
  have h1 := hf hu
  have h2 := hh hv
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The kernel with Fourier transform `(2b sinc(bx))⁴`.** The four-fold convolution of a box is
integrable, nonnegative, supported in `[-4b, 4b]`, and its Fourier transform is `(2 b sinc (b x))⁴`. -/
theorem exists_fourier_kernel {b : ℝ} (hb : 0 < b) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧ (∀ t, 4 * b < |t| → g t = 0) ∧
      ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ) := by
  have hbox : Integrable (boxR b) := integrable_boxR b
  have h2 : Integrable ((boxR b) ⋆[ContinuousLinearMap.mul ℝ ℝ] (boxR b)) := integrable_conv hbox hbox
  have h4 : Integrable (kernelR b) := integrable_conv h2 h2
  refine ⟨kernelR b, h4, ?_, ?_, ?_⟩
  · intro t
    exact convolution_nonneg (convolution_nonneg (boxR_nonneg b) (boxR_nonneg b))
      (convolution_nonneg (boxR_nonneg b) (boxR_nonneg b)) t
  · intro t ht
    have hs2 := support_conv_box (support_boxR b) (support_boxR b)
    have hs4 := support_conv_box hs2 hs2
    by_contra h0
    have := hs4 (show t ∈ Function.support (kernelR b) from h0)
    have hab : |t| ≤ b + b + (b + b) := abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
    linarith
  · intro x
    have hc : ∀ t, ((kernelR b t : ℝ) : ℂ) =
        ((fun s => (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) s : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          (fun s => (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) s : ℝ) : ℂ))) t := by
      intro t; exact convolution_ofReal t
    have hc2 : ∀ t, (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) t : ℝ) : ℂ) =
        ((fun s => (boxR b s : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun s => (boxR b s : ℂ))) t :=
      fun t => convolution_ofReal t
    have hB : Integrable (fun s => (boxR b s : ℂ)) := hbox.ofReal
    have hCfun : (fun s => (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) s : ℝ) : ℂ)) =
        ((fun s => (boxR b s : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun s => (boxR b s : ℂ))) :=
      funext hc2
    have hC : Integrable (fun s => (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) s : ℝ) : ℂ)) :=
      h2.ofReal
    have hBx : ∫ t, (boxR b t : ℂ) * char x t = 2 * b * (Real.sinc (b * x) : ℂ) := by
      have := integral_box_exp hb x
      simp only [box_eq] at this
      exact this
    have hCx : ∫ t, (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ] boxR b) t : ℝ) : ℂ) * char x t =
        (2 * b * (Real.sinc (b * x) : ℂ)) ^ 2 := by
      have := integral_convolution_char hB hB x
      simp_rw [← hc2] at this
      rw [this, hBx]; ring
    have hK : ∫ t, ((kernelR b t : ℝ) : ℂ) * char x t = ((∫ t, (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ]
        boxR b) t : ℝ) : ℂ) * char x t)) * ∫ t, (((boxR b ⋆[ContinuousLinearMap.mul ℝ ℝ]
        boxR b) t : ℝ) : ℂ) * char x t := by
      simp_rw [hc]
      exact integral_convolution_char hC hC x
    rw [hK, hCx]
    push_cast
    ring

end Lightlike.Tauberian
