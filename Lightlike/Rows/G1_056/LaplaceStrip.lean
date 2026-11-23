import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A Fourier-Laplace transform on the strip `-1 ≤ Im z ≤ 0` (G1-056)

Step toward the Bisognano-Wichmann theorem in the rapidity picture (`Lightlike/Rows/G1_056/`): the
correlation function `⟨ξ, Δ^{it} η⟩` of two vectors of the standard subspace is the transform
`laplace g z = ∫ g(x) e^{-2πi z x} dx` of `g = conj ξ · η`, where `Δ^{it}` is multiplication by
`e^{-2πitx}`. If `g` and `e^{-2πx} g` are integrable then `laplace g` is continuous on the closed strip
`-1 ≤ Im z ≤ 0` (`continuousOn_laplace`) and holomorphic in its interior (`differentiableOn_laplace`).

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory Complex Set Metric Filter
open scoped Real

noncomputable section

namespace Lightlike.BisognanoWichmann

/-- The kernel `e^{-2πi z x}` of the transform, as a function of `z`. -/
def kern (x : ℝ) (z : ℂ) : ℂ := cexp (-(2 * π * I * x) * z)

/-- **The Fourier-Laplace transform** `z ↦ ∫ g(x) e^{-2πi z x} dx`. -/
def laplace (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x, g x * kern x z

lemma norm_kern (x : ℝ) (z : ℂ) : ‖kern x z‖ = Real.exp (2 * π * x * z.im) := by
  rw [kern, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma continuous_kern (x : ℝ) : Continuous (kern x) := by
  unfold kern; fun_prop

lemma continuous_kern_x (z : ℂ) : Continuous (fun x : ℝ => kern x z) := by
  unfold kern; fun_prop

/-- On the closed strip the kernel is bounded by `1 + e^{-2πx}`. -/
lemma norm_kern_le {z : ℂ} (h1 : -1 ≤ z.im) (h2 : z.im ≤ 0) (x : ℝ) :
    ‖kern x z‖ ≤ 1 + Real.exp (-(2 * π * x)) := by
  rw [norm_kern]
  have hπ := Real.pi_pos
  rcases le_total 0 x with hx | hx
  · have : Real.exp (2 * π * x * z.im) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg hπ.le hx]
    linarith [Real.exp_pos (-(2 * π * x))]
  · have : Real.exp (2 * π * x * z.im) ≤ Real.exp (-(2 * π * x)) := by
      apply Real.exp_le_exp.mpr; nlinarith [mul_nonpos_of_nonneg_of_nonpos hπ.le hx]
    linarith

lemma mul_exp_neg_le_one {y : ℝ} (_hy : 0 ≤ y) : y * Real.exp (-y) ≤ 1 := by
  have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  calc y * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The kernel's `z`-derivative, bounded uniformly on a compact sub-strip. -/
lemma deriv_kern_bound {ε : ℝ} (hε : 0 < ε) {z : ℂ} (h1 : -1 + ε ≤ z.im) (h2 : z.im ≤ -ε) (x : ℝ) :
    ‖kern x z * (-(2 * π * I * x))‖ ≤ (1 / ε) * (1 + Real.exp (-(2 * π * x))) := by
  have hπ := Real.pi_pos
  have hn : ‖-(2 * (π : ℂ) * I * x)‖ = 2 * π * |x| := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul]
    simp [abs_of_pos hπ]
  rw [norm_mul, norm_kern, hn]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have h3 : Real.exp (2 * π * x * z.im) ≤ Real.exp (-(2 * π * ε * x)) := by
      apply Real.exp_le_exp.mpr; nlinarith [mul_nonneg hπ.le hx]
    have h4 := mul_exp_neg_le_one (y := 2 * π * ε * x) (by positivity)
    have h5 : Real.exp (2 * π * x * z.im) * (2 * π * x) ≤ 1 / ε := by
      calc Real.exp (2 * π * x * z.im) * (2 * π * x)
          ≤ Real.exp (-(2 * π * ε * x)) * (2 * π * x) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (1 / ε) * (2 * π * ε * x * Real.exp (-(2 * π * ε * x))) := by field_simp
        _ ≤ (1 / ε) * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 1 / ε := by ring
    have h6 : 0 ≤ (1 / ε) * Real.exp (-(2 * π * x)) := by positivity
    nlinarith
  · rw [abs_of_nonpos hx]
    have h3 : Real.exp (2 * π * x * z.im) ≤ Real.exp (-(2 * π * x)) * Real.exp (-(2 * π * ε * (-x))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hπ.le hx]
    have h4 := mul_exp_neg_le_one (y := 2 * π * ε * (-x))
      (by have : 0 ≤ 2 * π * ε := by positivity
          nlinarith)
    have h5 : Real.exp (2 * π * x * z.im) * (2 * π * -x) ≤ (1 / ε) * Real.exp (-(2 * π * x)) := by
      calc Real.exp (2 * π * x * z.im) * (2 * π * -x)
          ≤ (Real.exp (-(2 * π * x)) * Real.exp (-(2 * π * ε * (-x)))) * (2 * π * -x) :=
            mul_le_mul_of_nonneg_right h3 (by nlinarith)
        _ = (1 / ε) * Real.exp (-(2 * π * x)) *
              (2 * π * ε * (-x) * Real.exp (-(2 * π * ε * (-x)))) := by field_simp
        _ ≤ (1 / ε) * Real.exp (-(2 * π * x)) * 1 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (1 / ε) * Real.exp (-(2 * π * x)) := by ring
    have h6 : 0 ≤ 1 / ε := by positivity
    nlinarith

variable {g : ℝ → ℂ}

/-- The integrable majorant `‖g‖ + e^{-2πx} ‖g‖`. -/
lemma integrable_bound (hg : Integrable g) (hg' : Integrable fun x => Real.exp (-(2 * π * x)) • g x) :
    Integrable fun x => (1 + Real.exp (-(2 * π * x))) * ‖g x‖ := by
  have := hg.norm.add hg'.norm
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  ring

/-- **The transform is continuous on the closed strip** `-1 ≤ Im z ≤ 0`. -/
theorem continuousOn_laplace (hg : Integrable g)
    (hg' : Integrable fun x => Real.exp (-(2 * π * x)) • g x) :
    ContinuousOn (laplace g) {z : ℂ | -1 ≤ z.im ∧ z.im ≤ 0} := by
  refine continuousOn_of_dominated (bound := fun x => (1 + Real.exp (-(2 * π * x))) * ‖g x‖) ?_ ?_
    (integrable_bound hg hg') ?_
  · intro z _
    exact hg.1.mul (continuous_kern_x z).aestronglyMeasurable
  · intro z hz
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_kern_le hz.1 hz.2 x) (norm_nonneg _)
  · exact Eventually.of_forall fun x => ((continuous_kern x).const_smul (g x)).continuousOn

/-- **The transform is holomorphic in the open strip** `-1 < Im z < 0`. -/
theorem differentiableOn_laplace (hg : Integrable g)
    (hg' : Integrable fun x => Real.exp (-(2 * π * x)) • g x) :
    DifferentiableOn ℂ (laplace g) {z : ℂ | -1 < z.im ∧ z.im < 0} := by
  intro z0 hz0
  obtain ⟨h1, h2⟩ := hz0
  set ε : ℝ := min (-z0.im) (z0.im + 1) / 2 with hε
  have hε0 : 0 < ε := by
    have : 0 < min (-z0.im) (z0.im + 1) := lt_min (by linarith) (by linarith)
    positivity
  have hε1 : ε ≤ -z0.im / 2 := by
    have := min_le_left (-z0.im) (z0.im + 1); rw [hε]; linarith
  have hε2 : ε ≤ (z0.im + 1) / 2 := by
    have := min_le_right (-z0.im) (z0.im + 1); rw [hε]; linarith
  have hball : ∀ z ∈ ball z0 ε, -1 + ε ≤ z.im ∧ z.im ≤ -ε := by
    intro z hz
    have : |z.im - z0.im| ≤ ‖z - z0‖ := by
      simpa using Complex.abs_im_le_norm (z - z0)
    rw [mem_ball, dist_eq_norm] at hz
    have := abs_le.mp (this.trans hz.le)
    constructor <;> linarith [this.1, this.2]
  have hkd : ∀ x : ℝ, ∀ z : ℂ, HasDerivAt (fun w => g x * kern x w)
      (g x * (kern x z * (-(2 * π * I * x)))) z := by
    intro x z
    have h := ((hasDerivAt_id z).const_mul (-(2 * (π : ℂ) * I * x))).cexp.const_mul (g x)
    simpa [kern, mul_comm, mul_left_comm, mul_assoc] using h
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
    (F := fun z x => g x * kern x z)
    (F' := fun z x => g x * (kern x z * (-(2 * π * I * x))))
    (bound := fun x => (1 / ε) * ((1 + Real.exp (-(2 * π * x))) * ‖g x‖))
    (x₀ := z0) (s := ball z0 ε) (ball_mem_nhds z0 hε0)
    (Eventually.of_forall fun z => hg.1.mul (continuous_kern_x z).aestronglyMeasurable)
    (by
      refine (integrable_bound hg hg').mono' (hg.1.mul (continuous_kern_x z0).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_kern_le h1.le h2.le x) (norm_nonneg _))
    (by
      refine hg.1.mul ((continuous_kern_x z0).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x z hz => by
      rw [norm_mul]
      have := deriv_kern_bound hε0 (hball z hz).1 (hball z hz).2 x
      calc ‖g x‖ * ‖kern x z * (-(2 * π * I * x))‖
          ≤ ‖g x‖ * ((1 / ε) * (1 + Real.exp (-(2 * π * x)))) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = (1 / ε) * ((1 + Real.exp (-(2 * π * x))) * ‖g x‖) := by ring)
    ((integrable_bound hg hg').const_mul _)
    (Eventually.of_forall fun x z _ => hkd x z)
  exact (key.2.differentiableAt).differentiableWithinAt

end Lightlike.BisognanoWichmann
