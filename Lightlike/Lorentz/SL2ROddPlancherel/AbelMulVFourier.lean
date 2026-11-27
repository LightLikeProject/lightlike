import Mathlib
import Lightlike.Lorentz.SL2ROddPlancherel.AbelMulV
import Lightlike.Lorentz.SL2ROddPlancherel.ComplexFourier

/-!
# The Fourier transform of the Abel transform of `v G(v)`

With `g = 𝒜G` and `a(z) = ftC g z`, the Abel transform of `vG` is `cosh t · g(t) + k(t)` with
`k(t) = ½ ∫_{s>t} sinh s · g(s) ds` (`abelTransform_mul_v`), and `k' = -½ sinh · g`. Hence, for every complex `z`,

  `z · ftC (𝒜(vG)) z = ½ [(z - i/2) a(z - i) + (z + i/2) a(z + i)]`   (`ftC_abel_mul_v`):

multiplication by `cosh t` shifts the frequency by `±i`, and `z · k̂(z) = i · ft(k')(z)` is integration by parts
(`ftC_deriv`). On the Fourier side this is the Legendre recursion `(2μ + 1) v P_μ = (μ + 1) P_{μ+1} + μ P_{μ-1}`
(`docs/notes/sl2r-odd-plancherel-route.md`).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

lemma exp_sub_I_mul (z : ℂ) (t : ℝ) :
    Complex.exp ((z - I) * t * I) = Complex.exp (z * t * I) * (Real.exp t : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have := Complex.I_mul_I
  linear_combination (-(t : ℂ)) * this

lemma exp_add_I_mul (z : ℂ) (t : ℝ) :
    Complex.exp ((z + I) * t * I) = Complex.exp (z * t * I) * (Real.exp (-t) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  have := Complex.I_mul_I
  linear_combination ((t : ℂ)) * this

lemma integrable_exp_mul {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (z : ℂ) :
    Integrable fun t : ℝ => Complex.exp (z * t * I) * g t :=
  ((by fun_prop : Continuous fun t : ℝ => Complex.exp (z * t * I)).mul hg).integrable_of_hasCompactSupport
    hc.mul_left

/-- Multiplication by `cosh t` shifts the frequency by `±i`. -/
lemma ftC_cosh_mul {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (z : ℂ) :
    ftC (fun t => (Real.cosh t : ℂ) * g t) z = (1 / 2 : ℂ) * (ftC g (z - I) + ftC g (z + I)) := by
  unfold ftC
  have h1 := integrable_exp_mul hg hc (z - I)
  have h2 := integrable_exp_mul hg hc (z + I)
  rw [← integral_add h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [exp_sub_I_mul, exp_add_I_mul, Real.cosh_eq]
  push_cast
  ring

/-- Multiplication by `sinh t`. -/
lemma ftC_sinh_mul {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (z : ℂ) :
    ftC (fun t => (Real.sinh t : ℂ) * g t) z = (1 / 2 : ℂ) * (ftC g (z - I) - ftC g (z + I)) := by
  unfold ftC
  have h1 := integrable_exp_mul hg hc (z - I)
  have h2 := integrable_exp_mul hg hc (z + I)
  rw [← integral_sub h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [exp_sub_I_mul, exp_add_I_mul, Real.sinh_eq]
  push_cast
  ring

lemma ftC_add {f₁ f₂ : ℝ → ℂ} (h₁ : Continuous f₁) (c₁ : HasCompactSupport f₁) (h₂ : Continuous f₂)
    (c₂ : HasCompactSupport f₂) (z : ℂ) :
    ftC (fun t => f₁ t + f₂ t) z = ftC f₁ z + ftC f₂ z := by
  unfold ftC
  simp_rw [mul_add]
  exact integral_add (integrable_exp_mul h₁ c₁ z) (integrable_exp_mul h₂ c₂ z)

/-- The tail integral `k(t) = ½ ∫_{s>t} sinh s · g(s) ds`. -/
def tailK (g : ℝ → ℂ) (t : ℝ) : ℂ := (1 / 2 : ℂ) * ∫ s in Ioi t, (Real.sinh s : ℂ) * g s

lemma hasDerivAt_tailK {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (t : ℝ) :
    HasDerivAt (tailK g) (-(1 / 2 : ℂ) * ((Real.sinh t : ℂ) * g t)) t := by
  have hφc : Continuous fun s : ℝ => (Real.sinh s : ℂ) * g s :=
    (Complex.continuous_ofReal.comp Real.continuous_sinh).mul hg
  have hφi : Integrable fun s : ℝ => (Real.sinh s : ℂ) * g s :=
    hφc.integrable_of_hasCompactSupport hc.mul_left
  have := (hasDerivAt_integral_Ioi hφc hφi t).const_mul (1 / 2 : ℂ)
  refine HasDerivAt.congr_deriv this ?_
  ring

/-- `k` vanishes outside a compact set when `g` is even with compact support (the odd function `sinh · g`
has integral `0`). -/
lemma tailK_eq_zero {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (heven : ∀ t, g (-t) = g t)
    {R : ℝ} (hR : ∀ t, R < |t| → g t = 0) {t : ℝ} (ht : R < |t|) : tailK g t = 0 := by
  have hφc : Continuous fun s : ℝ => (Real.sinh s : ℂ) * g s :=
    (Complex.continuous_ofReal.comp Real.continuous_sinh).mul hg
  have hφi : Integrable fun s : ℝ => (Real.sinh s : ℂ) * g s :=
    hφc.integrable_of_hasCompactSupport hc.mul_left
  have hodd : ∫ s : ℝ, (Real.sinh s : ℂ) * g s = 0 := by
    have h := integral_neg_eq_self (fun s : ℝ => (Real.sinh s : ℂ) * g s) (volume : Measure ℝ)
    simp only [Real.sinh_neg, Complex.ofReal_neg, neg_mul, heven, integral_neg] at h
    have : (2 : ℂ) * ∫ s : ℝ, (Real.sinh s : ℂ) * g s = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  unfold tailK
  rcases lt_abs.mp ht with h | h
  · -- t > R
    have : ∫ s in Ioi t, (Real.sinh s : ℂ) * g s = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun s (hs : t < s) => by
        rw [hR s (lt_abs.mpr (Or.inl (by linarith)))]; simp
    rw [this]; simp
  · -- t < -R
    have hIic : ∫ s in Iic t, (Real.sinh s : ℂ) * g s = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun s (hs : s ≤ t) => by
        rw [hR s (lt_abs.mpr (Or.inr (by linarith)))]; simp
    have hsplit := integral_add_compl (measurableSet_Iic (a := t)) hφi
    have hcompl : (Iic t)ᶜ = Ioi t := compl_Iic
    rw [hcompl, hIic, zero_add, hodd] at hsplit
    rw [hsplit]; simp

/-- **The Fourier transform of `𝒜(vG)`**: `z · ftC 𝒜(vG) z = ½ [(z - i/2) a(z - i) + (z + i/2) a(z + i)]`
with `a = ftC (𝒜G)`. -/
theorem ftC_abel_mul_v {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (z : ℂ) :
    z * ftC (abelTransform fun v => (v : ℂ) * G v) z =
      (1 / 2 : ℂ) * ((z - I / 2) * ftC (abelTransform G) (z - I) +
        (z + I / 2) * ftC (abelTransform G) (z + I)) := by
  set g := abelTransform G with hgdef
  have hg1 : ContDiff ℝ ∞ g := contDiff_abelTransform G hG hc
  have hgc : HasCompactSupport g := hasCompactSupport_abelTransform G hc
  have hgcont : Continuous g := hg1.continuous
  have heven : ∀ t, g (-t) = g t := abelTransform_neg G
  obtain ⟨R, hR0, hR⟩ := exists_zero_of_abs_gt hgc
  have hkd : ∀ t, HasDerivAt (tailK g) (-(1 / 2 : ℂ) * ((Real.sinh t : ℂ) * g t)) t :=
    hasDerivAt_tailK hgcont hgc
  have hkderiv : deriv (tailK g) = fun t => -(1 / 2 : ℂ) * ((Real.sinh t : ℂ) * g t) :=
    funext fun t => (hkd t).deriv
  have hksm : ContDiff ℝ ∞ (tailK g) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hkd t).differentiableAt, ?_⟩
    rw [hkderiv]
    exact contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sinh).mul hg1)
  have hkc : HasCompactSupport (tailK g) :=
    HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun t ht => by
      apply tailK_eq_zero hgcont hgc heven hR
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have habel : abelTransform (fun v => (v : ℂ) * G v) = fun t => (Real.cosh t : ℂ) * g t + tailK g t := by
    funext t
    rw [abelTransform_mul_v hG hc t]
    unfold tailK
    ring
  have hcosh_c : Continuous fun t : ℝ => (Real.cosh t : ℂ) * g t :=
    (Complex.continuous_ofReal.comp Real.continuous_cosh).mul hgcont
  have hcosh_k : HasCompactSupport fun t : ℝ => (Real.cosh t : ℂ) * g t := hgc.mul_left
  rw [habel, ftC_add hcosh_c hcosh_k hksm.continuous hkc, ftC_cosh_mul hgcont hgc]
  -- `z · ftC k z = i · ftC k' z`
  have hk1 : ContDiff ℝ 1 (tailK g) := hksm.of_le (by norm_cast)
  have hd := ftC_deriv hk1 hkc z
  rw [hkderiv] at hd
  have hs : ftC (fun t => -(1 / 2 : ℂ) * ((Real.sinh t : ℂ) * g t)) z =
      -(1 / 2 : ℂ) * ftC (fun t => (Real.sinh t : ℂ) * g t) z := by
    unfold ftC
    rw [← integral_const_mul]
    congr 1; funext t; ring
  rw [hs, ftC_sinh_mul hgcont hgc] at hd
  have hI : I * I = -1 := Complex.I_mul_I
  have hkz : z * ftC (tailK g) z = -(I / 4) * (ftC g (z - I) - ftC g (z + I)) := by
    linear_combination (-I) * hd + (z * ftC (tailK g) z) * hI
  linear_combination hkz

end Lightlike.Lorentz.SL2ROddPlancherel
