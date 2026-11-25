import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelCasimir
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz
import Lightlike.Lorentz.SL2RPlancherel.AbelTransformDeriv
import Lightlike.Lorentz.SL2RPlancherel.DerivativePlancherel
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean

/-!
# The Abel transform diagonalises the radial Casimir

For `F` smooth with compact support and `Q F = -((v² - 1) F'' + 2 v F')` (the radial Laplacian of the
hyperbolic plane in the variable `v = cosh r`), the Abel transform satisfies
`𝒜(Q F) = (1/4) 𝒜F - (𝒜F)''`.
-/

open MeasureTheory Set Real
open scoped ContDiff FourierTransform

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The radial Laplacian `Q F = -((v² - 1) F'' + 2 v F')` in the variable `v = cosh r`. -/
def radialQ (F : ℝ → ℂ) (v : ℝ) : ℂ :=
  -((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v + ((2 * v : ℝ) : ℂ) * deriv F v)

/-- `(𝒜F)'' (t) = √2 (cosh t · H'(cosh t) + sinh² t · H''(cosh t))`, `H = halfAbel F`. -/
theorem deriv_deriv_abelTransform {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) :
    deriv (deriv (abelTransform F)) t =
      (√2 : ℂ) * ((Real.cosh t : ℂ) * halfAbel (deriv F) (Real.cosh t)
        + ((Real.sinh t ^ 2 : ℝ) : ℂ) * halfAbel (deriv (deriv F)) (Real.cosh t)) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_cast)
  have hd : deriv (abelTransform F) =
      fun s => (√2 : ℂ) * (Real.sinh s : ℂ) * halfAbel (deriv F) (Real.cosh s) :=
    funext fun s => (hasDerivAt_abelTransform F hF1 hc s).deriv
  have hF1d : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
  have hF1d1 : ContDiff ℝ 1 (deriv F) := hF1d.of_le (by norm_cast)
  have hH1 : HasDerivAt (halfAbel (deriv F)) (halfAbel (deriv (deriv F)) (Real.cosh t)) (Real.cosh t) :=
    hasDerivAt_halfAbel' (deriv F) hF1d1 hc.deriv _
  have hcomp := hH1.scomp t (Real.hasDerivAt_cosh t)
  have hsinh : HasDerivAt (fun s : ℝ => (√2 : ℂ) * (Real.sinh s : ℂ))
      ((√2 : ℂ) * (Real.cosh t : ℂ)) t := by
    have := (Real.hasDerivAt_sinh t).ofReal_comp.const_mul (√2 : ℂ)
    simpa using this
  have hprod := hsinh.mul (hcomp)
  rw [hd]
  have hprod' := hprod.deriv
  simp only [Pi.mul_def, Function.comp] at hprod'
  rw [hprod']
  simp only [Complex.real_smul]
  push_cast
  rw [sq]
  ring

/-- **The Abel transform diagonalises the Casimir**: `𝒜(Q F) = (1/4) 𝒜F - (𝒜F)''`. -/
theorem abelTransform_radialQ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) :
    abelTransform (radialQ F) t =
      (1 / 4 : ℂ) * abelTransform F t - deriv (deriv (abelTransform F)) t := by
  rw [deriv_deriv_abelTransform hF hc, abelTransform_eq_halfAbel, abelTransform_eq_halfAbel]
  have h := halfAbel_casimir (hF.of_le (by norm_cast) : ContDiff ℝ 2 F) hc (Real.cosh t)
  have hs : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := by
    have := Real.cosh_sq t; linarith
  unfold radialQ
  rw [h, hs]
  push_cast
  ring


/-- **The spherical transform diagonalises the radial Casimir**:
`(Q F)^(ρ) = (1/4 + ρ²) F^(ρ)`. -/
theorem sphTransformH_radialQ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ρ : ℝ) :
    sphTransformH (radialQ F) ρ = ((1 / 4 : ℂ) + (ρ : ℂ) ^ 2) * sphTransformH F ρ := by
  set g := abelSchwartz F hF hc with hg
  set ξ : ℝ := ρ / (2 * Real.pi) with hξ
  have hρ : 2 * Real.pi * ξ = ρ := by rw [hξ]; field_simp
  set h : SchwartzMap ℝ ℂ := (1 / 4 : ℂ) • g
    - SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g) with hh
  have hfun : abelTransform (radialQ F) = (h : ℝ → ℂ) := by
    funext t
    rw [abelTransform_radialQ hF hc]
    simp only [hh, sub_apply, smul_apply, SchwartzMap.derivCLM_apply,
      smul_eq_mul]
    have h1 : (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) = deriv (g : ℝ → ℂ) :=
      funext fun x => SchwartzMap.derivCLM_apply ℂ g x
    have h2 : deriv (g : ℝ → ℂ) = deriv (abelTransform F) := rfl
    rw [h1, h2]
    rfl
  have h1 := fourier_abelTransform (radialQ F) ξ
  rw [hρ, hfun] at h1
  have h2 := fourier_abelTransform F ξ
  rw [hρ] at h2
  have hg' : (g : ℝ → ℂ) = abelTransform F := rfl
  rw [← h1]
  have hl : 𝓕 (h : ℝ → ℂ) ξ = (1 / 4 : ℂ) * 𝓕 (g : ℝ → ℂ) ξ
      - 𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g) : ℝ → ℂ) ξ := by
    have := congrArg (fun k : SchwartzMap ℝ ℂ => (SchwartzMap.fourierTransformCLM ℂ k) ξ) hh
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul] at this
    exact this
  rw [hl, fourier_deriv_schwartz, fourier_deriv_schwartz, hg', h2]
  have hξρ : (2 * Real.pi * Complex.I * ξ : ℂ) = Complex.I * ρ := by
    rw [← hρ]; push_cast; ring
  rw [hξρ]
  have : (Complex.I * (ρ : ℂ)) * ((Complex.I * (ρ : ℂ)) * sphTransformH F ρ) =
      -((ρ : ℂ) ^ 2) * sphTransformH F ρ := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [this]
  ring

end Lightlike.Lorentz.SL2RPlancherel
