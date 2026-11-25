import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelCasimirTransform
import Lightlike.Lorentz.SL2RPlancherel.SphericalClean
import Lightlike.Lorentz.SL2RPlancherel.WeightIntegrable
import Lightlike.Lorentz.SL2RPlancherel.Linearity
import Lightlike.Lorentz.SL2RPlancherel.Ladder
import Lightlike.Lorentz.SL2RPlancherel.CoshChange

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

theorem contDiff_radialQ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (radialQ F) := by
  have h1 : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv F)) := (contDiff_infty_iff_deriv.1 h1).2
  have hp : ContDiff ℝ ∞ (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const)
  have hq : ContDiff ℝ ∞ (fun v : ℝ => ((2 * v : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  exact ((hp.mul h2).add (hq.mul h1)).neg

theorem hasCompactSupport_radialQ {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (radialQ F) :=
  ((hc.deriv.deriv.mul_left (f := fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ))).add
    (hc.deriv.mul_left (f := fun v : ℝ => ((2 * v : ℝ) : ℂ)))).neg

/-- Integration by parts for the radial Laplacian on `(1, ∞)`:
`∫_{v>1} conj F · Q F = ∫_{v>1} (v² - 1) |F'|²`. -/
theorem integral_conj_radialQ {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∫ v in Ioi (1 : ℝ), starRingEnd ℂ (F v) * radialQ F v =
      ∫ v in Ioi (1 : ℝ), (((v ^ 2 - 1 : ℝ)) : ℂ) * (starRingEnd ℂ (deriv F v) * deriv F v) := by
  have h1 : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv F)) := (contDiff_infty_iff_deriv.1 h1).2
  have hFd : ∀ v, HasDerivAt F (deriv F v) v := fun v =>
    ((hF.differentiable (by simp)) v).hasDerivAt
  have hF1d : ∀ v, HasDerivAt (deriv F) (deriv (deriv F) v) v := fun v =>
    ((h1.differentiable (by simp)) v).hasDerivAt
  set u : ℝ → ℂ := fun v => starRingEnd ℂ (F v) with hu
  set w : ℝ → ℂ := fun v => (((v ^ 2 - 1 : ℝ)) : ℂ) * deriv F v with hw
  have hu' : ∀ v, HasDerivAt u (starRingEnd ℂ (deriv F v)) v := fun v => by
    have := (hFd v).star
    simpa using this
  have hw' : ∀ v, HasDerivAt w ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v
      + ((2 * v : ℝ) : ℂ) * deriv F v) v := fun v => by
    have hp : HasDerivAt (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) ((2 * v : ℝ) : ℂ) v := by
      have := ((hasDerivAt_pow 2 v).sub_const 1).ofReal_comp
      simpa using this
    exact (hp.mul (hF1d v)).congr_deriv (by ring)
  have hcu : HasCompactSupport u := by
    have := hc.comp_left (g := starRingEnd ℂ) (map_zero _)
    exact this
  have hwc : Continuous w := by
    have hp : Continuous (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) := by fun_prop
    exact hp.mul (h1.continuous)
  have huc : Continuous u := (Complex.continuous_conj).comp hF.continuous
  have hu'c : Continuous (fun v => starRingEnd ℂ (deriv F v)) :=
    (Complex.continuous_conj).comp h1.continuous
  have hv'c : Continuous (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v
      + ((2 * v : ℝ) : ℂ) * deriv F v) := by
    have hp : Continuous (fun v : ℝ => (((v ^ 2 - 1 : ℝ)) : ℂ)) := by fun_prop
    have hq : Continuous (fun v : ℝ => ((2 * v : ℝ) : ℂ)) := by fun_prop
    exact (hp.mul h2.continuous).add (hq.mul h1.continuous)
  have hcu' : HasCompactSupport (fun v => starRingEnd ℂ (deriv F v)) :=
    hc.deriv.comp_left (g := starRingEnd ℂ) (map_zero _)
  have hz1 : Tendsto (u * w) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h0 : (u * w) 1 = 0 := by simp [hu, hw]
    have := ((huc.mul hwc).tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    rwa [h0] at this
  have hz2 : Tendsto (u * w) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_zero_translate hcu 0] with v hv
    have hv' : u v = 0 := by simpa using hv
    simp [Pi.mul_apply, hv']
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (a' := 0) (b' := 0)
    (u := u) (v := w) (u' := fun v => starRingEnd ℂ (deriv F v))
    (v' := fun v => (((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v + ((2 * v : ℝ) : ℂ) * deriv F v)
    (fun v _ => hu' v) (fun v _ => hw' v)
    ((huc.mul hv'c).integrable_of_hasCompactSupport hcu.mul_right).integrableOn
    ((hu'c.mul hwc).integrable_of_hasCompactSupport hcu'.mul_right).integrableOn hz1 hz2
  have e1 : ∀ v : ℝ, starRingEnd ℂ (F v) * radialQ F v =
      -(u v * ((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v + ((2 * v : ℝ) : ℂ) * deriv F v)) := by
    intro v; simp only [radialQ, hu]; ring
  have e2 : ∀ v : ℝ, starRingEnd ℂ (deriv F v) * w v =
      (((v ^ 2 - 1 : ℝ)) : ℂ) * (starRingEnd ℂ (deriv F v) * deriv F v) := by
    intro v; simp only [hw]; ring
  simp only [e1, integral_neg, key, e2]
  simp

theorem integrableOn_norm_sq {F : ℝ → ℂ} (hF : Continuous F) (hc : HasCompactSupport F)
    (s : Set ℝ) : IntegrableOn (fun v : ℝ => ‖F v‖ ^ 2) s := by
  have h1 : Continuous (fun v : ℝ => ‖F v‖ ^ 2) := by fun_prop
  have h2 : HasCompactSupport (fun v : ℝ => ‖F v‖ ^ 2) :=
    hc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact (h1.integrable_of_hasCompactSupport h2).integrableOn

theorem integrableOn_conj_mul {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hc : HasCompactSupport F) (s : Set ℝ) :
    IntegrableOn (fun v : ℝ => starRingEnd ℂ (F v) * G v) s := by
  have h1 : Continuous (fun v : ℝ => starRingEnd ℂ (F v) * G v) :=
    (Complex.continuous_conj.comp hF).mul hG
  have h2 : HasCompactSupport (fun v : ℝ => starRingEnd ℂ (F v) * G v) :=
    (hc.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right
  exact (h1.integrable_of_hasCompactSupport h2).integrableOn

/-- `‖z + w‖² = ‖z‖² + ‖w‖² + 2 Re (conj z · w)`. -/
theorem norm_add_sq_conj (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (starRingEnd ℂ z * w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The Plancherel formula for the derivative**: for `F` smooth with compact support,
`π² ∫_{v>1} (v² - 1) |F'(v)|² = ¼ ∫_{ρ>0} ρ tanh(πρ) (¼ + ρ²) |f̂(ρ)|² dρ`. -/
theorem norm_sq_deriv_eq_sph {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) * ‖deriv F v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ),
        ρ * Real.tanh (Real.pi * ρ) * ((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2 := by
  set G := radialQ F with hGdef
  have hG : ContDiff ℝ ∞ G := contDiff_radialQ hF
  have hGc : HasCompactSupport G := hasCompactSupport_radialQ hc
  have hH : ContDiff ℝ ∞ (F + G) := hF.add hG
  have hHc : HasCompactSupport (F + G) := hc.add hGc
  have p1 := norm_sq_eq_sph F hF hc
  have p2 := norm_sq_eq_sph G hG hGc
  have p3 := norm_sq_eq_sph (F + G) hH hHc
  -- the transforms
  have hĜ : ∀ ρ : ℝ, sphTransformH G ρ = (((1 / 4 : ℝ) + ρ ^ 2 : ℝ) : ℂ) * sphTransformH F ρ := by
    intro ρ; rw [hGdef, sphTransformH_radialQ hF hc]; push_cast; ring
  have hŜ : ∀ ρ : ℝ, sphTransformH (F + G) ρ =
      (((1 : ℝ) + ((1 / 4 : ℝ) + ρ ^ 2) : ℝ) : ℂ) * sphTransformH F ρ := by
    intro ρ; rw [sphTransformH_add hF hc hG hGc, hĜ]; push_cast; ring
  -- real-line side
  have iA : IntegrableOn (fun v : ℝ => ‖F v‖ ^ 2) (Ioi (1 : ℝ)) :=
    integrableOn_norm_sq hF.continuous hc _
  have iB : IntegrableOn (fun v : ℝ => ‖G v‖ ^ 2) (Ioi (1 : ℝ)) :=
    integrableOn_norm_sq hG.continuous hGc _
  have iC : IntegrableOn (fun v : ℝ => starRingEnd ℂ (F v) * G v) (Ioi (1 : ℝ)) :=
    integrableOn_conj_mul hF.continuous hG.continuous hc _
  have hK : ∫ v in Ioi (1 : ℝ), (starRingEnd ℂ (F v) * G v) =
      (((∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) * ‖deriv F v‖ ^ 2 : ℝ)) : ℂ) := by
    rw [hGdef, integral_conj_radialQ hF hc, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Complex.conj_mul']
    push_cast; ring
  have hL3 : ∫ v in Ioi (1 : ℝ), ‖(F + G) v‖ ^ 2 =
      (∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2) + (∫ v in Ioi (1 : ℝ), ‖G v‖ ^ 2)
        + 2 * (∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) * ‖deriv F v‖ ^ 2) := by
    have hre : ∫ v in Ioi (1 : ℝ), (starRingEnd ℂ (F v) * G v).re =
        ∫ v in Ioi (1 : ℝ), (v ^ 2 - 1) * ‖deriv F v‖ ^ 2 := by
      have h := integral_re iC
      simp only [RCLike.re_to_complex] at h
      rw [h, hK, Complex.ofReal_re]
    have : ∀ v : ℝ, ‖(F + G) v‖ ^ 2 =
        ‖F v‖ ^ 2 + ‖G v‖ ^ 2 + 2 * (starRingEnd ℂ (F v) * G v).re := fun v =>
      norm_add_sq_conj (F v) (G v)
    simp only [this]
    have iR : IntegrableOn (fun v : ℝ => (starRingEnd ℂ (F v) * G v).re) (Ioi (1 : ℝ)) := iC.re
    have iAB : IntegrableOn (fun v : ℝ => ‖F v‖ ^ 2 + ‖G v‖ ^ 2) (Ioi (1 : ℝ)) := iA.add iB
    have iR2 : IntegrableOn (fun v : ℝ => 2 * (starRingEnd ℂ (F v) * G v).re) (Ioi (1 : ℝ)) :=
      iR.const_mul 2
    rw [integral_add iAB iR2, integral_add iA iB, integral_const_mul, hre]
  -- Fourier side
  have nG : ∀ ρ : ℝ, ‖sphTransformH G ρ‖ ^ 2 =
      ((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2 := by
    intro ρ
    rw [hĜ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
  have nH : ∀ ρ : ℝ, ‖sphTransformH (F + G) ρ‖ ^ 2 =
      (1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2 := by
    intro ρ
    rw [hŜ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
  have j1 := integrableOn_sph_weight F hF hc
  have j2 : IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) *
      (((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2)) (Ioi (0 : ℝ)) := by
    have := integrableOn_sph_weight G hG hGc
    simpa only [nG] using this
  have j3 : IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) *
      ((1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2)) (Ioi (0 : ℝ)) := by
    have := integrableOn_sph_weight (F + G) hH hHc
    simpa only [nH] using this
  have jM : IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) *
      (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun ρ : ℝ => (1 / 2 : ℝ) * (
        ρ * Real.tanh (Real.pi * ρ) * ((1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2)
        - ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2
        - ρ * Real.tanh (Real.pi * ρ) *
          (((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2))) (Ioi (0 : ℝ)) :=
      ((j3.sub j1).sub j2).const_mul (1 / 2 : ℝ)
    refine MeasureTheory.IntegrableOn.congr_fun h (fun ρ _ => ?_) measurableSet_Ioi
    ring
  have j12 : IntegrableOn (fun ρ : ℝ => ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2
      + ρ * Real.tanh (Real.pi * ρ) *
          (((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2)) (Ioi (0 : ℝ)) := j1.add j2
  have jM2 : IntegrableOn (fun ρ : ℝ => 2 * (ρ * Real.tanh (Real.pi * ρ) *
      (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2))) (Ioi (0 : ℝ)) := jM.const_mul 2
  have hR : ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
        ((1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2) =
      (∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2)
      + (∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
          (((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2))
      + 2 * (∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
          (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => (by ring :
      ρ * Real.tanh (Real.pi * ρ) * ((1 + ((1 / 4 : ℝ) + ρ ^ 2)) ^ 2 * ‖sphTransformH F ρ‖ ^ 2) =
      (ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2
        + ρ * Real.tanh (Real.pi * ρ) * (((1 / 4 : ℝ) + ρ ^ 2) ^ 2 * ‖sphTransformH F ρ‖ ^ 2))
      + 2 * (ρ * Real.tanh (Real.pi * ρ) * (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2)))),
      integral_add j12 jM2, integral_add j1 j2, integral_const_mul]
  simp only [nG, nH] at p2 p3
  rw [hL3] at p3
  have hM : ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ((1 / 4 : ℝ) + ρ ^ 2) *
        ‖sphTransformH F ρ‖ ^ 2 = ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) *
          (((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => ?_)
    ring
  rw [hM]
  linear_combination (1 / 2 : ℝ) * p3 - (1 / 2 : ℝ) * p1 - (1 / 2 : ℝ) * p2 + (1 / 8 : ℝ) * hR

/-- **Plancherel for the K-type `(1, 0)`**: the `(1,0)` ladder image `ladUp 0 0 (F ∘ cosh)` of a smooth compactly
supported radial function has `L²(sinh ξ dξ)`-norm given by the spherical Plancherel measure times `¼ + ρ²`. -/
theorem norm_sq_ladUp_zero_eq_sph {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Real.pi ^ 2 * ∫ ξ in Ioi (0 : ℝ),
        ‖ladUp 0 0 (fun s : ℝ => F (Real.cosh s)) ξ‖ ^ 2 * Real.sinh ξ =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ),
        ρ * Real.tanh (Real.pi * ρ) * ((1 / 4 : ℝ) + ρ ^ 2) * ‖sphTransformH F ρ‖ ^ 2 := by
  rw [← norm_sq_deriv_eq_sph hF hc]
  congr 1
  have h := integral_Ioi_one_cosh (fun a : ℝ => (((a ^ 2 - 1) * ‖deriv F a‖ ^ 2 : ℝ) : ℂ))
  rw [integral_complex_ofReal] at h
  have h2 : ∫ ξ in Ioi (0 : ℝ), ‖ladUp 0 0 (fun s : ℝ => F (Real.cosh s)) ξ‖ ^ 2 * Real.sinh ξ =
      ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℝ) *
        ((Real.cosh ξ ^ 2 - 1) * ‖deriv F (Real.cosh ξ)‖ ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ _ => ?_)
    have hd : deriv (fun s : ℝ => F (Real.cosh s)) ξ = (Real.sinh ξ : ℂ) * deriv F (Real.cosh ξ) := by
      have := ((hF.differentiable (by simp)) (Real.cosh ξ)).hasDerivAt.scomp ξ (Real.hasDerivAt_cosh ξ)
      have e : deriv (fun s : ℝ => F (Real.cosh s)) ξ = Real.sinh ξ • deriv F (Real.cosh ξ) :=
        this.deriv
      rw [e]; simp [Complex.real_smul]
    simp only [ladUp, ladCoeff, hd, zero_mul, zero_div, add_zero, Complex.ofReal_zero, sub_zero]
    rw [norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
    have : Real.sinh ξ ^ 2 = Real.cosh ξ ^ 2 - 1 := by have := Real.cosh_sq ξ; linarith
    rw [this]; ring
  rw [h2]
  have h3 : ∫ t in Ioi (0 : ℝ), (Real.sinh t : ℂ) *
      (((Real.cosh t ^ 2 - 1) * ‖deriv F (Real.cosh t)‖ ^ 2 : ℝ) : ℂ) =
      (((∫ t in Ioi (0 : ℝ), Real.sinh t *
        ((Real.cosh t ^ 2 - 1) * ‖deriv F (Real.cosh t)‖ ^ 2) : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    push_cast; ring
  rw [h3] at h
  exact_mod_cast h.symm

end Lightlike.Lorentz.SL2RPlancherel
