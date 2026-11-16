module

public import Lightlike.Lorentz.Spherical
public import Lightlike.Lorentz.Radial
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Plancherel formula of SL(2,ℂ) for radial functions (milestone HA2)

A function on `G = SL(2,ℂ)` is *radial* (bi-`SU(2)`-invariant) when it depends only on the
hyperbolic distance `r`, `cosh r = coshDist g = ‖g‖_F² / 2`. For `f = F ∘ coshDist` with `F` smooth
and compactly supported, this file proves

  `∫_G |f(g)|² dg = (2π⁴)⁻¹ ∫₀^∞ ρ² |f̂(ρ)|² dρ`      (`spherical_plancherel`),

where `f̂(ρ) = ∫_G f(g) ⟨e₀, π_{0,ρ}(g) e₀⟩ dg` (`sphTransform`, `sphTransform_eq_integral_inner`)
pairs `f` with the spherical function `sin(ρr)/(ρ sinh r)` of the principal series `(0, ρ)`
(`Spherical.lean`). This is the part of the Plancherel formula of `SL(2,ℂ)` (Gel'fand–Naimark)
supported on the representations with an `SU(2)`-fixed vector, with Plancherel density `ρ²`.

## Implementation notes

1. *Radial formula.* `map_coshDist_haarC`: the hyperbolic distance has law `4π³ sinh² r dr` under
   Haar measure; `integral_coshDist` is the Bochner form, with no integrability hypothesis.
2. *Profile.* `h(r) = sinh r · F(cosh r)` is odd, smooth and compactly supported, hence a Schwartz
   function (`sinhSchwartz`); `∫_G |f|² = 4π³ ∫₀^∞ |h|² = 2π³ ∫_ℝ |h|²`.
3. *Sine transform.* The Fourier transform of an odd function is a sine transform
   (`fourier_eq_sine_of_odd`), and `f̂(ρ) = (4π³/ρ) ∫₀^∞ sin(ρr) h(r) dr`
   (`sphTransform_eq_sine`), so `ρ² |f̂(ρ)|² = 4π⁶ |𝓕h(ρ/2π)|²` (`sq_mul_norm_sq_sphTransform`).
4. *Plancherel on `ℝ`.* Mathlib's `SchwartzMap.integral_norm_sq_fourier`, the substitution
   `ρ = 2πξ` and the evenness of `|𝓕h|²` give the formula.

## References

* I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR Ser. Mat. 11 (1947).
* I. M. Gel'fand, M. I. Graev, N. Ya. Vilenkin, *Generalized Functions*, vol. 5: *Integral
  Geometry and Representation Theory* (1966).
* S. Helgason, *Groups and Geometric Analysis* (1984): the spherical transform on symmetric spaces.
  On `ℍ³` with the measure `4π sinh² r dr` the Plancherel constant is `(2π²)⁻¹`, the same as for
  radial functions on `ℝ³`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform ContDiff InnerProductSpace SchwartzMap

namespace Lightlike.Lorentz

/-- The radial measure `4π³ sinh² r dr` on `(0, ∞)`. -/
noncomputable def radialMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun r =>
    ENNReal.ofReal (4 * Real.pi ^ 3 * Real.sinh r ^ 2)

/-- **The distribution of the hyperbolic distance under Haar measure**: the push-forward of
`haarC` under `coshDist` is the push-forward of `4π³ sinh² r dr` under `cosh`. -/
theorem map_coshDist_haarC : haarC.map coshDist = radialMeasure.map Real.cosh := by
  have key : ∀ Φ : ℝ → ℝ≥0∞, Measurable Φ →
      ∫⁻ t, Φ t ∂(haarC.map coshDist) = ∫⁻ t, Φ t ∂(radialMeasure.map Real.cosh) := by
    intro Φ hΦ
    rw [lintegral_map hΦ continuous_coshDist.measurable,
      lintegral_map hΦ Real.continuous_cosh.measurable, lintegral_coshDist_sinh hΦ, radialMeasure,
      lintegral_withDensity_eq_lintegral_mul₀
        (f := fun r => ENNReal.ofReal (4 * Real.pi ^ 3 * Real.sinh r ^ 2))
        (g := fun a => Φ (Real.cosh a)) (by fun_prop)
        (hΦ.comp Real.continuous_cosh.measurable).aemeasurable,
      ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun r => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 3), mul_assoc]
  ext s hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs]
  exact key _ (measurable_one.indicator hs)

/-- **Radial integrals over `SL(2,ℂ)`** (Bochner form): for `Φ : ℝ → E`,
`∫_G Φ(coshDist g) dg = ∫₀^∞ 4π³ sinh² r Φ(cosh r) dr`. No integrability is assumed: both sides
are `0` together when the integrand is not integrable. -/
theorem integral_coshDist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : ℝ → E}
    (hΦ : StronglyMeasurable Φ) :
    ∫ g, Φ (coshDist g) ∂haarC =
      ∫ r in Ioi (0 : ℝ), (4 * Real.pi ^ 3 * Real.sinh r ^ 2) • Φ (Real.cosh r) := by
  rw [← integral_map continuous_coshDist.aemeasurable hΦ.aestronglyMeasurable, map_coshDist_haarC,
    integral_map Real.continuous_cosh.aemeasurable hΦ.aestronglyMeasurable, radialMeasure]
  have hm : Measurable fun r : ℝ => (4 * Real.pi ^ 3 * Real.sinh r ^ 2).toNNReal := by fun_prop
  rw [show (fun r : ℝ => ENNReal.ofReal (4 * Real.pi ^ 3 * Real.sinh r ^ 2)) =
      fun r => ((4 * Real.pi ^ 3 * Real.sinh r ^ 2).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 3 *
    Real.sinh r ^ 2)]

/-! ### Even and odd functions on the line -/

/-- For an even real function, the integral over `(0, ∞)` is half the integral over `ℝ`. No
integrability is needed: both sides are `0` otherwise. -/
lemma integral_Ioi_of_even {f : ℝ → ℝ} (he : ∀ x, f (-x) = f x) :
    ∫ x in Ioi 0, f x = (∫ x, f x) / 2 := by
  have h := integral_comp_abs (f := f)
  have hf : (fun x => f |x|) = f := funext fun x => by
    rcases abs_choice x with hx | hx <;> rw [hx]
    exact he x
  rw [hf] at h
  linarith

/-- For an integrable even function, the integral over `ℝ` is twice the integral over
`(0, ∞)`. -/
lemma integral_eq_two_smul_Ioi_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Integrable f) (he : ∀ x, f (-x) = f x) :
    ∫ x, f x = (2 : ℝ) • ∫ x in Ioi 0, f x := by
  rw [← intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn, two_smul]
  congr 1
  have h := integral_comp_neg_Ioi 0 f
  simp only [neg_zero, he] at h
  exact h.symm

/-- **The Fourier transform of an odd function is a sine transform**:
`𝓕 f ξ = -i ∫ sin(2π r ξ) f(r) dr`. -/
theorem fourier_eq_sine_of_odd {f : ℝ → ℂ} (hf : Integrable f) (ho : ∀ x, f (-x) = -f x)
    (ξ : ℝ) :
    𝓕 f ξ = -Complex.I * ∫ r, (Real.sin (2 * Real.pi * r * ξ) : ℂ) * f r := by
  set g : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) • f v with hg_def
  have hg : Integrable g := by
    have : Integrable fun v =>
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * f v :=
      hf.bdd_mul (c := 1) (by fun_prop)
        (Filter.Eventually.of_forall fun v => by rw [Complex.norm_exp_ofReal_mul_I])
    simpa only [hg_def, smul_eq_mul] using this
  have key : ∀ v, g v + g (-v) =
      2 * (-Complex.I * ((Real.sin (2 * Real.pi * v * ξ) : ℂ) * f v)) := by
    intro v
    have e1 : -2 * Real.pi * v * ξ = -(2 * Real.pi * v * ξ) := by ring
    have e2 : -2 * Real.pi * (-v) * ξ = 2 * Real.pi * v * ξ := by ring
    simp only [hg_def, smul_eq_mul, ho, e1, e2]
    generalize 2 * Real.pi * v * ξ = θ
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
      Complex.sin_neg, Complex.ofReal_sin]
    ring
  have h1 : 𝓕 f ξ = ∫ v, g v := Real.fourier_real_eq_integral_exp_smul f ξ
  have h2 : ∫ v, g (-v) = ∫ v, g v := integral_neg_eq_self g volume
  calc 𝓕 f ξ = (1 / 2 : ℂ) * ((∫ v, g v) + ∫ v, g (-v)) := by rw [h2, h1]; ring
    _ = (1 / 2 : ℂ) * ∫ v, (g v + g (-v)) := by rw [integral_add hg hg.comp_neg]
    _ = (1 / 2 : ℂ) * ∫ v, 2 * (-Complex.I * ((Real.sin (2 * Real.pi * v * ξ) : ℂ) * f v)) := by
        simp_rw [key]
    _ = _ := by rw [integral_const_mul, integral_const_mul]; ring

/-- The sine transform of an odd function over the half-line:
`𝓕 f ξ = -2i ∫₀^∞ sin(2π r ξ) f(r) dr`. -/
theorem fourier_eq_sine_Ioi_of_odd {f : ℝ → ℂ} (hf : Integrable f) (ho : ∀ x, f (-x) = -f x)
    (ξ : ℝ) :
    𝓕 f ξ = -2 * Complex.I * ∫ r in Ioi 0, (Real.sin (2 * Real.pi * r * ξ) : ℂ) * f r := by
  rw [fourier_eq_sine_of_odd hf ho, integral_eq_two_smul_Ioi_of_even]
  · rw [Complex.real_smul]; push_cast; ring
  · exact hf.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun r => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  · intro x
    rw [show 2 * Real.pi * -x * ξ = -(2 * Real.pi * x * ξ) by ring, Real.sin_neg, ho]
    push_cast
    ring

/-! ### The profile `sinh r · F(cosh r)` -/

/-- The profile `h(r) = sinh r · F(cosh r)` of a radial function `F ∘ coshDist`. It is odd, and
`4π³ ∫₀^∞ |h|² dr` is the squared norm of `F ∘ coshDist` in `L²(SL(2,ℂ))`. -/
noncomputable def sinhProfile (F : ℝ → ℂ) (r : ℝ) : ℂ := (Real.sinh r : ℂ) * F (Real.cosh r)

/-- The profile is odd. -/
lemma sinhProfile_neg (F : ℝ → ℂ) (r : ℝ) : sinhProfile F (-r) = -sinhProfile F r := by
  simp [sinhProfile, Real.sinh_neg, Real.cosh_neg]

/-- The profile of a smooth `F` is smooth. -/
lemma contDiff_sinhProfile {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (sinhProfile F) :=
  (Complex.ofRealCLM.contDiff.comp Real.contDiff_sinh).mul (hF.comp Real.contDiff_cosh)

/-- `|r| < cosh r`, since `|r| ≤ sinh |r| < cosh |r|`. -/
lemma abs_lt_cosh (r : ℝ) : |r| < Real.cosh r := by
  rw [← Real.cosh_abs]
  exact (Real.self_le_sinh_iff.mpr (abs_nonneg r)).trans_lt (Real.sinh_lt_cosh _)

/-- The profile of a compactly supported `F` is compactly supported: `F(cosh r) = 0` once
`cosh r` leaves the support, and `cosh r > |r|`. -/
lemma hasCompactSupport_sinhProfile {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport (sinhProfile F) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun r hr => ?_
  have h1 : R < |r| := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hr
    exact hr
  have h2 : Real.cosh r ∉ tsupport F := fun h => by
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos (Real.cosh_pos r)] at this
    linarith [abs_lt_cosh r]
  simp [sinhProfile, image_eq_zero_of_notMem_tsupport h2]

/-! ### The spherical transform -/

/-- The spherical function is measurable in `r`. -/
lemma measurable_sphericalFn (ρ : ℝ) : Measurable (sphericalFn ρ) := by
  have h : Measurable fun r : ℝ =>
      if ρ = 0 then r / Real.sinh r else Real.sin (ρ * r) / (ρ * Real.sinh r) := by
    by_cases hρ : ρ = 0
    · simp only [hρ, ↓reduceIte]; fun_prop
    · simp only [hρ, ↓reduceIte]; fun_prop
  unfold sphericalFn
  exact Measurable.ite (measurableSet_singleton 0) measurable_const h

/-- `arcosh` is measurable. -/
lemma measurable_arcosh : Measurable Real.arcosh := by
  unfold Real.arcosh; fun_prop

/-- The **spherical transform** of a radial function `f = F ∘ coshDist` on `SL(2,ℂ)`:
`f̂(ρ) = ∫_G f(g) φ_ρ(g) dg` with the spherical function `φ_ρ = sphericalFn ρ ∘ r` of the
principal series `(0, ρ)`, where `r = arcosh (coshDist g)` is the hyperbolic distance. -/
noncomputable def sphTransform (F : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∫ g, F (coshDist g) * (sphericalFn ρ (Real.arcosh (coshDist g)) : ℂ) ∂haarC

/-- The spherical transform is the integral of `f` against the matrix coefficient
`⟨e₀, π_{0,ρ}(g) e₀⟩` of the `SU(2)`-invariant unit vector. -/
theorem sphTransform_eq_integral_inner (F : ℝ → ℂ) (ρ : ℝ) :
    sphTransform F ρ =
      ∫ g, F (coshDist g) * ⟪sphVec ρ, principalSeries 0 ρ g (sphVec ρ)⟫_ℂ ∂haarC := by
  simp only [sphTransform, inner_sphVec_eq_sphericalFn]

/-- The spherical transform as a sine transform of the profile:
`f̂(ρ) = (4π³/ρ) ∫₀^∞ sin(ρ r) sinh r F(cosh r) dr` for `ρ > 0`. -/
theorem sphTransform_eq_sine {F : ℝ → ℂ} (hF : Continuous F) {ρ : ℝ} (hρ : 0 < ρ) :
    sphTransform F ρ = ((4 * Real.pi ^ 3 / ρ : ℝ) : ℂ) *
      ∫ r in Ioi 0, (Real.sin (ρ * r) : ℂ) * sinhProfile F r := by
  have hm : StronglyMeasurable fun t => F t * (sphericalFn ρ (Real.arcosh t) : ℂ) :=
    (hF.measurable.mul (Complex.measurable_ofReal.comp
      ((measurable_sphericalFn ρ).comp measurable_arcosh))).stronglyMeasurable
  rw [sphTransform, integral_coshDist hm, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr : 0 < r := hr
  have hs : Real.sinh r ≠ 0 := (Real.sinh_pos_iff.mpr hr).ne'
  simp only [Real.arcosh_cosh hr.le, sphericalFn, hr.ne', hρ.ne', ↓reduceIte, sinhProfile,
    Complex.real_smul]
  push_cast
  field_simp

/-! ### The Plancherel formula -/

/-- The squared `L²` norm of a radial function is `4π³ ∫₀^∞ |sinh r F(cosh r)|² dr`. -/
theorem integral_norm_sq_coshDist {F : ℝ → ℂ} (hF : Continuous F) :
    ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC = 4 * Real.pi ^ 3 * ∫ r in Ioi 0, ‖sinhProfile F r‖ ^ 2 := by
  rw [integral_coshDist (Φ := fun t => ‖F t‖ ^ 2) (hF.norm.pow 2).stronglyMeasurable,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul, sinhProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

/-- The profile `sinh r · F(cosh r)` as a Schwartz function. -/
noncomputable def sinhSchwartz {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_sinhProfile hc).toSchwartzMap (contDiff_sinhProfile hF)

/-- The Schwartz profile is the profile `sinh r · F(cosh r)`. -/
lemma sinhSchwartz_apply {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (r : ℝ) :
    sinhSchwartz hF hc r = sinhProfile F r := rfl

/-- The Fourier transform of the profile is a sine transform. -/
lemma fourier_sinhSchwartz {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (ξ : ℝ) :
    𝓕 (sinhSchwartz hF hc) ξ =
      -2 * Complex.I * ∫ r in Ioi 0, (Real.sin (2 * Real.pi * r * ξ) : ℂ) * sinhProfile F r :=
  fourier_eq_sine_Ioi_of_odd (sinhSchwartz hF hc).integrable (sinhProfile_neg F) ξ

/-- The Fourier transform of the (odd) profile is odd. -/
lemma fourier_sinhSchwartz_neg {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (ξ : ℝ) : 𝓕 (sinhSchwartz hF hc) (-ξ) = -𝓕 (sinhSchwartz hF hc) ξ := by
  rw [fourier_sinhSchwartz, fourier_sinhSchwartz]
  simp only [show ∀ r : ℝ, 2 * Real.pi * r * -ξ = -(2 * Real.pi * r * ξ) from fun r => by ring,
    Real.sin_neg, Complex.ofReal_neg, neg_mul, integral_neg]
  ring

/-- The spherical transform through the Fourier transform of the profile:
`ρ² |f̂(ρ)|² = 4π⁶ |𝓕h(ρ/2π)|²` for `ρ > 0`. -/
theorem sq_mul_norm_sq_sphTransform {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2 =
      4 * Real.pi ^ 6 * ‖𝓕 (sinhSchwartz hF hc) ((2 * Real.pi)⁻¹ * ρ)‖ ^ 2 := by
  have hπ := Real.pi_pos
  have harg : ∀ r : ℝ, 2 * Real.pi * r * ((2 * Real.pi)⁻¹ * ρ) = ρ * r := fun r => by
    field_simp
  rw [sphTransform_eq_sine hF.continuous hρ, fourier_sinhSchwartz]
  simp only [harg, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 4 * Real.pi ^ 3 / ρ), Complex.norm_ofNat]
  field_simp
  ring

/-- **The Plancherel formula of `SL(2,ℂ)` for radial functions** (Gel'fand–Naimark): for
`f = F ∘ coshDist` with `F` smooth and compactly supported,
`∫_G |f|² dg = (2π⁴)⁻¹ ∫₀^∞ ρ² |f̂(ρ)|² dρ`, where `f̂(ρ) = ∫_G f φ_ρ dg` is the spherical
transform against the spherical functions of the principal series `(0, ρ)`.
The Plancherel density on these representations is `ρ²`. The constant `(2π⁴)⁻¹` belongs to the
normalisation `dg = 4π³ sinh² r dr` of the Haar measure on radial functions; on hyperbolic space
`SL(2,ℂ)/SU(2)` it is the classical `(2π²)⁻¹`, since the fibre `SU(2)` has volume `π²` here.
The proof writes both sides through the odd profile `h(r) = sinh r F(cosh r)`: the left side is
`2π³ ∫_ℝ |h|²` by the radial formula, and `f̂(ρ)` is `(2π³ i/ρ) 𝓕h(ρ/2π)` by the sine-transform
identity, so the formula is Plancherel's theorem for the Schwartz function `h`. -/
theorem spherical_plancherel {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC =
      (2 * Real.pi ^ 4)⁻¹ * ∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2 := by
  set S := sinhSchwartz hF hc
  have hπ := Real.pi_pos
  have hL : ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC = 2 * Real.pi ^ 3 * ∫ r, ‖S r‖ ^ 2 := by
    rw [integral_norm_sq_coshDist hF.continuous]
    simp only [S, sinhSchwartz_apply]
    rw [integral_Ioi_of_even (fun r => by simp only [sinhProfile_neg, norm_neg])]
    ring
  calc ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC = 2 * Real.pi ^ 3 * ∫ r, ‖S r‖ ^ 2 := hL
    _ = (2 * Real.pi ^ 4)⁻¹ *
          (4 * Real.pi ^ 6 * ((2 * Real.pi) * ((∫ ξ, ‖𝓕 S ξ‖ ^ 2) / 2))) := by
        rw [SchwartzMap.integral_norm_sq_fourier]
        field_simp
        ring
    _ = (2 * Real.pi ^ 4)⁻¹ * ∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2 := by
        rw [setIntegral_congr_fun measurableSet_Ioi
            (fun ρ hρ => sq_mul_norm_sq_sphTransform hF hc hρ), integral_const_mul,
          integral_comp_mul_left_Ioi (fun ξ => ‖𝓕 S ξ‖ ^ 2) 0 (by positivity), mul_zero,
          integral_Ioi_of_even (fun ξ => by rw [fourier_sinhSchwartz_neg, norm_neg]),
          smul_eq_mul, inv_inv]

end Lightlike.Lorentz
