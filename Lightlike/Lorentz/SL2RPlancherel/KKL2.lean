import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KKParseval

/-!
# The `K × K` decomposition of `L²(SL(2,ℝ))`

The `K × K`-Fourier components `kkCoeff f m` of a continuous square-integrable `f` lie in
`L²((0, ∞), sinh ξ dξ)`, presented as `√(sinh ξ) f_m(ξ)` in `L²(0, ∞)` (`kkSrc`), and
`‖f‖² = (2π)² ∑_m ‖f_m‖²` (`lintegral_norm_sq_eq_kk`).  This file builds the extension of
`f ↦ (f_m)_m` to all of `L²(SL(2,ℝ))`.  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (the
first step of the assembly), milestone HA3.
-/

open MeasureTheory Set Real Filter Topology Lightlike.Lorentz.SL2R
open scoped ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The box `(0, 1]²` is almost everywhere the closed box `[0, 1]²`. -/
lemma box_ae_eq_Icc : box =ᵐ[volume] Icc (0 : Fin 2 → ℝ) 1 := by
  have h : box = Set.pi univ fun _ : Fin 2 => Ioc (0 : ℝ) 1 := by
    ext x; simp [box, Set.mem_pi]
  rw [h, volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))

/-- The `K × K` components of a continuous function are continuous in the radius. -/
lemma continuous_kkCoeff {f : SL2R → ℂ} (hf : Continuous f) (n : Fin 2 → ℤ) :
    Continuous (kkCoeff f n) := by
  have hfun : kkCoeff f n = fun ξ => ∫ x in Icc (0 : Fin 2 → ℝ) 1,
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * kkProfile f ξ x :=
    funext fun ξ => setIntegral_congr_set box_ae_eq_Icc
  rw [hfun]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  have h1 : Continuous fun p : ℝ × (Fin 2 → ℝ) =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * ((p.2 i : ℝ) : ℂ))) := by fun_prop
  have h2 : Continuous fun p : ℝ × (Fin 2 → ℝ) =>
      f (rot (2 * π * p.2 0) * aR p.1 * rot (2 * π * p.2 1)) := by
    refine hf.comp (((continuous_rot.comp ?_).mul (continuous_aR.comp continuous_fst)).mul
      (continuous_rot.comp ?_)) <;> fun_prop
  exact h1.mul h2

/-- The `K × K` component as a vector of `L²(0, ∞)`: `√(sinh ξ) f_m(ξ)`. -/
def kkSrc (f : SL2R → ℂ) (m : Fin 2 → ℤ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * kkCoeff f m ξ

lemma summable_kkCoeff {f : SL2R → ℂ} (hf : Continuous f) (ξ : ℝ) :
    Summable fun n : Fin 2 → ℤ => ‖kkCoeff f n ξ‖ ^ 2 :=
  (hasSum_sq_box (continuous_kkProfile hf ξ)).summable

lemma norm_sq_kkSrc (f : SL2R → ℂ) (m : Fin 2 → ℤ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖kkSrc f m ξ‖ ^ 2 = Real.sinh ξ * ‖kkCoeff f m ξ‖ ^ 2 := by
  rw [kkSrc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Real.sinh_pos_iff.2 hξ).le]

lemma continuous_kkSrc {f : SL2R → ℂ} (hf : Continuous f) (m : Fin 2 → ℤ) :
    Continuous (kkSrc f m) :=
  (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_sinh)).mul
    (continuous_kkCoeff hf m)

/-- The square integral of a square-integrable function as an `ENNReal` integral. -/
lemma lintegral_norm_sq_lt_top {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) :
    ∫⁻ g, ENNReal.ofReal (‖f g‖ ^ 2) ∂haarR < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).1 hf
  have := hi.2
  rw [HasFiniteIntegral] at this
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun g => ?_)) this
  rw [Real.enorm_of_nonneg (by positivity)]

/-- **The summed components**: `∫₀^∞ sinh ξ · ∑_m |f_m(ξ)|²` is finite and
`(2π)² ∫₀^∞ sinh ξ ∑_m |f_m(ξ)|² dξ = ∫ |f|² d haarR`, in `ENNReal`. -/
lemma lintegral_tsum_kkSrc {f : SL2R → ℂ} (hfc : Continuous f) :
    ENNReal.ofReal ((2 * π) ^ 2) *
      ∑' m : Fin 2 → ℤ, ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) =
      ∫⁻ g, ENNReal.ofReal (‖f g‖ ^ 2) ∂haarR := by
  have hm : ∀ m, Measurable fun ξ => ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) := fun m =>
    ((continuous_kkSrc hfc m).norm.pow 2).measurable.ennreal_ofReal
  have hmt : Measurable fun ξ => ∑' m, ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) :=
    Measurable.ennreal_tsum hm
  rw [lintegral_norm_sq_eq_kk hfc, ← lintegral_tsum fun m => (hm m).aemeasurable,
    ← lintegral_const_mul _ hmt]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  simp only [norm_sq_kkSrc f _ hξ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (Real.sinh_pos_iff.2 hξ).le (sq_nonneg _))
    ((summable_kkCoeff hfc ξ).mul_left _), tsum_mul_left, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (Real.sinh_pos_iff.2 hξ).le]
  congr 1
  ring

end Lightlike.Lorentz.SL2RPlancherel
