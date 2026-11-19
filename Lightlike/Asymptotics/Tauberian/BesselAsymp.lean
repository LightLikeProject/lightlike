import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Laplace's method for `∫₀^π e^{-z (1 - cos θ)} cos θ dθ`

`√z ∫₀^π e^{-z(1 - cos θ)} cos θ dθ → √(π/2)` as `z → ∞` (substitute `θ = u/√z` and use dominated
convergence with the bound `1 - cos s ≥ 2 s²/π²`, `|s| ≤ π`). With the series for `I₁` this gives
`I₁(z) ~ e^z / √(2π z)`, the asymptotics of the crossing kernel.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- `∫₀^π e^{-z (1 - cos θ)} cos θ dθ`. -/
def cosLaplace (z : ℝ) : ℝ := ∫ θ in (0 : ℝ)..π, Real.exp (-z * (1 - Real.cos θ)) * Real.cos θ

/-- The rescaled integrand `1_{u ≤ π√z} e^{-z (1 - cos (u/√z))} cos (u/√z)`. -/
def cosLaplaceScaled (z u : ℝ) : ℝ :=
  (Ioc (0 : ℝ) (π * Real.sqrt z)).indicator
    (fun u => Real.exp (-z * (1 - Real.cos (u / Real.sqrt z))) * Real.cos (u / Real.sqrt z)) u

lemma sqrt_mul_cosLaplace {z : ℝ} (hz : 0 < z) :
    Real.sqrt z * cosLaplace z = ∫ u in Ioi (0 : ℝ), cosLaplaceScaled z u := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  unfold cosLaplaceScaled cosLaplace
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.2 Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (by positivity)]
  have := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := π) (fun u : ℝ => Real.exp (-z * (1 - Real.cos (u / Real.sqrt z))) *
      Real.cos (u / Real.sqrt z)) hs.ne'
  have e : ∀ θ : ℝ, Real.exp (-z * (1 - Real.cos (Real.sqrt z * θ / Real.sqrt z))) *
      Real.cos (Real.sqrt z * θ / Real.sqrt z) = Real.exp (-z * (1 - Real.cos θ)) * Real.cos θ := by
    intro θ; rw [mul_div_cancel_left₀ _ hs.ne']
  simp only [e, mul_zero, smul_eq_mul] at this
  rw [mul_comm π, this, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

lemma sin_eq_mul_sinc (x : ℝ) : Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]; field_simp

lemma one_sub_cos_eq (s : ℝ) : 1 - Real.cos s = s ^ 2 / 2 * Real.sinc (s / 2) ^ 2 := by
  have h1 : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    ring_nf
  rw [h1, sin_eq_mul_sinc (s / 2)]
  ring

lemma tendsto_scaled_exponent (u : ℝ) :
    Tendsto (fun z : ℝ => z * (1 - Real.cos (u / Real.sqrt z))) atTop (𝓝 (u ^ 2 / 2)) := by
  have hs : Tendsto (fun z : ℝ => u / (2 * Real.sqrt z)) atTop (𝓝 0) := by
    have : Tendsto (fun z : ℝ => 2 * Real.sqrt z) atTop atTop :=
      (Filter.Tendsto.const_mul_atTop two_pos Real.tendsto_sqrt_atTop)
    exact this.const_div_atTop u
  have hc := ((Real.continuous_sinc.tendsto 0).comp hs)
  rw [Real.sinc_zero] at hc
  have h2 := (hc.pow 2).const_mul (u ^ 2 / 2)
  rw [one_pow, mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  have hs0 : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  rw [one_sub_cos_eq]
  simp only [Function.comp]
  have e : u / Real.sqrt z / 2 = u / (2 * Real.sqrt z) := by field_simp
  rw [e]
  have e2 : z * ((u / Real.sqrt z) ^ 2 / 2 * Real.sinc (u / (2 * Real.sqrt z)) ^ 2) =
      u ^ 2 / 2 * Real.sinc (u / (2 * Real.sqrt z)) ^ 2 := by
    have : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz.le
    field_simp
    rw [this]; ring
  rw [e2]

lemma abs_cosLaplaceScaled_le {z : ℝ} (hz : 0 < z) (u : ℝ) :
    ‖cosLaplaceScaled z u‖ ≤ Real.exp (-(2 / π ^ 2) * u ^ 2) := by
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  unfold cosLaplaceScaled
  by_cases hu : u ∈ Ioc (0 : ℝ) (π * Real.sqrt z)
  · rw [Set.indicator_of_mem hu, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 : |u / Real.sqrt z| ≤ π := by
      rw [abs_of_pos (div_pos hu.1 hs), div_le_iff₀ hs]; exact hu.2
    have h2 := Real.cos_le_one_sub_mul_cos_sq h1
    have hz2 : z * (u / Real.sqrt z) ^ 2 = u ^ 2 := by
      rw [div_pow, Real.sq_sqrt hz.le]; field_simp
    have h3 : Real.exp (-z * (1 - Real.cos (u / Real.sqrt z))) ≤ Real.exp (-(2 / π ^ 2) * u ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have : (2 / π ^ 2) * (u / Real.sqrt z) ^ 2 ≤ 1 - Real.cos (u / Real.sqrt z) := by linarith
      have e : (2 / π ^ 2) * u ^ 2 = z * ((2 / π ^ 2) * (u / Real.sqrt z) ^ 2) := by
        rw [← hz2]; ring
      nlinarith [mul_le_mul_of_nonneg_left this hz.le, e]
    calc Real.exp (-z * (1 - Real.cos (u / Real.sqrt z))) * ‖Real.cos (u / Real.sqrt z)‖
        ≤ Real.exp (-(2 / π ^ 2) * u ^ 2) * 1 :=
          mul_le_mul h3 (by simpa using Real.abs_cos_le_one _) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hu]; simpa using (Real.exp_pos _).le

/-- **Laplace's method.** `√z ∫₀^π e^{-z(1 - cos θ)} cos θ dθ → √(π/2)`. -/
theorem tendsto_sqrt_mul_cosLaplace :
    Tendsto (fun z : ℝ => Real.sqrt z * cosLaplace z) atTop (𝓝 (Real.sqrt (π / 2))) := by
  have hlim : Tendsto (fun z : ℝ => ∫ u in Ioi (0 : ℝ), cosLaplaceScaled z u) atTop
      (𝓝 (∫ u in Ioi (0 : ℝ), Real.exp (-(1 / 2) * u ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => Real.exp (-(2 / π ^ 2) * u ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards with z
      unfold cosLaplaceScaled
      exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-z * (1 - Real.cos (u / Real.sqrt z))) *
        Real.cos (u / Real.sqrt z)).measurable.indicator measurableSet_Ioc |>.aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      exact Eventually.of_forall fun u => abs_cosLaplaceScaled_le hz u
    · exact (integrable_exp_neg_mul_sq (by positivity : 0 < 2 / π ^ 2)).integrableOn
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu
      have hexp := ((Real.continuous_exp.tendsto _).comp (tendsto_scaled_exponent u).neg)
      have hcos : Tendsto (fun z : ℝ => Real.cos (u / Real.sqrt z)) atTop (𝓝 1) := by
        have h0 : Tendsto (fun z : ℝ => u / Real.sqrt z) atTop (𝓝 0) :=
          Real.tendsto_sqrt_atTop.const_div_atTop u
        have := (Real.continuous_cos.tendsto 0).comp h0
        rwa [Real.cos_zero] at this
      have hprod := hexp.mul hcos
      rw [mul_one] at hprod
      have hbig : ∀ᶠ z : ℝ in atTop, u ≤ π * Real.sqrt z :=
        (Filter.Tendsto.const_mul_atTop Real.pi_pos Real.tendsto_sqrt_atTop).eventually_ge_atTop u
      have hlim' : Tendsto (fun z : ℝ => cosLaplaceScaled z u) atTop
          (𝓝 (Real.exp (-(u ^ 2 / 2)))) := by
        refine hprod.congr' ?_
        filter_upwards [hbig] with z hz
        unfold cosLaplaceScaled
        rw [Set.indicator_of_mem (show u ∈ Ioc (0 : ℝ) (π * Real.sqrt z) from ⟨hu0, hz⟩)]
        simp only [Function.comp, neg_mul]
      convert hlim' using 2
      ring
  rw [show Real.sqrt (π / 2) = ∫ u in Ioi (0 : ℝ), Real.exp (-(1 / 2) * u ^ 2) by
    rw [integral_gaussian_Ioi]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    rw [show π / (1 / 2) = 2 * π by ring, show π / 2 = 2 * π / 4 by ring,
      Real.sqrt_div (by positivity), h4]]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  exact (sqrt_mul_cosLaplace hz).symm

end Lightlike.Tauberian
