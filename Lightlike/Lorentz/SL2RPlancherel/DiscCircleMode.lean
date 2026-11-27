module

public import Mathlib

/-!
# The Fourier modes of a holomorphic function on the unit disc

For `h` holomorphic on the open unit disc, the Cauchy power series `cauchyPowerSeries h 0 s` is the Taylor series of `h`
at `0` for every radius `0 < s < 1` (`cauchyPowerSeries_eq`), so its coefficient `discCoeff h m` does not depend on `s`,
and the `m`-th Fourier mode of `h` on the circle of radius `s` is `∫_{-π}^{π} h(s e^{iθ}) e^{-imθ} dθ = 2π s^m discCoeff h m`
(`integral_circle_mode`). In particular `h = 0` when all the coefficients vanish (`eq_zero_of_discCoeff_eq_zero`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The `m`-th Taylor coefficient at `0`** of a function holomorphic on the unit disc, as the coefficient of the Cauchy
power series of radius `1/2`. -/
def discCoeff (h : ℂ → ℂ) (m : ℕ) : ℂ :=
  cauchyPowerSeries h 0 (1 / 2) m (fun _ => (1 : ℂ))

lemma hasFPowerSeriesOnBall_cauchy {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasFPowerSeriesOnBall h (cauchyPowerSeries h 0 s) 0 (Real.toNNReal s) := by
  have hdc : DiffContOnCl ℂ h (ball (0 : ℂ) (Real.toNNReal s)) := by
    rw [Real.coe_toNNReal _ hs.1.le]
    exact (hh.mono (closedBall_subset_ball hs.2)).diffContOnCl_ball subset_rfl
  have := hdc.hasFPowerSeriesOnBall (by simpa using hs.1)
  rwa [Real.coe_toNNReal _ hs.1.le] at this

/-- The Cauchy power series of every radius `s ∈ (0, 1)` is the same formal series. -/
lemma cauchyPowerSeries_eq {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {s s' : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hs' : s' ∈ Ioo (0 : ℝ) 1) :
    cauchyPowerSeries h 0 s = cauchyPowerSeries h 0 s' := by
  have h1 := (hasFPowerSeriesOnBall_cauchy hh hs).hasFPowerSeriesAt
  have h2 := (hasFPowerSeriesOnBall_cauchy hh hs').hasFPowerSeriesAt
  exact h1.eq_formalMultilinearSeries h2

lemma cauchyPowerSeries_apply_eq {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (m : ℕ) (w : ℂ) :
    cauchyPowerSeries h 0 s m (fun _ => w) = w ^ m * discCoeff h m := by
  have hs0 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  rw [cauchyPowerSeries_eq hh hs hs0]
  have h2 := (cauchyPowerSeries h 0 (1 / 2) m).map_smul_univ (fun _ => w) (fun _ => (1 : ℂ))
  simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  rw [h2]
  rfl

lemma integrand_mode (h : ℂ → ℂ) (m : ℕ) {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    deriv (circleMap 0 s) θ • ((1 / (circleMap 0 s θ - 0)) ^ m • (circleMap 0 s θ - 0)⁻¹ • h (circleMap 0 s θ)) =
      Complex.I * ((s : ℂ) ^ m)⁻¹ * (h (circleMap 0 s θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) := by
  rw [deriv_circleMap]
  simp only [circleMap, zero_add, sub_zero, smul_eq_mul]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have he : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hm : Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) = (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ ^ m := by
    rw [← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; ring
  rw [hm]
  simp only [div_pow, one_pow, mul_pow]
  field_simp
  have hem : Complex.exp ((θ : ℂ) * Complex.I) ^ m * (1 / Complex.exp ((θ : ℂ) * Complex.I)) ^ m = 1 := by
    rw [← mul_pow, mul_one_div_cancel he, one_pow]
  linear_combination (-(h ((s : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))) * hem

/-- **The Fourier modes of a holomorphic function on a circle inside the disc**:
`∫_0^{2π} h(s e^{iθ}) e^{-imθ} dθ = 2π s^m discCoeff h m`. -/
lemma integral_circleMap_mode {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) (m : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 s θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
      (2 * π : ℂ) * ((s : ℂ) ^ m * discCoeff h m) := by
  have h1 := cauchyPowerSeries_apply_eq hh hs m 1
  rw [cauchyPowerSeries_apply] at h1
  simp only [circleIntegral, one_div, one_pow, one_mul, smul_eq_mul] at h1
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.1.ne'
  have h2 : ∀ θ : ℝ, deriv (circleMap 0 s) θ * ((circleMap 0 s θ - 0)⁻¹ ^ m * ((circleMap 0 s θ - 0)⁻¹ * h (circleMap 0 s θ))) =
      Complex.I * ((s : ℂ) ^ m)⁻¹ * (h (circleMap 0 s θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) := by
    intro θ
    have := integrand_mode h m hs.1 θ
    simpa only [one_div, smul_eq_mul] using this
  simp only [h2, intervalIntegral.integral_const_mul] at h1
  have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hsm : ((s : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hs0
  rw [← h1]
  generalize (∫ θ in (0 : ℝ)..2 * π, h (circleMap 0 s θ) *
    Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) = J
  field_simp

/-- The same on the polar parametrisation `θ ∈ (-π, π)` used for the integral over the disc. -/
lemma integral_polar_mode {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) (m : ℕ) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ θ in Ioo (-π) π, h (Complex.polarCoord.symm (s, θ)) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) =
      (2 * π : ℂ) * ((s : ℂ) ^ m * discCoeff h m) := by
  rw [← integral_circleMap_mode hh m hs]
  have hper : Function.Periodic (fun θ : ℝ => h (circleMap 0 s θ) *
      Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I))) (2 * π) := by
    intro θ
    have hc := periodic_circleMap (0 : ℂ) s θ
    simp only [hc]
    congr 1
    have : -((m : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * Complex.I) =
        -((m : ℂ) * (θ : ℂ) * Complex.I) + ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h1 := hper.intervalIntegral_add_eq 0 (-π)
  simp only [zero_add] at h1
  rw [h1, show -π + 2 * π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  simp only [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, zero_add]

/-- **A holomorphic function on the disc with vanishing Taylor coefficients vanishes.** -/
lemma eq_zero_of_discCoeff_eq_zero {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1))
    (h0 : ∀ m, discCoeff h m = 0) : ∀ w ∈ ball (0 : ℂ) 1, h w = 0 := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  set s : ℝ := (‖w‖ + 1) / 2 with hsdef
  have hs : s ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [hsdef]; linarith⟩
  have hws : w ∈ ball (0 : ℂ) (Real.toNNReal s) := by
    rw [mem_ball_zero_iff, Real.coe_toNNReal _ hs.1.le, hsdef]; linarith [norm_nonneg w]
  have hP := (hasFPowerSeriesOnBall_cauchy hh hs).hasSum (y := w) (by simpa using hws)
  have hz : ∀ m, cauchyPowerSeries h 0 s m (fun _ => w) = 0 := by
    intro m; rw [cauchyPowerSeries_apply_eq hh hs m w, h0 m, mul_zero]
  simp only [hz, zero_add] at hP
  exact (hasSum_zero.unique hP).symm

/-- **The monomial `c w^k` has the Taylor coefficient `c` in degree `k`.** -/
lemma discCoeff_monomial (c : ℂ) (k : ℕ) : discCoeff (fun w => c * w ^ k) k = c := by
  have hh : DifferentiableOn ℂ (fun w : ℂ => c * w ^ k) (ball (0 : ℂ) 1) :=
    ((differentiable_const c).mul (differentiable_id.pow k)).differentiableOn
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := integral_circleMap_mode hh k hs
  have h2 : ∀ θ : ℝ, c * circleMap 0 (1 / 2) θ ^ k * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) =
      c * (((1 / 2 : ℝ) : ℂ)) ^ k := by
    intro θ
    simp only [circleMap, zero_add, mul_pow]
    have : Complex.exp ((θ : ℂ) * Complex.I) ^ k * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      rw [show (k : ℂ) * ((θ : ℂ) * Complex.I) + -((k : ℂ) * (θ : ℂ) * Complex.I) = 0 by ring]
      simp
    linear_combination (c * (((1 / 2 : ℝ) : ℂ)) ^ k) * this
  beta_reduce at h1
  simp only [h2, intervalIntegral.integral_const, sub_zero, Complex.real_smul] at h1
  have hpi : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this]
  have hs0 : (((1 / 2 : ℝ) : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hne : (2 * (π : ℂ)) * (((1 / 2 : ℝ) : ℂ)) ^ k ≠ 0 := mul_ne_zero hpi hs0
  have h3 : (2 * (π : ℂ)) * (((1 / 2 : ℝ) : ℂ)) ^ k * c =
      (2 * (π : ℂ)) * (((1 / 2 : ℝ) : ℂ)) ^ k * discCoeff (fun w => c * w ^ k) k := by
    push_cast at h1 ⊢
    linear_combination h1
  exact (mul_left_cancel₀ hne h3).symm

/-- The Taylor coefficients depend only on the values on the open disc. -/
lemma discCoeff_congr {h h' : ℂ → ℂ} (heq : EqOn h h' (ball (0 : ℂ) 1)) (m : ℕ) :
    discCoeff h m = discCoeff h' m := by
  unfold discCoeff
  rw [cauchyPowerSeries_apply, cauchyPowerSeries_apply]
  congr 1
  refine circleIntegral.integral_congr (by norm_num) (fun z hz => ?_)
  have hz1 : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    have := mem_sphere_zero_iff_norm.1 hz
    rw [this]; norm_num
  simp only [heq hz1]

/-- **The Taylor coefficients of a function given by a power series on the unit ball.** -/
lemma discCoeff_eq_of_hasFPowerSeriesOnBall {h : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) (hp : HasFPowerSeriesOnBall h p 0 1) (k : ℕ) :
    discCoeff h k = p k (fun _ => (1 : ℂ)) := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := (hasFPowerSeriesOnBall_cauchy hh hs).hasFPowerSeriesAt
  have h2 := hp.hasFPowerSeriesAt
  have h3 := h1.eq_formalMultilinearSeries h2
  unfold discCoeff
  rw [h3]

end Lightlike.Lorentz.SL2RPlancherel
