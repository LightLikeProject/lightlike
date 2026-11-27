module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileODE

/-!
# The radial profiles of the discrete series are real

The Taylor coefficients at `0` of a function `h` holomorphic on the unit disc with `h (conj w) = conj (h w)` are
real (`conj_discCoeff`). The generating function `(t + w)^l (1 + t w)^{-(n+l)}` of the profile polynomials has this
symmetry for real `t`, so `P_{jl}(t)` is real (`conj_profPoly`) and the profile `κ cosh(ξ/2)^{-n} P_{jl}(tanh(ξ/2))` is
real for real `κ` (`conj_profileFun`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Real Taylor coefficients**: if `h (conj w) = conj (h w)` on the unit disc, the Taylor coefficients of `h` at `0`
are real. -/
theorem conj_discCoeff {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball (0 : ℂ) 1))
    (hreal : ∀ w ∈ ball (0 : ℂ) 1, h ((starRingEnd ℂ) w) = (starRingEnd ℂ) (h w)) (m : ℕ) :
    (starRingEnd ℂ) (discCoeff h m) = discCoeff h m := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 := integral_circleMap_mode hh m hs
  set g : ℝ → ℂ := fun θ => h (circleMap 0 (1 / 2) θ) * Complex.exp (-((m : ℂ) * (θ : ℂ) * Complex.I)) with hg
  have hmem : ∀ θ : ℝ, circleMap 0 (1 / 2) θ ∈ ball (0 : ℂ) 1 := fun θ => by
    rw [mem_ball_zero_iff, norm_circleMap_zero]; norm_num
  -- `g (2π - θ) = conj (g θ)`
  have hsym : ∀ θ : ℝ, g (2 * π - θ) = (starRingEnd ℂ) (g θ) := by
    intro θ
    have e1 : Complex.exp (((2 * π - θ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((starRingEnd ℂ) ((θ : ℂ) * Complex.I)) := by
      have : ((2 * π - θ : ℝ) : ℂ) * Complex.I =
          (starRingEnd ℂ) ((θ : ℂ) * Complex.I) + ((1 : ℤ) : ℂ) * (2 * π * Complex.I) := by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hc : circleMap (0 : ℂ) (1 / 2) (2 * π - θ) = (starRingEnd ℂ) (circleMap 0 (1 / 2) θ) := by
      simp only [circleMap, zero_add]
      rw [map_mul, Complex.conj_ofReal, e1, Complex.exp_conj]
    simp only [hg]
    rw [hc, hreal _ (hmem θ), map_mul]
    congr 1
    rw [← Complex.exp_conj]
    have : -((m : ℂ) * ((2 * π - θ : ℝ) : ℂ) * Complex.I) =
        (starRingEnd ℂ) (-((m : ℂ) * (θ : ℂ) * Complex.I)) + ((-(m : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) := by
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hint : (starRingEnd ℂ) (∫ θ in (0 : ℝ)..2 * π, g θ) = ∫ θ in (0 : ℝ)..2 * π, g θ := by
    have hc2 : (starRingEnd ℂ) (∫ θ in (0 : ℝ)..2 * π, g θ) = ∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (g θ) := by
      rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity),
        ← integral_conj]
    rw [hc2]
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 2 * π) g (2 * π)
    simp only [sub_self, sub_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact (hsym θ).symm
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hpi
  have hpow : (((1 / 2 : ℝ) : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by norm_num))
  have h2 : (starRingEnd ℂ) (2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * discCoeff h m)) =
      2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * discCoeff h m) := by
    rw [← h1]; exact hint
  have hc3 : (starRingEnd ℂ) (2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * discCoeff h m)) =
      2 * π * (((1 / 2 : ℝ) : ℂ) ^ m * (starRingEnd ℂ) (discCoeff h m)) := by
    simp [map_mul, map_pow, map_inv₀, map_ofNat, Complex.conj_ofReal]
  rw [hc3] at h2
  exact mul_left_cancel₀ hpow (mul_left_cancel₀ h2pi h2)

lemma genFun_conj (n l : ℕ) (t : ℝ) (w : ℂ) :
    genFun n l t ((starRingEnd ℂ) w) = (starRingEnd ℂ) (genFun n l t w) := by
  simp [genFun, map_pow, map_inv₀, Complex.conj_ofReal]

/-- **The profile polynomials are real** for real `t`, `|t| < 1`. -/
theorem conj_profPoly (n l j : ℕ) {t : ℝ} (ht : |t| < 1) :
    (starRingEnd ℂ) (profPoly n l j t) = profPoly n l j t :=
  conj_discCoeff (differentiableOn_genFun n l ht) (fun w _ => genFun_conj n l t w) j

/-- **The profile is real** for a real constant `κ`. -/
theorem conj_profileFun (n l j : ℕ) {κ : ℂ} (hκ : (starRingEnd ℂ) κ = κ) (ξ : ℝ) :
    (starRingEnd ℂ) (profileFun n l j κ ξ) = profileFun n l j κ ξ := by
  unfold profileFun
  rw [map_mul, map_mul, hκ, Complex.conj_ofReal, conj_profPoly n l j (abs_tanh_half_lt_one ξ)]

end Lightlike.Lorentz.SL2RPlancherel
