module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.LadderComponents

/-!
# The `K × K` components of mixed parity vanish

The central element `k_π = -1` of `SL(2,ℝ)` gives `k_{α+π} a(ξ) k_{θ-π} = k_α a(ξ) k_θ`, so the
`(m, n)`-th Fourier component `f_{m,n}` of every continuous `f` vanishes when `m - n` is odd
(`kkCoeff_eq_zero_of_odd`).  The nonzero components are the even ones (both `m` and `n` even,
integer `K`-types) and the odd ones (both odd, half-integer `K`-types).  Layer 2c-iii of the
Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The integrand of `f_{m,n}(ξ)` in the angles `(a, b)`, `α = 2π a`, `θ = 2π b`. -/
def kkInt (f : SL2R → ℂ) (m n : ℤ) (ξ a b : ℝ) : ℂ :=
  torusChar m n a b * f (rot (2 * π * a) * aR ξ * rot (2 * π * b))

lemma continuous_kkInt {f : SL2R → ℂ} (hf : Continuous f) (m n : ℤ) (ξ : ℝ) :
    Continuous fun p : ℝ × ℝ => kkInt f m n ξ p.1 p.2 := by
  unfold kkInt
  refine (continuous_torusChar m n).mul (hf.comp ?_)
  exact ((continuous_rot.comp (continuous_const.mul continuous_fst)).mul continuous_const).mul
    (continuous_rot.comp (continuous_const.mul continuous_snd))

lemma kkCoeff_eq_iter {f : SL2R → ℂ} (hf : Continuous f) (m n : ℤ) (ξ : ℝ) :
    kkCoeff f ![m, n] ξ = ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, kkInt f m n ξ a b := by
  have hc : Continuous fun x : Fin 2 → ℝ =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, ((![m, n] i : ℤ) : ℂ) * (x i : ℂ))) *
        kkProfile f ξ x := by
    have h1 := continuous_kkProfile hf ξ
    have h2 : Continuous fun x : Fin 2 → ℝ =>
        Complex.exp (-(2 * π * Complex.I * ∑ i, ((![m, n] i : ℤ) : ℂ) * (x i : ℂ))) := by
      simp only [Fin.sum_univ_two]
      exact Complex.continuous_exp.comp (by fun_prop)
    exact h2.mul h1
  unfold kkCoeff
  rw [integral_box_eq hc]
  simp [kkInt, kkProfile, torusChar, Fin.sum_univ_two]

lemma kkInt_add_one_left (f : SL2R → ℂ) (m n : ℤ) (ξ a b : ℝ) :
    kkInt f m n ξ (a + 1) b = kkInt f m n ξ a b := by
  unfold kkInt torusChar
  have h1 : rot (2 * π * (a + 1)) = rot (2 * π * a) := by
    rw [mul_add, mul_one]
    exact rot_periodic (2 * π * a)
  have h2 : Complex.exp (-(2 * π * Complex.I * (m * ((a + 1 : ℝ) : ℂ) + n * b))) =
      Complex.exp (-(2 * π * Complex.I * (m * (a : ℂ) + n * b))) := by
    have : -(2 * π * Complex.I * (m * ((a + 1 : ℝ) : ℂ) + n * b)) =
        -(2 * π * Complex.I * (m * (a : ℂ) + n * b)) + ((-m : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, h2]

lemma kkInt_add_one_right (f : SL2R → ℂ) (m n : ℤ) (ξ a b : ℝ) :
    kkInt f m n ξ a (b + 1) = kkInt f m n ξ a b := by
  unfold kkInt torusChar
  have h1 : rot (2 * π * (b + 1)) = rot (2 * π * b) := by
    rw [mul_add, mul_one]
    exact rot_periodic (2 * π * b)
  have h2 : Complex.exp (-(2 * π * Complex.I * (m * (a : ℂ) + n * ((b + 1 : ℝ) : ℂ)))) =
      Complex.exp (-(2 * π * Complex.I * (m * (a : ℂ) + n * b))) := by
    have : -(2 * π * Complex.I * (m * (a : ℂ) + n * ((b + 1 : ℝ) : ℂ))) =
        -(2 * π * Complex.I * (m * (a : ℂ) + n * b)) + ((-n : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, h2]

/-- The half-turn symmetry for odd `m - n`: `E(a + 1/2, b - 1/2) = -E(a, b)`. -/
lemma kkInt_half_shift_odd (f : SL2R → ℂ) {m n : ℤ} (h : Odd (m - n)) (ξ a b : ℝ) :
    kkInt f m n ξ (a + 1 / 2) (b + -(1 / 2)) = -kkInt f m n ξ a b := by
  have hrot : rot (2 * π * (a + 1 / 2)) * aR ξ * rot (2 * π * (b + -(1 / 2))) =
      rot (2 * π * a) * aR ξ * rot (2 * π * b) := by
    have e1 : rot (2 * π * (a + 1 / 2)) = rot (2 * π * a) * rot π := by
      rw [← rot_add]; congr 1; ring
    have e2 : rot (2 * π * (b + -(1 / 2))) = rot (-π) * rot (2 * π * b) := by
      rw [← rot_add]; congr 1; ring
    have e3 : rot π * rot (-π) = 1 := rot_mul_rot_neg π
    calc rot (2 * π * (a + 1 / 2)) * aR ξ * rot (2 * π * (b + -(1 / 2)))
        = rot (2 * π * a) * (rot π * aR ξ) * (rot (-π) * rot (2 * π * b)) := by
          rw [e1, e2]; simp only [mul_assoc]
      _ = rot (2 * π * a) * (aR ξ * rot π) * (rot (-π) * rot (2 * π * b)) := by
          rw [rot_pi_mul_comm_aR]
      _ = rot (2 * π * a) * aR ξ * (rot π * rot (-π)) * rot (2 * π * b) := by
          simp only [mul_assoc]
      _ = _ := by rw [e3, mul_one]
  obtain ⟨k, hk⟩ := h
  unfold kkInt torusChar
  rw [hrot]
  have hsc : Complex.exp (-(2 * π * Complex.I * (m * ((a + 1 / 2 : ℝ) : ℂ) + n * ((b + -(1 / 2) : ℝ) : ℂ)))) =
      -Complex.exp (-(2 * π * Complex.I * (m * (a : ℂ) + n * b))) := by
    have hmn : (m : ℂ) - n = 2 * k + 1 := by exact_mod_cast hk
    have : -(2 * π * Complex.I * (m * ((a + 1 / 2 : ℝ) : ℂ) + n * ((b + -(1 / 2) : ℝ) : ℂ))) =
        -(2 * π * Complex.I * (m * (a : ℂ) + n * b)) + ((-k : ℤ) : ℂ) * (2 * π * Complex.I) +
          -(π * Complex.I) := by
      push_cast
      linear_combination (-(π : ℂ) * Complex.I) * hmn
    have hneg : Complex.exp (-(π * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, hneg]
    ring
  rw [hsc]
  ring

/-- Shifting a continuous `1`-periodic function does not change its integral over a period. -/
lemma integral_Ioc_shift_periodic {φ : ℝ → ℂ} (hφ : Function.Periodic φ 1) (c : ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, φ (x + c) = ∫ x in Ioc (0 : ℝ) 1, φ x := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right (fun x => φ x) c]
  have := hφ.intervalIntegral_add_eq (0 + c) 0
  simpa [add_comm] using this

/-- **Components of mixed parity vanish**: `f_{m,n} = 0` when `m - n` is odd, for continuous `f`. -/
theorem kkCoeff_eq_zero_of_odd {f : SL2R → ℂ} (hf : Continuous f) {m n : ℤ} (h : Odd (m - n))
    (ξ : ℝ) : kkCoeff f ![m, n] ξ = 0 := by
  rw [kkCoeff_eq_iter hf]
  set E := kkInt f m n ξ with hE
  -- the inner integral shifted by `-1/2`
  have hper_b : ∀ a, Function.Periodic (fun b => E a b) 1 := fun a b => kkInt_add_one_right f m n ξ a b
  have h1 : ∀ a, ∫ b in Ioc (0 : ℝ) 1, E a (b + -(1 / 2)) = ∫ b in Ioc (0 : ℝ) 1, E a b :=
    fun a => integral_Ioc_shift_periodic (hper_b a) _
  set Φ : ℝ → ℂ := fun a => ∫ b in Ioc (0 : ℝ) 1, E a (b + -(1 / 2)) with hΦ
  have hΦper : Function.Periodic Φ 1 := by
    intro a
    simp only [hΦ, hE]
    exact integral_congr_ae (Filter.Eventually.of_forall fun b => kkInt_add_one_left f m n ξ a _)
  have h2 : ∫ a in Ioc (0 : ℝ) 1, Φ (a + 1 / 2) = ∫ a in Ioc (0 : ℝ) 1, Φ a :=
    integral_Ioc_shift_periodic hΦper _
  have h3 : ∀ a, Φ (a + 1 / 2) = -∫ b in Ioc (0 : ℝ) 1, E a b := by
    intro a
    simp only [hΦ, hE]
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun b => kkInt_half_shift_odd f h ξ a b)
  have h4 : ∫ a in Ioc (0 : ℝ) 1, Φ a = ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, E a b :=
    integral_congr_ae (Filter.Eventually.of_forall h1)
  simp_rw [h3] at h2
  rw [integral_neg, h4] at h2
  have : (2 : ℂ) * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, E a b = 0 := by
    linear_combination -h2
  simpa using this

end Lightlike.Lorentz.SL2R
