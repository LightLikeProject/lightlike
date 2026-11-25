import Lightlike.OperatorAlgebras.UnruhEffect.Rindler

/-!
# Unruh's analytic continuation of the Rindler mode

Row G1-049 (milestone SC1).  Use null coordinates `U = t - x` on the 1+1 Minkowski plane.  A Rindler mode of
frequency `ω > 0` (acceleration parameter `a > 0`) that depends on `U` only is, in the right wedge
(`U < 0`), `e^{-iωu}` with `u = -(1/a) log (-aU)`, i.e. `(-aU)^{iω/a}`.  The function
`F(U) = exp ((iω/a) Log (-aU))` (principal logarithm) is holomorphic for `Im U < 0`, which is the analytic
signature of a positive-frequency Minkowski mode (`e^{-iΩU}`, `Ω > 0`, is bounded there).  Its boundary
value on the positive axis `U > 0` (the left wedge) differs from the pure left Rindler mode by the factor
`e^{-πω/a}`.  This factor is what produces the Planck spectrum `1/(e^{2πω/a} - 1)`
(see `Lightlike.OperatorAlgebras.UnruhEffect.Bogoliubov`).

## Main statements

* `F_rindler_right`: in Rindler coordinates of the right wedge, `F(t - x) = e^{-iω(η - ξ)}`.
* `F_pos`: for `U > 0`, `F(U) = e^{-πω/a} · exp ((iω/a) ln (aU))`.
* `F_rindler_left`: in left Rindler coordinates, `F(t - x) = e^{-πω/a} e^{iω(η + ξ)}`.
* `differentiableOn_F`: `F` is holomorphic on the lower half plane.
-/

namespace Lightlike.OperatorAlgebras.UnruhEffect

open Real
open scoped Complex

/-- The Unruh mode `U ↦ exp ((iω/a) Log (-aU))`, continued through the lower half plane. -/
noncomputable def unruhMode (ω a : ℝ) (U : ℂ) : ℂ :=
  cexp (Complex.I * ω / a * Complex.log (-(a * U)))

/-- The principal logarithm of a negative real number. -/
theorem log_ofReal_neg {x : ℝ} (hx : x < 0) :
    Complex.log (x : ℂ) = (Real.log (-x) : ℂ) + (π : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, abs_of_neg hx, Real.log_neg_eq_log]
  · simp [Complex.log_im, Complex.arg_ofReal_of_neg hx]

/-- On the right wedge (`U < 0`) the mode is `exp ((iω/a) ln (-aU))`, the Rindler mode `e^{-iωu}`. -/
theorem unruhMode_neg {ω a : ℝ} (ha : 0 < a) {U : ℝ} (hU : U < 0) :
    unruhMode ω a (U : ℂ) = cexp (Complex.I * ω / a * (Real.log (-(a * U)) : ℂ)) := by
  unfold unruhMode
  have h : 0 < -(a * U) := by nlinarith
  rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_log h.le]

/-- **The mode on the left wedge**: for `U > 0`, `F(U) = e^{-πω/a} exp ((iω/a) ln (aU))`. -/
theorem unruhMode_pos {ω a : ℝ} (ha : 0 < a) {U : ℝ} (hU : 0 < U) :
    unruhMode ω a (U : ℂ) =
      (Real.exp (-(π * ω / a)) : ℂ) * cexp (Complex.I * ω / a * (Real.log (a * U) : ℂ)) := by
  unfold unruhMode
  have h : -(a * U) < 0 := by nlinarith
  have h2 : -((a : ℂ) * (U : ℂ)) = ((-(a * U) : ℝ) : ℂ) := by push_cast; ring
  rw [h2, log_ofReal_neg h, neg_neg, mul_add, Complex.exp_add, mul_comm]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp
  rw [Complex.I_sq]; ring

/-- **Right wedge in Rindler coordinates**: `F(t - x) = e^{-iω(η - ξ)}`, a pure positive-frequency
Rindler mode in the Rindler time `η` along the line `ξ`. -/
theorem unruhMode_rindler_right {ω a : ℝ} (ha : 0 < a) (η ξ : ℝ) :
    unruhMode ω a (((rindlerMap a η ξ).1 - (rindlerMap a η ξ).2 : ℝ) : ℂ) =
      cexp (-(Complex.I * ω * ((η : ℂ) - ξ))) := by
  have hU : (rindlerMap a η ξ).1 - (rindlerMap a η ξ).2 = -(exp (a * (ξ - η)) / a) := by
    simp only [rindlerMap]
    have : exp (a * (ξ - η)) = exp (a * ξ) * (cosh (a * η) - sinh (a * η)) := by
      rw [cosh_sub_sinh, ← Real.exp_add]; ring_nf
    rw [this]; ring
  have hneg : (rindlerMap a η ξ).1 - (rindlerMap a η ξ).2 < 0 := by
    rw [hU]; exact neg_neg_of_pos (div_pos (exp_pos _) ha)
  rw [unruhMode_neg ha hneg, hU]
  have : -(a * -(exp (a * (ξ - η)) / a)) = exp (a * (ξ - η)) := by field_simp
  rw [this, Real.log_exp]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp
  ring

/-- Left Rindler coordinates `t = (e^{aξ}/a) sinh (aη)`, `x = -(e^{aξ}/a) cosh (aη)` (the mirror wedge). -/
noncomputable def leftRindlerMap (a η ξ : ℝ) : ℝ × ℝ :=
  (exp (a * ξ) / a * sinh (a * η), -(exp (a * ξ) / a * cosh (a * η)))

/-- **Left wedge in Rindler coordinates**: `F(t - x) = e^{-πω/a} e^{iω(η + ξ)}`.  The second factor is the
complex conjugate of the positive-frequency left Rindler mode `e^{-iω(η+ξ)}`; the weight `e^{-πω/a}` is the
Bogoliubov ratio `|β / α|`. -/
theorem unruhMode_rindler_left {ω a : ℝ} (ha : 0 < a) (η ξ : ℝ) :
    unruhMode ω a (((leftRindlerMap a η ξ).1 - (leftRindlerMap a η ξ).2 : ℝ) : ℂ) =
      (Real.exp (-(π * ω / a)) : ℂ) * cexp (Complex.I * ω * ((η : ℂ) + ξ)) := by
  have hU : (leftRindlerMap a η ξ).1 - (leftRindlerMap a η ξ).2 = exp (a * (ξ + η)) / a := by
    simp only [leftRindlerMap]
    have : exp (a * (ξ + η)) = exp (a * ξ) * (cosh (a * η) + sinh (a * η)) := by
      rw [cosh_add_sinh, ← Real.exp_add]; ring_nf
    rw [this]; ring
  have hpos : 0 < (leftRindlerMap a η ξ).1 - (leftRindlerMap a η ξ).2 := by
    rw [hU]; exact div_pos (exp_pos _) ha
  rw [unruhMode_pos ha hpos, hU]
  have : a * (exp (a * (ξ + η)) / a) = exp (a * (ξ + η)) := by field_simp
  rw [this, Real.log_exp]
  congr 2
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  push_cast
  field_simp
  ring

/-- **Holomorphy in the lower half plane**: `F` is complex differentiable on `{Im U < 0}`, where
`-aU` lies in the upper half plane, inside the slit plane of the principal logarithm. -/
theorem differentiableOn_unruhMode (ω a : ℝ) (ha : 0 < a) :
    DifferentiableOn ℂ (unruhMode ω a) {U : ℂ | U.im < 0} := by
  intro U hU
  have hs : -((a : ℂ) * U) ∈ Complex.slitPlane := by
    right
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have : U.im < 0 := hU
    simp only [ne_eq]
    nlinarith
  have h1 : DifferentiableAt ℂ (fun U : ℂ => -((a : ℂ) * U)) U := by fun_prop
  have h2 := (Complex.differentiableAt_log hs).comp U h1
  have h3 : DifferentiableAt ℂ (unruhMode ω a) U := by
    unfold unruhMode
    exact DifferentiableAt.cexp ((differentiableAt_const _).mul h2)
  exact h3.differentiableWithinAt

end Lightlike.OperatorAlgebras.UnruhEffect

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.differentiableOn_unruhMode := _root_.Lightlike.OperatorAlgebras.UnruhEffect.differentiableOn_unruhMode
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.leftRindlerMap := _root_.Lightlike.OperatorAlgebras.UnruhEffect.leftRindlerMap
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.log_ofReal_neg := _root_.Lightlike.OperatorAlgebras.UnruhEffect.log_ofReal_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.unruhMode := _root_.Lightlike.OperatorAlgebras.UnruhEffect.unruhMode
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.unruhMode_neg := _root_.Lightlike.OperatorAlgebras.UnruhEffect.unruhMode_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.unruhMode_pos := _root_.Lightlike.OperatorAlgebras.UnruhEffect.unruhMode_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.unruhMode_rindler_left := _root_.Lightlike.OperatorAlgebras.UnruhEffect.unruhMode_rindler_left
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_049.unruhMode_rindler_right := _root_.Lightlike.OperatorAlgebras.UnruhEffect.unruhMode_rindler_right
