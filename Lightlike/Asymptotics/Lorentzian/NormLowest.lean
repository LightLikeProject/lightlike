import Lightlike.Asymptotics.Lorentzian.LinkIntegral
import Lightlike.Asymptotics.Lorentzian.RadialBeta

/-!
# The norm of the lowest-level vector of the principal series

`‖tlin n 0 ρ e₀‖² = π/(n+1)`: the explicit constant of `link_integral`.
-/

open Matrix Complex MeasureTheory
open scoped ComplexConjugate InnerProductSpace
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz

namespace Lightlike.Asymptotics.Lorentzian

/-- **The modulus of the weight on the chart**: `‖wgt p q ρ z‖² = (1 + ‖z‖²)^{-2-(p+q)}`; the
imaginary part of the exponent drops out of the modulus. -/
theorem norm_sq_wgt (p q : ℕ) (ρ : ℝ) (z : ℂ) :
    ‖wgt p q ρ z‖ ^ 2 = (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ) - (p + q : ℕ)) := by
  have hx : 0 < 1 + ‖z‖ ^ 2 := by positivity
  unfold wgt
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub, Complex.one_re]
  rw [sqrt_inv_pow_eq_rpow hx, ← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- The first basis vector is the coherent state of the identity. -/
theorem bv_zero_eq_cohState (n p q : ℕ) (hp : p = n) (hq : q = 0) :
    (bv (0 : Fin (p + q + 1)) : Fin (p + q + 1) → ℂ) =
      fun k : Fin (p + q + 1) => cohState n (1 : Matrix (Fin 2) (Fin 2) ℂ) (Fin.cast (by omega) k) := by
  subst hp hq
  funext k
  simp [cohState, spinMat_one, bv, Matrix.one_apply, eq_comm]

/-- **`tlin` on the first basis vector**: `tfun e₀ (z) = wgt z · z^n`. -/
theorem tfun_bv_zero (n : ℕ) (ρ : ℝ) (z : ℂ) :
    tfun (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ (bv 0) z =
      wgt (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ z * z ^ n := by
  have hp : 0 + p0 (n : ℤ) = n := by simp [p0]
  have hq : 0 + q0 (n : ℤ) = 0 := by simp [q0]
  unfold tfun
  rw [chart_hvec]
  congr 1
  rw [bv_zero_eq_cohState n _ _ hp hq, lam_emb_cohState_cast n _ _ hp hq]
  simp

end Lightlike.Asymptotics.Lorentzian
