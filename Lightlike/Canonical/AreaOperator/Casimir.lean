import Lightlike.Canonical.AreaOperator.Spectrum
import Lightlike.Spin4.Ladder
import Lightlike.SU2.Completeness

/-!
# `casSqrt` is the square root of the `SU(2)` Casimir (row G2-012)

The area operator of `Area.lean` multiplies the spin-`m/2` Peter–Weyl block by `casSqrt m = √(m(m+2))/2`.
This file ties that number to the group: with the Hermitian spin operators
`J_a = (i/2) · dSpin m (X_a)`, where `dSpin m` is the derivative of the spin-`m/2` representation
(`hasDerivAt_spinMat`) and `X_a ∈ {suX, suY, suZ}` is the standard basis of `su(2)`, the Casimir
`J_x² + J_y² + J_z²` acts on the spin-`m/2` space as the scalar `casSqrt m ^ 2 = j(j+1)`, `j = m/2`
(`sum_spinOp_sq_eq_casSqrt_sq`).  So `casSqrt m` is the positive square root of the Casimir eigenvalue,
not a definition adopted by fiat.  The Lie-algebra computation is `Lightlike.Spin4.casimir_eq`.
-/

open Matrix Lightlike.SU2

namespace Lightlike.Canonical.AreaOperator

noncomputable section

/-- **The quadratic form in the `su(2)` basis**:
`Σ_a dSpin m (X_a)² = −m(m+2)` on the spin-`m/2` space. -/
theorem sum_dSpin_su_sq (m : ℕ) :
    dSpin m suX * dSpin m suX + dSpin m suY * dSpin m suY + dSpin m suZ * dSpin m suZ =
      (-((m : ℂ) * ((m : ℂ) + 2))) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have h := Lightlike.Spin4.casimir_eq m
  have key : dSpin m suX * dSpin m suX + dSpin m suY * dSpin m suY + dSpin m suZ * dSpin m suZ =
      (-4 : ℂ) • ((1 / 2 : ℂ) • (dSpin m matE * dSpin m matF + dSpin m matF * dSpin m matE) +
        (1 / 4 : ℂ) • (dSpin m matH * dSpin m matH)) := by
    simp only [suX_eq, suY_eq, suZ_eq, dSpin_smul, dSpin_add, dSpin_sub, smul_mul_smul_comm,
      add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_smul, Complex.I_mul_I]
    module
  rw [key, h, smul_smul]
  congr 1
  ring

/-- The Hermitian spin operator `J_X = (i/2) · dSpin m X`. -/
def spinOp (m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  (Complex.I / 2) • dSpin m X

/-- **`casSqrt m` is the square root of the Casimir**: `J_x² + J_y² + J_z² = (casSqrt m)² · 1`, i.e.
`j(j+1)` for `j = m/2`; hence `casSqrt m = √(j(j+1))` is the positive root of the `SU(2)` Casimir eigenvalue. -/
theorem sum_spinOp_sq_eq_casSqrt_sq (m : ℕ) :
    spinOp m suX * spinOp m suX + spinOp m suY * spinOp m suY + spinOp m suZ * spinOp m suZ =
      ((casSqrt m ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  have h := sum_dSpin_su_sq m
  have hc : ((casSqrt m ^ 2 : ℝ) : ℂ) = (m : ℂ) * ((m : ℂ) + 2) / 4 := by
    rw [casSqrt_sq]; push_cast; ring
  have hI : Complex.I / 2 * (Complex.I / 2) = -(1 / 4) := by
    rw [div_mul_div_comm, Complex.I_mul_I]; norm_num
  simp only [spinOp, smul_mul_smul_comm, hI]
  rw [← smul_add, ← smul_add, h, hc, smul_smul]
  congr 1
  ring

end

end Lightlike.Canonical.AreaOperator

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.spinOp := _root_.Lightlike.Canonical.AreaOperator.spinOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.sum_dSpin_su_sq := _root_.Lightlike.Canonical.AreaOperator.sum_dSpin_su_sq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.sum_spinOp_sq_eq_casSqrt_sq := _root_.Lightlike.Canonical.AreaOperator.sum_spinOp_sq_eq_casSqrt_sq
