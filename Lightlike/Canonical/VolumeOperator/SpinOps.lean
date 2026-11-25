import Lightlike.Poincare.PauliLubanskiRest
import Lightlike.Spin4.EPRL

/-!
# Spin operators `J_a` of the spin-`n/2` representation: Hermiticity and commutation relations

First piece of the volume operator (row G2-014, milestone CA4). The volume operator of loop quantum
gravity is built from the angular-momentum operators `J_a` of the edges at a node. This file proves
what the construction uses of the single-edge operators `spinOp n a` (`Lightlike/Poincare/PauliLubanskiRest.lean`):

* `dSpin_bracket_EF`: `[E, F] = H` in every spin representation;
* `spinOp_conjTranspose`: the `J_a` are Hermitian;
* `spinOp_comm_xy`, `spinOp_comm_yz`, `spinOp_comm_zx`: `[J_a, J_b] = i J_c` for `(a, b, c)` cyclic.
-/

open Matrix Lightlike.SU2 Lightlike.Spin4 Lightlike.Poincare

namespace Lightlike.Canonical.VolumeOperator

variable {n : ℕ}

/-- `[E, F] = H` in every spin representation. -/
theorem dSpin_bracket_EF :
    dSpin n matE * dSpin n matF - dSpin n matF * dSpin n matE = dSpin n matH := by
  ext i j
  have h1 : (dSpin n matE * dSpin n matF) i j =
      if (i : ℕ) < n then (lad n i : ℂ) * (if (i : ℕ) + 1 = (j : ℕ) + 1 then (lad n j : ℂ) else 0)
      else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [dSpin_F_apply]
    exact sum_dSpin_E_mul (fun k => if k = (j : ℕ) + 1 then (lad n j : ℂ) else 0) i
  have h2 : (dSpin n matF * dSpin n matE) i j =
      if 0 < (i : ℕ) then (lad n ((i : ℕ) - 1) : ℂ) *
        (if (j : ℕ) = ((i : ℕ) - 1) + 1 then (lad n ((i : ℕ) - 1) : ℂ) else 0)
      else 0 := by
    rw [Matrix.mul_apply]
    simp_rw [dSpin_E_apply]
    exact sum_dSpin_F_mul (fun k => if (j : ℕ) = k + 1 then (lad n k : ℂ) else 0) i
  rw [Matrix.sub_apply, h1, h2, dSpin_H_apply]
  by_cases hij : i = j
  · subst hij
    have d1 : (if (i : ℕ) < n then (lad n i : ℂ) *
        (if (i : ℕ) + 1 = (i : ℕ) + 1 then (lad n i : ℂ) else 0) else 0) =
        if (i : ℕ) < n then ((i : ℂ) + 1) * ((n : ℂ) - i) else 0 := by
      by_cases hn : (i : ℕ) < n
      · have h' : (lad n i : ℂ) * lad n i = ((i : ℂ) + 1) * ((n : ℂ) - i) := by
          exact_mod_cast lad_sq hn.le
        rw [ite_eq_left hn, ite_eq_left hn, ite_eq_left rfl, h']
      · rw [ite_eq_right hn, ite_eq_right hn]
    have d2 : (if 0 < (i : ℕ) then (lad n ((i : ℕ) - 1) : ℂ) *
        (if (i : ℕ) = ((i : ℕ) - 1) + 1 then (lad n ((i : ℕ) - 1) : ℂ) else 0) else 0) =
        if 0 < (i : ℕ) then (i : ℂ) * ((n : ℂ) - i + 1) else 0 := by
      by_cases hp : 0 < (i : ℕ)
      · have hle : (i : ℕ) - 1 ≤ n := by have := i.2; omega
        have hc : (((i : ℕ) - 1 : ℕ) : ℂ) = (i : ℂ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have h' : (lad n ((i : ℕ) - 1) : ℂ) * lad n ((i : ℕ) - 1) =
            (i : ℂ) * ((n : ℂ) - i + 1) := by
          have : (lad n ((i : ℕ) - 1) : ℂ) * lad n ((i : ℕ) - 1) =
              ((((i : ℕ) - 1 : ℕ) : ℂ) + 1) * ((n : ℂ) - (((i : ℕ) - 1 : ℕ) : ℂ)) := by
            exact_mod_cast lad_sq hle
          rw [this, hc]; ring
        have e : (i : ℕ) = ((i : ℕ) - 1) + 1 := by omega
        rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left e, h']
      · rw [ite_eq_right hp, ite_eq_right hp]
    rw [d1, d2, ite_eq_left rfl]
    by_cases hn : (i : ℕ) < n <;> by_cases hp : 0 < (i : ℕ)
    · rw [ite_eq_left hn, ite_eq_left hp]; ring
    · have h0 : ((i : ℕ) : ℂ) = 0 := by
        have : (i : ℕ) = 0 := by omega
        rw [this]; simp
      rw [ite_eq_left hn, ite_eq_right hp, h0]; ring
    · have hc : ((i : ℕ) : ℂ) = n := by
        have : (i : ℕ) = n := by have := i.2; omega
        exact_mod_cast this
      rw [ite_eq_right hn, ite_eq_left hp, hc]; ring
    · have h0 : ((i : ℕ) : ℂ) = 0 := by
        have : (i : ℕ) = 0 := by omega
        rw [this]; simp
      have hn0 : (n : ℂ) = 0 := by
        have : n = 0 := by omega
        rw [this]; simp
      rw [ite_eq_right hn, ite_eq_right hp, h0, hn0]; ring
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    have e1 : ¬ ((i : ℕ) + 1 = (j : ℕ) + 1) := by omega
    have e2 : 0 < (i : ℕ) → ¬ ((j : ℕ) = ((i : ℕ) - 1) + 1) := fun h => by omega
    rw [ite_eq_right hij]
    by_cases hp : 0 < (i : ℕ)
    · rw [ite_eq_left hp, ite_eq_right (e2 hp), mul_zero]
      by_cases hn : (i : ℕ) < n
      · rw [ite_eq_left hn, ite_eq_right e1, mul_zero]; simp
      · rw [ite_eq_right hn]; simp
    · rw [ite_eq_right hp]
      by_cases hn : (i : ℕ) < n
      · rw [ite_eq_left hn, ite_eq_right e1, mul_zero]; simp
      · rw [ite_eq_right hn]; simp

/-- `[F, H] = 2F` (the form of `dSpin_bracket_HF` used below). -/
lemma dSpin_bracket_FH :
    dSpin n matF * dSpin n matH - dSpin n matH * dSpin n matF = (2 : ℂ) • dSpin n matF := by
  have h := dSpin_bracket_HF (n := n)
  rw [← neg_sub, h]; module

/-- `[E, H] = -2E` (the form of `dSpin_bracket_HE` used below). -/
lemma dSpin_bracket_EH :
    dSpin n matE * dSpin n matH - dSpin n matH * dSpin n matE = (-2 : ℂ) • dSpin n matE := by
  have h := dSpin_bracket_HE (n := n)
  rw [← neg_sub, h]; module

/-- `J_x = -(E + F)/2`. -/
lemma spinOp_zero_eq :
    spinOp n 0 = (-1 / 2 : ℂ) • (dSpin n matE + dSpin n matF) := by
  simp only [spinOp, rotVel, Matrix.cons_val_zero, dSpin_smul, smul_smul, dSpin_add]
  congr 1
  rw [div_mul_eq_mul_div, Complex.I_mul_I]

/-- `J_y = (i/2)(F - E)`. -/
lemma spinOp_one_eq :
    spinOp n 1 = (Complex.I / 2 : ℂ) • (dSpin n matF - dSpin n matE) := by
  have h : rotVel 1 = matF - matE := rfl
  rw [spinOp, h, dSpin_sub]

/-- `J_z = -H/2`. -/
lemma spinOp_two_eq :
    spinOp n 2 = (-1 / 2 : ℂ) • dSpin n matH := by
  simp only [spinOp, rotVel, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, dSpin_smul,
    smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, Complex.I_mul_I]

/-- The spin operators are Hermitian. -/
theorem spinOp_conjTranspose (a : Fin 3) : (spinOp n a)ᴴ = spinOp n a := by
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, spinOp_zero_eq, conjTranspose_smul, conjTranspose_add,
      dSpin_E_conjTranspose, dSpin_F_conjTranspose]
    simp only [star_div₀, star_neg, star_one, star_ofNat]
    module
  · simp only [Fin.mk_one, Fin.isValue, spinOp_one_eq, conjTranspose_smul, conjTranspose_sub,
      dSpin_E_conjTranspose, dSpin_F_conjTranspose]
    simp only [star_div₀, Complex.star_def, Complex.conj_I, map_ofNat]
    module
  · simp only [Fin.reduceFinMk, spinOp_two_eq, conjTranspose_smul,
      dSpin_H_conjTranspose]
    simp only [star_div₀, star_neg, star_one, star_ofNat]

/-- `[J_x, J_y] = i J_z`. -/
theorem spinOp_comm_xy :
    spinOp n 0 * spinOp n 1 - spinOp n 1 * spinOp n 0 = Complex.I • spinOp n 2 := by
  rw [spinOp_zero_eq, spinOp_one_eq, spinOp_two_eq, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm (Complex.I / 2) (-1 / 2), ← smul_sub]
  have e : (dSpin n matE + dSpin n matF) * (dSpin n matF - dSpin n matE) -
      (dSpin n matF - dSpin n matE) * (dSpin n matE + dSpin n matF) =
      (dSpin n matE * dSpin n matF - dSpin n matF * dSpin n matE) +
        (dSpin n matE * dSpin n matF - dSpin n matF * dSpin n matE) := by
    noncomm_ring
  rw [e, dSpin_bracket_EF]
  module

/-- `[J_y, J_z] = i J_x`. -/
theorem spinOp_comm_yz :
    spinOp n 1 * spinOp n 2 - spinOp n 2 * spinOp n 1 = Complex.I • spinOp n 0 := by
  rw [spinOp_zero_eq, spinOp_one_eq, spinOp_two_eq, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm (-1 / 2 : ℂ) (Complex.I / 2), ← smul_sub]
  have e : (dSpin n matF - dSpin n matE) * dSpin n matH - dSpin n matH * (dSpin n matF - dSpin n matE) =
      (dSpin n matF * dSpin n matH - dSpin n matH * dSpin n matF) -
        (dSpin n matE * dSpin n matH - dSpin n matH * dSpin n matE) := by
    noncomm_ring
  rw [e, dSpin_bracket_FH, dSpin_bracket_EH]
  module

/-- `[J_z, J_x] = i J_y`. -/
theorem spinOp_comm_zx :
    spinOp n 2 * spinOp n 0 - spinOp n 0 * spinOp n 2 = Complex.I • spinOp n 1 := by
  rw [spinOp_zero_eq, spinOp_one_eq, spinOp_two_eq, smul_mul_smul_comm, smul_mul_smul_comm,
    ← smul_sub]
  have e : dSpin n matH * (dSpin n matE + dSpin n matF) - (dSpin n matE + dSpin n matF) * dSpin n matH =
      (dSpin n matH * dSpin n matE - dSpin n matE * dSpin n matH) +
        (dSpin n matH * dSpin n matF - dSpin n matF * dSpin n matH) := by
    noncomm_ring
  have hI : Complex.I * (Complex.I / 2) = -1 / 2 := by rw [← mul_div_assoc, Complex.I_mul_I]
  rw [e, dSpin_bracket_HE, dSpin_bracket_HF, smul_smul, hI]
  module

end Lightlike.Canonical.VolumeOperator

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.dSpin_bracket_EF := _root_.Lightlike.Canonical.VolumeOperator.dSpin_bracket_EF
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.dSpin_bracket_EH := _root_.Lightlike.Canonical.VolumeOperator.dSpin_bracket_EH
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.dSpin_bracket_FH := _root_.Lightlike.Canonical.VolumeOperator.dSpin_bracket_FH
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_comm_xy := _root_.Lightlike.Canonical.VolumeOperator.spinOp_comm_xy
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_comm_yz := _root_.Lightlike.Canonical.VolumeOperator.spinOp_comm_yz
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_comm_zx := _root_.Lightlike.Canonical.VolumeOperator.spinOp_comm_zx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_conjTranspose := _root_.Lightlike.Canonical.VolumeOperator.spinOp_conjTranspose
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_one_eq := _root_.Lightlike.Canonical.VolumeOperator.spinOp_one_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_two_eq := _root_.Lightlike.Canonical.VolumeOperator.spinOp_two_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.spinOp_zero_eq := _root_.Lightlike.Canonical.VolumeOperator.spinOp_zero_eq
