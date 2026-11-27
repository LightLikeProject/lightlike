import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical

/-!
# Symmetries of the principal-series matrix coefficients

The reflection `x ↦ -x` sends `e_k` to `e_{-k}`, so `Φ^ν_{-m,-n} = Φ^ν_{m,n}` (`mcoefP_neg_neg`).
Conjugating `a(ξ)` by the rotation `k_{π/2}` gives `a(-ξ)`, so
`Φ^ν_{m,n}(-ξ) = (-1)^{m-n} Φ^ν_{m,n}(ξ)` (`mcoefP_neg_arg`); with unitarity,
`Φ^ν_{m,n}(ξ) = conj Φ^ν_{n,m}(-ξ)` (`mcoefP_swap`) and
`Φ^ν_{m,n} = (-1)^{n-m} conj Φ^ν_{n,m}` (`mcoefP_eq_conj`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (pairing the ladder chains with the matrix
coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `e_k(-x) = e_{-k}(x)`. -/
lemma kVecP_neg (ν : ℝ) (k : ℤ) (x : ℝ) : kVecP ν k (-x) = kVecP ν (-k) x := by
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  have h3 : -(x : ℂ) + I ≠ 0 := by
    rw [show -(x : ℂ) + I = -((x : ℂ) - I) by ring]; exact neg_ne_zero.2 hm
  simp only [kVecP, neg_sq, Complex.ofReal_neg, zpow_neg, ← inv_zpow, inv_div]
  congr 2
  rw [div_eq_div_iff h3 hm]
  ring

/-- **The reflection symmetry**: `Φ^ν_{-m,-n} = Φ^ν_{m,n}`. -/
theorem mcoefP_neg_neg (ν ξ : ℝ) (m n : ℤ) : mcoefP ν (-m) (-n) ξ = mcoefP ν m n ξ := by
  rw [mcoefP_eq_integral, mcoefP_eq_integral, ← integral_neg_eq_self]
  congr 1
  funext x
  simp only [kVecP_neg, mul_neg, neg_neg]

/-- `k_{π/2} a(ξ) k_{-π/2} = a(-ξ)`. -/
lemma rot_mul_aR_mul_rot (ξ : ℝ) : rot (Real.pi / 2) * aR ξ * rot (-(Real.pi / 2)) = aR (-ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aR, diagSL, Matrix.mul_apply, Fin.sum_univ_two, neg_div, Real.exp_neg]

/-- **The Weyl symmetry**: `Φ^ν_{m,n}(-ξ) = (-1)^{m-n} Φ^ν_{m,n}(ξ)`. -/
theorem mcoefP_neg_arg (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n (-ξ) = (-1 : ℂ) ^ (m - n) * mcoefP ν m n ξ := by
  have h := inner_kVecL2_kak ν (Real.pi / 2) ξ (-(Real.pi / 2)) m n
  rw [rot_mul_aR_mul_rot] at h
  have h' : mcoefP ν m n (-ξ) = _ := h
  rw [h']
  congr 1
  have e : -(2 * ((m : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) + (n : ℂ) * ((-(Real.pi / 2) : ℝ) : ℂ)) * I) =
      ((m - n : ℤ) : ℂ) * (-(Real.pi * I)) := by
    push_cast; ring
  rw [e, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-- **Unitarity**: `Φ^ν_{m,n}(ξ) = conj Φ^ν_{n,m}(-ξ)`. -/
theorem mcoefP_swap (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n ξ = (starRingEnd ℂ) (mcoefP ν n m (-ξ)) := by
  rw [show mcoefP ν n m (-ξ) =
      inner ℂ (kVecL2 ν n) (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m)) from rfl,
    inner_conj_symm, inner_aR_neg_kVecL2]

/-- `Φ^ν_{m,n} = (-1)^{n-m} conj Φ^ν_{n,m}`. -/
theorem mcoefP_eq_conj (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n ξ = (-1 : ℂ) ^ (n - m) * (starRingEnd ℂ) (mcoefP ν n m ξ) := by
  rw [mcoefP_swap, mcoefP_neg_arg, map_mul, map_zpow₀, map_neg, map_one]

end Lightlike.Lorentz.SL2RPlancherel
