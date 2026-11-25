import Lightlike.GR.HawkingRadiation.Planck
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The Bogoliubov kernels of the collapse model: the Wronskian density (SC4, part 2)

Row G1-068 (milestone SC4).  We compute `|Γ(is)|² = π / (s sinh (π s))` from Euler's reflection formula
and deduce the pointwise value of the Wronskian density
`|α|² - |β|² = (2π/s) |c|²` of the kernels `α = c·Γ(is)(iw)^{-is}`, `β = c·Γ(is)(-iw)^{-is}`
(common prefactor `c`), which is what normalises the Bogoliubov transformation.  Together with
`norm_kernelMinus_sq` this fixes the thermal occupation (Carlip 2014, §3.2).

## Main statements

* `norm_gamma_I_mul_sq`: `‖Γ(i s)‖² = π / (s sinh (π s))` for `s > 0`.
* `wronskian_density`: `‖c·kernelPlus s w‖² - ‖c·kernelMinus s w‖² = (2π/s) ‖c‖²`.
* `normalized_kernels_planck`: with `‖c‖² = s/(2π)` the kernels satisfy `|α|²-|β|² = 1`
  and `|β|² = 1/(e^{2πs} - 1)`.
-/

open Complex

namespace Lightlike.GR.HawkingRadiation

noncomputable section

/-- **Modulus of `Γ(is)`**: `|Γ(is)|² = π / (s sinh (π s))` for `s > 0`. -/
theorem norm_gamma_I_mul_sq {s : ℝ} (hs : 0 < s) :
    ‖Complex.Gamma (I * s)‖ ^ 2 = Real.pi / (s * Real.sinh (Real.pi * s)) := by
  have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hIs : I * (s : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hsC
  have h1 := Complex.Gamma_mul_Gamma_one_sub (I * s)
  have h2 : Complex.Gamma (1 - I * s) = (-(I * s)) * Complex.Gamma (-(I * s)) := by
    have := Complex.Gamma_add_one (-(I * s)) (neg_ne_zero.mpr hIs)
    rw [← this]
    congr 1
    ring
  have h3 : Complex.Gamma (-(I * s)) = (starRingEnd ℂ) (Complex.Gamma (I * s)) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp
  have hsin : Complex.sin (Real.pi * (I * s)) = I * (Real.sinh (Real.pi * s) : ℂ) := by
    have : (Real.pi : ℂ) * (I * s) = ((Real.pi * s : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.sin_mul_I, Complex.ofReal_sinh]
    push_cast
    ring
  have hpos : 0 < Real.sinh (Real.pi * s) := Real.sinh_pos_iff.mpr (by positivity)
  have hsh : (Real.sinh (Real.pi * s) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  rw [h2, h3, hsin] at h1
  have hmc : Complex.Gamma (I * s) * (starRingEnd ℂ) (Complex.Gamma (I * s)) =
      ((‖Complex.Gamma (I * s)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h4 : ((‖Complex.Gamma (I * s)‖ ^ 2 : ℝ) : ℂ) =
      ((Real.pi / (s * Real.sinh (Real.pi * s)) : ℝ) : ℂ) := by
    have e : Complex.Gamma (I * s) * (-(I * s) * (starRingEnd ℂ) (Complex.Gamma (I * s))) =
        (-(I * s)) * (Complex.Gamma (I * s) * (starRingEnd ℂ) (Complex.Gamma (I * s))) := by ring
    rw [e, hmc] at h1
    have h5 := (div_eq_iff (mul_ne_zero I_ne_zero hsh)).mp h1.symm
    have h6 : (s : ℂ) * ((‖Complex.Gamma (I * s)‖ ^ 2 : ℝ) : ℂ) * (Real.sinh (Real.pi * s) : ℂ)
        = (Real.pi : ℂ) := by
      linear_combination (-1) * h5 +
        ((s : ℂ) * ((‖Complex.Gamma (I * s)‖ ^ 2 : ℝ) : ℂ) * (Real.sinh (Real.pi * s) : ℂ)) *
          Complex.I_sq
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (mul_ne_zero hsC hsh)]
    linear_combination h6
  exact_mod_cast h4

/-- **The Wronskian density of the collapse kernels**: for any common prefactor `c`,
`|c α|² - |c β|² = (2π/s) |c|²` (`s > 0`, `w > 0`). -/
theorem wronskian_density {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (c : ℂ) :
    ‖c * kernelPlus s w‖ ^ 2 - ‖c * kernelMinus s w‖ ^ 2 = 2 * Real.pi / s * ‖c‖ ^ 2 := by
  have hpos : 0 < Real.sinh (Real.pi * s) := Real.sinh_pos_iff.mpr (by positivity)
  have hG := norm_gamma_I_mul_sq hs
  have hm := norm_kernelMinus_sq (s := s) hw
  have hexp : Real.exp (Real.pi * s) - Real.exp (-(Real.pi * s)) = 2 * Real.sinh (Real.pi * s) := by
    rw [Real.sinh_eq]; ring
  have hP : ‖kernelPlus s w‖ ^ 2 = ‖Complex.Gamma (I * s)‖ ^ 2 * Real.exp (Real.pi * s) := by
    unfold kernelPlus
    rw [norm_mul, norm_cpow_plus hw, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  have hM : ‖kernelMinus s w‖ ^ 2 = ‖Complex.Gamma (I * s)‖ ^ 2 * Real.exp (-(Real.pi * s)) := by
    unfold kernelMinus
    rw [norm_mul, norm_cpow_minus hw, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hP, hM, hG]
  have : (Real.pi / (s * Real.sinh (Real.pi * s)) * Real.exp (Real.pi * s)) -
      (Real.pi / (s * Real.sinh (Real.pi * s)) * Real.exp (-(Real.pi * s))) =
      2 * Real.pi / s := by
    rw [← mul_sub, hexp]
    field_simp
  calc ‖c‖ ^ 2 * (Real.pi / (s * Real.sinh (Real.pi * s)) * Real.exp (Real.pi * s)) -
        ‖c‖ ^ 2 * (Real.pi / (s * Real.sinh (Real.pi * s)) * Real.exp (-(Real.pi * s)))
      = ‖c‖ ^ 2 * (2 * Real.pi / s) := by rw [← mul_sub, this]
    _ = _ := by ring

/-- **Normalised collapse kernels give the Planck law.**  With the prefactor `‖c‖² = s/(2π)` one has
`|α|² - |β|² = 1` and `|β|² = 1/(e^{2πs} - 1)`, `s = ω/κ`. -/
theorem normalized_kernels_planck {s w : ℝ} (hs : 0 < s) (hw : 0 < w) (c : ℂ)
    (hc : ‖c‖ ^ 2 = s / (2 * Real.pi)) :
    ‖c * kernelPlus s w‖ ^ 2 - ‖c * kernelMinus s w‖ ^ 2 = 1 ∧
    ‖c * kernelMinus s w‖ ^ 2 = 1 / (Real.exp (2 * Real.pi * s) - 1) := by
  have h1 : ‖c * kernelPlus s w‖ ^ 2 - ‖c * kernelMinus s w‖ ^ 2 = 1 := by
    rw [wronskian_density hs hw, hc]
    field_simp
  refine ⟨h1, planck_of_ratio (by positivity) h1 ?_⟩
  rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_kernelMinus_sq hw]
  ring

end

end Lightlike.GR.HawkingRadiation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.norm_gamma_I_mul_sq := _root_.Lightlike.GR.HawkingRadiation.norm_gamma_I_mul_sq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.normalized_kernels_planck := _root_.Lightlike.GR.HawkingRadiation.normalized_kernels_planck
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_068.wronskian_density := _root_.Lightlike.GR.HawkingRadiation.wronskian_density
