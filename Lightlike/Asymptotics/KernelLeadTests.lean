import Lightlike.Asymptotics.KernelLead

/-!
# Trust checks for the leading form of Racah's kernel

* **Known value.** For `A = 0` the amplitude is `P_0(w) = w^{−2}`: at `w = i`,
  `exp(−½ · 4 · iπ/2) = e^{−iπ} = −1` (`leadP_zero_I`), and at `w = 2i` the rescaling law
  `P_{cA}(cw) = P_A(w)/c²` gives `(2i)^{−2} = −1/4` (`leadP_zero_two_I`). The half-shift defect
  at `X = 1` is `ρ(1) = (3/2) log(3/2) − 1/2` (`stirRho_one`).
* **Wrong input fails.** The amplitude is a product of four square roots, so it scales with the
  power `c^{−2}`; the one-root law `P_A(w)/c` gives `−1/2 ≠ −1/4` at `A = 0`, `w = i`, `c = 2`
  (`leadP_smul_wrong_power`).
* **Non-vacuity.** For `a = 0`, `b = 0`, `N = 112`, `Aᵢ = 3/224`, `Bₖ = 1/56`, `x = i`, `y = 1`,
  `R = 2` all hypotheses of `norm_racahKernel_sub_lead_le` hold, so the bound applies
  (`racahKernel_lead_zero`).
* **Junk values.** Lean's `log 0 = 0` gives `P_0(0) = 1` (`leadP_zero_zero`), although the true
  amplitude has a pole there; the bounds therefore assume `Im w ≥ y > 0`. On the real axis the
  denominator `1 + e^{2πiZ}` of `racahKernel_eq_lead` vanishes at `Z = 1/2`
  (`one_add_exp_half_eq_zero`), so the exact form assumes `Im Z > 0`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `P_0(i) = i^{−2} = −1`. -/
theorem leadP_zero_I : leadP 0 I = -1 := by
  simp only [leadP, Pi.zero_apply, ofReal_zero, sub_zero, log_I, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show -((4 : ℕ) * (π / 2 * I)) / 2 = -(π * I) by push_cast; ring, exp_neg, exp_pi_mul_I]
  norm_num

/-- **Known value**: `P_0(2i) = (2i)^{−2} = −1/4`, from the rescaling law `leadP_smul`. -/
theorem leadP_zero_two_I : leadP 0 (2 * I) = -1 / 4 := by
  have h := leadP_smul 0 (c := 2) (by norm_num) (w := I) (by simp)
  rw [smul_zero, leadP_zero_I] at h
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, h]
  norm_num

/-- **Known value**: `ρ(1) = (3/2) log(3/2) − 1/2`. -/
theorem stirRho_one : stirRho 1 = 3 / 2 * log (3 / 2) - 1 / 2 := by
  simp only [stirRho, stirF, log_one]
  norm_num
  ring

/-- **Wrong input**: the one-root scaling `P_{cA}(cw) = P_A(w)/c` fails; the amplitude scales
with `c^{−2}`. -/
theorem leadP_smul_wrong_power : leadP ((2 : ℝ) • 0) ((2 : ℝ) * I) ≠ leadP 0 I / (2 : ℝ) := by
  rw [smul_zero, show ((2 : ℝ) : ℂ) * I = 2 * I by norm_num, leadP_zero_two_I, leadP_zero_I]
  norm_num

/-- **Non-vacuity**: the leading-form estimate applies to `a = 0`, `b = 0` at `N = 112`,
`x = i`, `y = 1`, `R = 2`. -/
theorem racahKernel_lead_zero :
    ‖(2 * π) ^ 2 * ((112 : ℝ) : ℂ) ^ 2 * racahKernel 0 0 (((112 : ℝ) : ℂ) * I - 3 / 2) -
        cexp (((112 : ℝ) : ℂ) * phaseC (fun _ => 3 / 224) (fun _ => 1 / 56) I) *
          leadP (fun _ => 3 / 224) I‖ ≤
      kernelLeadC 1 2 / 112 *
        ‖cexp (((112 : ℝ) : ℂ) * phaseC (fun _ => 3 / 224) (fun _ => 1 / 56) I) *
          leadP (fun _ => 3 / 224) I‖ := by
  have hxA : ‖I - ((3 / 224 : ℝ) : ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_I, norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hxB : ‖I - ((1 / 56 : ℝ) : ℂ)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_I, norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  exact norm_racahKernel_sub_lead_le 0 0 (N := 112) (A := fun _ => 3 / 224)
    (B := fun _ => 1 / 56) (fun _ => by norm_num) (fun _ => by norm_num)
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
    (x := I) (y := 1) (R := 2) one_pos (by simp) (by simp) (fun _ => hxA) (fun _ => hxB)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Junk value**: `log 0 = 0` gives `P_0(0) = 1`, although the amplitude has a pole at `0`. -/
theorem leadP_zero_zero : leadP 0 0 = 1 := by
  simp [leadP]

/-- **Junk value**: on the real axis the denominator `1 + e^{2πiZ}` of the exact form vanishes at
`Z = 1/2`. -/
theorem one_add_exp_half_eq_zero : 1 + cexp (2 * π * I * (1 / 2 : ℂ)) = 0 := by
  rw [show 2 * (π : ℂ) * I * (1 / 2) = π * I by ring, exp_pi_mul_I]
  norm_num

end Lightlike.Asymptotics
