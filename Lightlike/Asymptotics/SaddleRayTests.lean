import Lightlike.Asymptotics.SaddleRay
import Lightlike.Asymptotics.Tests

/-!
# Trust checks for the rays through the saddle

* **Known value.** For four equal factors `fᵢ = 4` the weight `e^{−(Σᵢ log fᵢ)/2}` of
  `exp_neg_half_sum_log_sq` is `4^{−2} = 1/16` (`exp_neg_half_sum_log_four`). The rescaling
  `w ↦ 2w − 3/2` sends `i` to a point of imaginary part `2` (`im_rescale_two_I`). At the regular
  tetrahedron and `X = −π/4` the leading term of `IsEuclid.im_lead_main` is
  `1/(√(12π) (2π)²)`, the maximum of the cosine (`im_lead_main_regular`).
* **Wrong input fails.** The phase of `P(s) u₀` is `e^{−iπ/4}`, not `e^{iπ/4}`: the two have
  imaginary parts of opposite sign (`exp_neg_quarter_ne`).
* **Non-vacuity.** The mean value bound `norm_sub_le_of_path` applies to the straight path
  `t ↦ t` from `0` to `1` with `F = id` and is an equality there (`norm_sub_le_of_path_segment`);
  `hasDerivAt_rescale` applies to `Φ = id`, `f = 1` and gives the derivative `N` of
  `w ↦ N w − 3/2` (`hasDerivAt_rescale_id`).
* **Junk values.** `ne_intCast_of_im_pos` needs `Im z > 0`: on the real axis `z = 0` is the
  integer `0` (`not_ne_intCast_zero`). Racah's kernel has poles at the integers, so every bound
  on it is stated on the open upper half-plane.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `e^{−(4 log 4)/2} = 1/16`, from `exp_neg_half_sum_log_sq` with `fᵢ = 4`. -/
theorem exp_neg_half_sum_log_four :
    Real.exp (-(∑ _i : Fin 4, Real.log 4) / 2) = 1 / 16 := by
  have h := exp_neg_half_sum_log_sq (f := fun _ => (4 : ℝ)) (fun _ => by norm_num)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hpos := Real.exp_pos (-(∑ _i : Fin 4, Real.log 4) / 2)
  nlinarith [sq_nonneg (Real.exp (-(∑ _i : Fin 4, Real.log 4) / 2) - 1 / 16)]

/-- **Known value**: `Im (2i − 3/2) = 2`. -/
theorem im_rescale_two_I : (((2 : ℝ) : ℂ) * I - 3 / 2).im = 2 := by
  rw [im_rescale, I_im, mul_one]

/-- **Known value**: at the regular tetrahedron and `X = −π/4` the leading term is
`1/(√(12π) (2π)²)`. -/
theorem im_lead_main_regular :
    -(√(√(vol2l fun _ => 1)) / (π * (2 * π) ^ 2)) *
        (cexp (((-(π / 4) : ℝ) : ℂ) * I) * (leadP (faceSum fun _ => 1) (saddle fun _ => 1) *
          saddleDir (fun _ => 1) * (√(π / ‖saddleCoeff fun _ => 1‖) : ℂ))).im =
      1 / (√(12 * π) * (2 * π) ^ 2) := by
  rw [isEuclid_regular.im_lead_main, neg_add_cancel, Real.cos_zero]

/-- **Wrong input fails**: `e^{−iπ/4} ≠ e^{iπ/4}`, so the phase `−π/4` of
`leadP_mul_saddleDir` cannot be replaced by `+π/4`. -/
theorem exp_neg_quarter_ne : cexp (-(π / 4 : ℂ) * I) ≠ cexp ((π / 4 : ℂ) * I) := by
  intro h
  have h' := congrArg Complex.im h
  rw [show -(π / 4 : ℂ) * I = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring,
    show (π / 4 : ℂ) * I = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring,
    exp_ofReal_mul_I_im, exp_ofReal_mul_I_im, Real.sin_neg] at h'
  have : 0 < Real.sin (π / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  linarith

/-- **Non-vacuity**: the mean value bound along the segment `t ↦ t`, `t ∈ [0, 1]`, for `F = id`,
`f = 1`; both sides equal `1`. -/
theorem norm_sub_le_of_path_segment :
    ‖(fun z : ℂ => z) (((1 : ℝ) : ℂ)) - (fun z : ℂ => z) (((0 : ℝ) : ℂ))‖ ≤ 1 * 1 * (1 - 0) ∧
      ‖(fun z : ℂ => z) (((1 : ℝ) : ℂ)) - (fun z : ℂ => z) (((0 : ℝ) : ℂ))‖ = 1 := by
  refine ⟨norm_sub_le_of_path (F := fun z => z) (f := fun _ => 1) (γ := fun t : ℝ => (t : ℂ))
    (γ' := fun _ => ((1 : ℝ) : ℂ)) zero_le_one (by fun_prop)
    (fun t _ => (hasDerivAt_id t).ofReal_comp.hasDerivWithinAt) (fun _ _ => by simp)
    (fun _ _ => hasDerivAt_id _) (fun _ _ => by simp) (by fun_prop), by simp⟩

/-- **Non-vacuity**: `hasDerivAt_rescale` for `Φ = id`, `f = 1` gives the derivative `N` of
`w ↦ N w − 3/2`. -/
theorem hasDerivAt_rescale_id {N : ℝ} (hN : 0 < N) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun w : ℂ => (N : ℂ) * w - 3 / 2) N w := by
  have h := hasDerivAt_rescale (Φ := fun z => z) (f := fun _ => 1) hN
    (fun z _ _ => hasDerivAt_id z) hw
  rwa [mul_one] at h

/-- **Junk value**: on the real axis the hypothesis `Im z > 0` of `ne_intCast_of_im_pos` is
needed, since `0 = (0 : ℤ)`. -/
theorem not_ne_intCast_zero : ¬ ∀ n : ℤ, (0 : ℂ) ≠ n :=
  fun h => h 0 (by simp)

end Lightlike.Asymptotics
