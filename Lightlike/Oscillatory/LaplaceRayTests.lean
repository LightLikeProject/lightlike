module

public import Lightlike.Oscillatory.LaplaceRay

/-!
# Trust checks for `laplace_ray_uniform`

* **Non-vacuity** (`laplace_ray_gaussian`): the hypotheses hold for the pure Gaussian
  `φ t = -t² / 2`, `g = 1`, `a = 1` on `[0, 1]`, so the theorem gives
  `∫₀¹ e^{-N t² / 2} dt = √(2π / N) / 2 + O(1 / N)`. This is the classical value: the half-line
  Gaussian `∫₀^∞ e^{-N t² / 2} dt = √(π / (2 N))`, with an exponentially small tail beyond `1`.
* **Wrong constant** (`laplace_ray_gaussian_wrong_constant`): with the full-line Gaussian
  `√(2π / N)` as leading term (the factor `1/2` of the half-line dropped), no `O(1 / N)` bound
  holds. The leading coefficient in `laplace_ray_uniform` is therefore pinned down.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace Lightlike.Oscillatory

/-- Non-vacuity of `laplace_ray_uniform`: for the Gaussian phase `φ t = -t² / 2` and `g = 1` on
`[0, 1]` it gives `‖∫₀¹ e^{-N t² / 2} dt - (π / (N / 2))^{1/2} / 2‖ ≤ C / N`. -/
theorem laplace_ray_gaussian :
    ∃ C : ℝ, ∀ N : ℝ, 0 < N →
      ‖(∫ t in (0 : ℝ)..1, cexp (N * ((-t ^ 2 / 2 : ℝ) : ℂ))) -
          (π / (N / 2)) ^ (1 / 2 : ℂ) / 2‖ ≤ C / N := by
  obtain ⟨C, hC⟩ := laplace_ray_uniform 1 1 0 (1 / 2) 0 1 one_pos one_pos (by norm_num)
  refine ⟨C, fun N hN => ?_⟩
  have h := hC 1 (fun t => ((-t ^ 2 / 2 : ℝ) : ℂ)) (fun _ => 1) (by simp)
    (by fun_prop) continuousOn_const
    (fun t _ => by
      rw [show ((-t ^ 2 / 2 : ℝ) : ℂ) + 1 * (t : ℂ) ^ 2 / 2 = 0 by push_cast; ring]
      simp)
    (fun t _ => by
      rw [Complex.ofReal_re]; linarith)
    (fun t _ => by simp) (by simp) N hN
  simpa only [one_mul, mul_one] using h

/-- Wrong constant: with the leading term `(π / (N / 2))^{1/2} = √(2π / N)` (the full-line
Gaussian, factor `1/2` dropped) the error is not `O(1 / N)`. -/
theorem laplace_ray_gaussian_wrong_constant :
    ¬ ∃ C : ℝ, ∀ N : ℝ, 0 < N →
      ‖(∫ t in (0 : ℝ)..1, cexp (N * ((-t ^ 2 / 2 : ℝ) : ℂ))) -
          (π / (N / 2)) ^ (1 / 2 : ℂ)‖ ≤ C / N := by
  rintro ⟨C, hC⟩
  obtain ⟨C₀, hC₀⟩ := laplace_ray_gaussian
  have key : ∀ N : ℝ, 0 < N → ‖((π : ℂ) / (N / 2)) ^ (1 / 2 : ℂ)‖ / 2 ≤ (C + C₀) / N := by
    intro N hN
    have h1 := hC₀ N hN
    have h2 := hC N hN
    set I := ∫ t in (0 : ℝ)..1, cexp (N * ((-t ^ 2 / 2 : ℝ) : ℂ))
    set L := ((π : ℂ) / (N / 2)) ^ (1 / 2 : ℂ)
    calc ‖L‖ / 2 = ‖L / 2‖ := by rw [norm_div]; norm_num
      _ = ‖(I - L / 2) - (I - L)‖ := by congr 1; ring
      _ ≤ ‖I - L / 2‖ + ‖I - L‖ := norm_sub_le _ _
      _ ≤ C₀ / N + C / N := add_le_add h1 h2
      _ = (C + C₀) / N := by ring
  have hnorm : ∀ N : ℝ, 0 < N → ‖((π : ℂ) / (N / 2)) ^ (1 / 2 : ℂ)‖ = √(2 * π / N) := by
    intro N hN
    have : ((π : ℂ) / (N / 2)) = ((2 * π / N : ℝ) : ℂ) := by
      push_cast
      rw [div_div_eq_mul_div]
      ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have hπ := Real.pi_gt_three
  set D := C + C₀
  have hN₀ : 0 < D ^ 2 + 1 := by positivity
  have h := key (D ^ 2 + 1) hN₀
  rw [hnorm _ hN₀, div_le_div_iff₀ two_pos hN₀] at h
  set s := √(2 * π / (D ^ 2 + 1))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 * (D ^ 2 + 1) = 2 * π := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hsN : 0 < s * (D ^ 2 + 1) := mul_pos hs hN₀
  have hD : 0 ≤ D := by nlinarith
  have hsq : s ^ 2 * (D ^ 2 + 1) ^ 2 = 2 * π * (D ^ 2 + 1) := by rw [← hs2]; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg (mul_nonneg hD two_pos.le) hsN.le),
    mul_pos (sub_pos.mpr hπ) hN₀]

end Lightlike.Oscillatory
