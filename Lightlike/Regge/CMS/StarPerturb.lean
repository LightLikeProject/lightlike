import Mathlib
import Lightlike.Regge.CMS.Winding

/-!
# A small relative perturbation of a star keeps its winding (RC6b, step 5)

The star `u i = w i + O(h²)` obtained by displacing the neighbours to normal coordinates winds as
many times as the chart star `w`. Write `u i = s i * w i` with `s i` close to `1`; then
`u (i+1) / u i = (w (i+1) / w i) * (s (i+1) / s i)`, the arguments of the second factor telescope
around the cycle, and no argument crosses `±π` as long as the angles of `w` stay away from `π`.

## Main results

* `abs_arg_le_of_norm_sub_one_le`: `‖s - 1‖ ≤ ε` and `2 ε ≤ sin ψ` give `|arg s| ≤ ψ`.
* `sum_angle_perturb`: for positively oriented stars `u`, `w` with `‖u i / w i - 1‖ ≤ ε` and
  every angle of `w` at most `π - θ`, `4 ε ≤ sin (θ / 4)`, the angle sums agree.
-/

open Real Complex

namespace Lightlike.CMS

theorem abs_arg_le_of_norm_sub_one_le {s : ℂ} {ε ψ : ℝ} (hψ0 : 0 ≤ ψ) (hψ : ψ ≤ π / 2)
    (hε : 2 * ε ≤ Real.sin ψ)
    (hε2 : ε ≤ 1 / 2) (hs : ‖s - 1‖ ≤ ε) : |arg s| ≤ ψ := by
  have him : |s.im| ≤ ε := by
    have := Complex.abs_im_le_norm (s - 1)
    simpa using this.trans hs
  have hre : 1 - ε ≤ s.re := by
    have := Complex.abs_re_le_norm (s - 1)
    have h2 := (abs_le.mp (this.trans hs)).1
    simp at h2; linarith
  have hn : 1 / 2 ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [abs_of_nonneg (by linarith)] at this; linarith
  have hn0 : 0 < ‖s‖ := by linarith
  have hsψ : 0 ≤ Real.sin ψ := by linarith [abs_nonneg s.im, him, hε]
  have ht : |s.im / ‖s‖| ≤ Real.sin ψ := by
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    nlinarith [abs_nonneg s.im]
  rw [Complex.arg_of_re_nonneg (by linarith)]
  have ht' := abs_le.mp ht
  have hsin1 : Real.sin ψ ≤ 1 := Real.sin_le_one ψ
  rw [abs_le]
  constructor
  · have := Real.arcsin_le_iff_le_sin (x := -(s.im / ‖s‖)) (y := ψ) ⟨by linarith, by linarith⟩
      ⟨by linarith [Real.pi_pos], hψ⟩
    have h2 := (this.mpr (by linarith))
    rw [Real.arcsin_neg] at h2; linarith
  · exact (Real.arcsin_le_iff_le_sin ⟨by linarith, by linarith⟩ ⟨by linarith [Real.pi_pos], hψ⟩).mpr
      (by linarith)

theorem ne_zero_of_isPosStar {n : ℕ} [NeZero n] {u : ZMod n → ℂ} (hu : IsPosStar u) (i : ZMod n) :
    u i ≠ 0 := by
  intro h
  have := hu i
  simp [h] at this

/-- **A small relative perturbation of a positively oriented star has the same angle sum.** -/
theorem sum_angle_perturb {n : ℕ} [NeZero n] {w u : ZMod n → ℂ} (hw : IsPosStar w)
    (hu : IsPosStar u) {ε θ : ℝ} (hθ : 0 < θ) (hθπ : θ ≤ π)
    (hang : ∀ i, InnerProductGeometry.angle (w i) (w (i + 1)) ≤ π - θ)
    (hε : 4 * ε ≤ Real.sin (θ / 4)) (hs : ∀ i, ‖u i / w i - 1‖ ≤ ε) :
    ∑ i, InnerProductGeometry.angle (u i) (u (i + 1)) =
      ∑ i, InnerProductGeometry.angle (w i) (w (i + 1)) := by
  have hψ0 : 0 ≤ θ / 4 := by positivity
  have hψ : θ / 4 ≤ π / 2 := by linarith [Real.pi_pos]
  have hsin1 : Real.sin (θ / 4) ≤ 1 := Real.sin_le_one _
  have hε0 : ε ≤ 1 / 4 := by linarith
  have hsin0 : 0 ≤ Real.sin (θ / 4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hψ0 (by linarith [Real.pi_pos])
  have harg : ∀ i, |arg (u i / w i)| ≤ θ / 4 := fun i =>
    abs_arg_le_of_norm_sub_one_le hψ0 hψ (by linarith) (by linarith) (hs i)
  have hwu : ∀ i, w i ≠ 0 := ne_zero_of_isPosStar hw
  have huu : ∀ i, u i ≠ 0 := ne_zero_of_isPosStar hu
  have key : ∀ i, InnerProductGeometry.angle (u i) (u (i + 1)) =
      InnerProductGeometry.angle (w i) (w (i + 1)) +
        (arg (u (i + 1) / w (i + 1)) - arg (u i / w i)) := by
    intro i
    rw [angle_eq_arg (hu i), angle_eq_arg (hw i)]
    set q := w (i + 1) / w i with hq
    set s1 := u (i + 1) / w (i + 1) with hs1
    set s0 := u i / w i with hs0
    have hs1n : s1 ≠ 0 := div_ne_zero (huu _) (hwu _)
    have hs0n : s0 ≠ 0 := div_ne_zero (huu _) (hwu _)
    have hqn : q ≠ 0 := div_ne_zero (hwu _) (hwu _)
    have hfac : u (i + 1) / u i = q * (s1 * s0⁻¹) := by
      rw [hq, hs1, hs0]; field_simp [hwu i, hwu (i + 1), huu i, huu (i + 1)]
    have h0 := harg i
    have h1 := harg (i + 1)
    rw [← hs0] at h0; rw [← hs1] at h1
    have hne0 : arg s0 ≠ π := by
      intro h; rw [h, abs_of_pos Real.pi_pos] at h0; linarith [Real.pi_pos]
    have hinv : arg s0⁻¹ = -arg s0 := by rw [arg_inv, ite_eq_right_iff.mpr (fun h => absurd h hne0)]
    have hsum1 : arg s1 + arg s0⁻¹ ∈ Set.Ioc (-π) π := by
      rw [hinv]
      constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2, (abs_le.mp h1).1,
        (abs_le.mp h1).2, Real.pi_pos]
    have hr : arg (s1 * s0⁻¹) = arg s1 - arg s0 := by
      rw [(arg_mul_eq_add_arg_iff hs1n (inv_ne_zero hs0n)).mpr hsum1, hinv]; ring
    have hq0 : 0 ≤ arg q := by
      rw [hq, ← angle_eq_arg (hw i)]; exact InnerProductGeometry.angle_nonneg _ _
    have hq1 : arg q ≤ π - θ := by
      rw [hq, ← angle_eq_arg (hw i)]; exact hang i
    have hsum2 : arg q + arg (s1 * s0⁻¹) ∈ Set.Ioc (-π) π := by
      rw [hr]
      constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2, (abs_le.mp h1).1,
        (abs_le.mp h1).2, Real.pi_pos]
    rw [hfac, (arg_mul_eq_add_arg_iff hqn (mul_ne_zero hs1n (inv_ne_zero hs0n))).mpr hsum2, hr]
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have : ∑ i : ZMod n, arg (u (i + 1) / w (i + 1)) = ∑ i : ZMod n, arg (u i / w i) :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ => rfl
  rw [this]; ring

end Lightlike.CMS
