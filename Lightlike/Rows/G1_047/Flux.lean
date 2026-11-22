import Lightlike.Rows.G1_047.Decay

/-!
# Magnetic flux and winding number (CO24)

For a configuration `(φ, A₁, A₂)` on `ℝ²` with `|φ|² → v² ≠ 0` and covariant derivatives decaying
faster than `1/r` (`r ‖D_jφ‖ → 0`), the flux through the square `[−R, R]²` satisfies
`e ∫∫ B → 2π n`, where `n` is the winding number of `φ` on large squares (`∮ dθ = 2π n`).

## Main results

* `box_flux_eq_bdy`: Stokes on a square, `∫∫ B = ∮ A`.
* `current_eq`: `J_u = |φ|² (dθ_u − e A_u)`.
* `tendsto_delta`: `r |dθ_u − e A_u| → 0`.
* `tendsto_bdy_A`: `e ∮ A → 2π n`.
* `flux_tendsto`: `e ∫∫_{[−R,R]²} B → 2π n` (flux `= 2π n / e` for `e ≠ 0`).
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set Filter

/-- **Stokes on a square.** `∫∫ (∂₁A₂ − ∂₂A₁) = ∮ (A₂ dy − A₁ dx)` for `C¹` potentials. -/
theorem box_flux_eq_bdy {A₁ A₂ : ℝ × ℝ → ℝ} (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (R : ℝ) :
    (∫ x in (-R)..R, ∫ y in (-R)..R,
        (fderiv ℝ A₂ (x, y) (1, 0) - fderiv ℝ A₁ (x, y) (0, 1))) = bdy A₁ A₂ R := by
  have hG : ContDiff ℝ 1 (fun p => -A₁ p) := hA₁.neg
  have := integral2_divergence_prod_of_hasFDerivAt A₂ (fun p => -A₁ p)
    (fun p => fderiv ℝ A₂ p) (fun p => fderiv ℝ (fun p => -A₁ p) p) (-R) (-R) R R
    hA₂.continuous.continuousOn hG.continuous.continuousOn
    (fun x _ => ((hA₂.differentiable one_ne_zero) x).hasFDerivAt)
    (fun x _ => ((hG.differentiable one_ne_zero) x).hasFDerivAt) (by
      have hc : Continuous fun p => fderiv ℝ A₂ p (1, 0) +
          fderiv ℝ (fun p => -A₁ p) p (0, 1) :=
        ((hA₂.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
          ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      exact hc.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc))
  have key : ∀ p : ℝ × ℝ, fderiv ℝ A₂ p (1, 0) + fderiv ℝ (fun p => -A₁ p) p (0, 1) =
      fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1) := fun p => by
    rw [fderiv_fun_neg]; simp [sub_eq_add_neg]
  simp only [key] at this
  rw [this]
  rfl

/-- `J_u = |φ|² (dθ_u − e A_u)`. -/
theorem current_eq (e : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u p : ℝ × ℝ) :
    current e A φ u p = Complex.normSq (φ p) * (windingForm φ u p - e * A p) := by
  have h := Wfield_eq e 0 A φ u p
  unfold Wfield errTerm at h
  linear_combination h

/-- `|dθ_u − e A_u| · |φ| ≤ ‖D_uφ‖` where `φ ≠ 0`. -/
theorem abs_delta_mul_le (e : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u p : ℝ × ℝ) (hp : φ p ≠ 0) :
    |windingForm φ u p - e * A p| * ‖φ p‖ ≤ ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖ := by
  have hpos : 0 < ‖φ p‖ := norm_pos_iff.mpr hp
  have h1 : |current e A φ u p| ≤ ‖φ p‖ * ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  rw [current_eq, abs_mul, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)] at h1
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_lt_mul_of_pos_left hc hpos]

/-- Decay of `r · |dθ_u − e A_u|` from `r ‖D_uφ‖ → 0` and `|φ|² → v² ≠ 0`. -/
theorem tendsto_delta (e v : ℝ) (hv : v ≠ 0) {A : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} (u : ℝ × ℝ)
    (hφ : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2)))
    (h : Tendsto (fun p : ℝ × ℝ => ‖p‖ * ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0)) :
    Tendsto (fun p : ℝ × ℝ => ‖p‖ * |windingForm φ u p - e * A p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  obtain ⟨r, hr⟩ := exists_norm_ge_of_tendsto_normSq hv hφ
  have hlim : Tendsto (fun p : ℝ × ℝ => (2 / |v|) *
      (‖p‖ * ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖)) (Bornology.cobounded (ℝ × ℝ)) (nhds 0) := by
    simpa using h.const_mul (2 / |v|)
  refine squeeze_zero' (Eventually.of_forall fun p => by positivity) ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop r] with p hp
  have hφp := hr p hp
  have hne : φ p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hφp
    linarith
  have h1 := abs_delta_mul_le e A φ u p hne
  have h2 : |windingForm φ u p - e * A p| * (|v| / 2) ≤
      ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖ :=
    le_trans (mul_le_mul_of_nonneg_left hφp (abs_nonneg _)) h1
  have h3 : |windingForm φ u p - e * A p| ≤
      2 / |v| * ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hav]
    linarith
  calc ‖p‖ * |windingForm φ u p - e * A p|
      ≤ ‖p‖ * (2 / |v| * ‖covD e (A p) (fderiv ℝ φ p u) (φ p)‖) := by gcongr
    _ = _ := by ring

end Lightlike.Vortex
