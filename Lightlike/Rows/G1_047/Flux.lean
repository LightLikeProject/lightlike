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

/-- **Circulation of `e A` at infinity.** With `φ ∈ C¹`, `A_j` continuous, `|φ|² → v² ≠ 0`,
`r ‖D_jφ‖ → 0` and winding number `n` (`∮ dθ = 2π n` on large squares),
`e ∮_{∂[−R,R]²} (A₂ dy − A₁ dx) → 2π n`. -/
theorem tendsto_bdy_A (e v : ℝ) (n : ℤ) (hv : v ≠ 0) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hA₁ : Continuous A₁) (hA₂ : Continuous A₂)
    (hinf : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2)))
    (h₁ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * ‖covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p)‖)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (h₂ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * ‖covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p)‖)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (hw : ∀ᶠ R in atTop,
      bdy (windingForm φ (1, 0)) (windingForm φ (0, 1)) R = 2 * Real.pi * n) :
    Tendsto (fun R => e * bdy A₁ A₂ R) atTop (nhds (2 * Real.pi * n)) := by
  obtain ⟨R₀, hR₀⟩ := exists_ne_zero_of_tendsto_normSq hv hinf
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hw
  have d₁ := tendsto_delta e v hv (A := A₁) (1, 0) hinf h₁
  have d₂ := tendsto_delta e v hv (A := A₂) (0, 1) hinf h₂
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r₁, hr₁⟩ := decay_bound d₁ (c := ε / 16) (by positivity)
  obtain ⟨r₂, hr₂⟩ := decay_bound d₂ (c := ε / 16) (by positivity)
  refine ⟨max (max N₁ (max r₁ r₂)) (max R₀ 1), fun R hR => ?_⟩
  have hRN : N₁ ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hRr₁ : r₁ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hR))
  have hRr₂ : r₂ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hR))
  have hRR₀ : R₀ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hR1 : 1 ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRpos : 0 < R := by linarith
  have hsph : ∀ p : ℝ × ℝ, ‖p‖ = R → φ p ≠ 0 := fun p hp => hR₀ p (by rw [hp]; exact hRR₀)
  have hwf : ∀ u : ℝ × ℝ, ContinuousOn (windingForm φ u) {p | ‖p‖ = R} := fun u p hp =>
    (continuousAt_windingForm hφ u (hsph p hp)).continuousWithinAt
  have hδ : ∀ (A : ℝ × ℝ → ℝ) (u : ℝ × ℝ), Continuous A →
      ContinuousOn (fun p => windingForm φ u p - e * A p) {p | ‖p‖ = R} := fun A u hA =>
    (hwf u).sub (continuous_const.mul hA).continuousOn
  have hlin := bdy_lin e hRpos.le hA₁.continuousOn hA₂.continuousOn
    (hδ A₁ (1, 0) hA₁) (hδ A₂ (0, 1) hA₂)
  simp only [add_sub_cancel] at hlin
  rw [hN₁ R hRN] at hlin
  have hb : |bdy (fun p => windingForm φ (1, 0) p - e * A₁ p)
      (fun p => windingForm φ (0, 1) p - e * A₂ p) R| ≤ 8 * R * (ε / 16 / R) := by
    refine bdy_abs_le hRpos.le fun p hp => ⟨?_, ?_⟩
    · have := hr₁ p (by rw [hp]; exact hRr₁)
      rw [hp, abs_of_nonneg (mul_nonneg hRpos.le (abs_nonneg _))] at this
      rw [le_div_iff₀ hRpos]; linarith
    · have := hr₂ p (by rw [hp]; exact hRr₂)
      rw [hp, abs_of_nonneg (mul_nonneg hRpos.le (abs_nonneg _))] at this
      rw [le_div_iff₀ hRpos]; linarith
  have h8 : 8 * R * (ε / 16 / R) = ε / 2 := by field_simp; ring
  rw [h8] at hb
  rw [Real.dist_eq]
  have : e * bdy A₁ A₂ R - 2 * Real.pi * n =
      -bdy (fun p => windingForm φ (1, 0) p - e * A₁ p)
        (fun p => windingForm φ (0, 1) p - e * A₂ p) R := by
    linarith
  rw [this, abs_neg]
  linarith

/-- **Flux quantisation (CO24).** Under the hypotheses of `tendsto_bdy_A` (and `φ, A_j ∈ C¹`),
the flux through `[−R, R]²` satisfies `e ∫∫ B → 2π n`, `B = ∂₁A₂ − ∂₂A₁`; i.e. the total flux is
`2π n / e` for `e ≠ 0`. -/
theorem flux_tendsto (e v : ℝ) (n : ℤ) (hv : v ≠ 0) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hinf : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2)))
    (h₁ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * ‖covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p)‖)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (h₂ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * ‖covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p)‖)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (hw : ∀ᶠ R in atTop,
      bdy (windingForm φ (1, 0)) (windingForm φ (0, 1)) R = 2 * Real.pi * n) :
    Tendsto (fun R : ℝ => e * ∫ x in (-R)..R, ∫ y in (-R)..R,
        (fderiv ℝ A₂ (x, y) (1, 0) - fderiv ℝ A₁ (x, y) (0, 1))) atTop
      (nhds (2 * Real.pi * n)) := by
  simp only [box_flux_eq_bdy hA₁ hA₂]
  exact tendsto_bdy_A e v n hv hφ hA₁.continuous hA₂.continuous hinf h₁ h₂ hw

end Lightlike.Vortex
