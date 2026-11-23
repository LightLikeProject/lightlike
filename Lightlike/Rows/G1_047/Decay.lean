import Lightlike.Rows.G1_047.Bundle

/-!
# Decay of the error term from natural hypotheses (CO24)

`bogomolny_bound` assumes `‖p‖ · |errTerm| → 0`.  Here this is derived from the natural
hypotheses `|φ|² → v²` (with `v ≠ 0`) and
`‖p‖ · ||φ|² − v²| · (|A| + ‖Dφ‖) → 0`: the winding form is bounded by `‖Dφ‖/|φ|`, and
`|φ|` is bounded below near infinity.

## Main results

* `abs_windingForm_mul_le`: `|dθ_u| · |φ| ≤ ‖Dφ‖ ‖u‖`.
* `errTerm_eq`: `errTerm = (|φ|² − v²) (dθ_u − e A)`.
* `tendsto_errTerm`: the decay of `‖p‖ · |errTerm|`.
* `exists_ne_zero_of_tendsto_normSq`: `|φ|² → v² ≠ 0` implies `φ ≠ 0` near infinity.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set Filter

/-- Eventually in `cobounded (ℝ × ℝ)` is the same as outside a ball. -/
theorem exists_norm_of_eventually {P : ℝ × ℝ → Prop}
    (h : ∀ᶠ p in Bornology.cobounded (ℝ × ℝ), P p) : ∃ r : ℝ, ∀ p : ℝ × ℝ, r ≤ ‖p‖ → P p := by
  obtain ⟨r, -, hr⟩ :=
    ((Metric.hasBasis_cobounded_compl_closedBall (0 : ℝ × ℝ)).eventually_iff).mp h
  refine ⟨r + 1, fun p hp => hr (x := p) ?_⟩
  simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  linarith

/-- `|dθ_u| · |φ| ≤ ‖Dφ‖ ‖u‖`. -/
theorem abs_windingForm_mul_le (φ : ℝ × ℝ → ℂ) (u p : ℝ × ℝ) (hp : φ p ≠ 0) :
    |windingForm φ u p| * ‖φ p‖ ≤ ‖fderiv ℝ φ p‖ * ‖u‖ := by
  have hpos : 0 < ‖φ p‖ := norm_pos_iff.mpr hp
  have h1 : |((starRingEnd ℂ) (φ p) * fderiv ℝ φ p u).im| ≤ ‖φ p‖ * (‖fderiv ℝ φ p‖ * ‖u‖) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left ((fderiv ℝ φ p).le_opNorm u) hpos.le
  unfold windingForm
  rw [Complex.normSq_eq_norm_sq, abs_div, abs_of_pos (by positivity : 0 < ‖φ p‖ ^ 2),
    div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- `errTerm = (|φ|² − v²) (dθ_u − e A)`. -/
theorem errTerm_eq (e v : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u p : ℝ × ℝ) :
    errTerm e v A φ u p =
      (Complex.normSq (φ p) - v ^ 2) * (windingForm φ u p - e * A p) := by
  unfold errTerm; ring

/-- If `|φ|² → v² ≠ 0` then `|φ| ≥ |v|/2` outside a ball. -/
theorem exists_norm_ge_of_tendsto_normSq {v : ℝ} (hv : v ≠ 0) {φ : ℝ × ℝ → ℂ}
    (hφ : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2))) :
    ∃ r : ℝ, ∀ p : ℝ × ℝ, r ≤ ‖p‖ → |v| / 2 ≤ ‖φ p‖ := by
  have hv2 : 0 < v ^ 2 := by positivity
  have h := hφ.eventually (Ioi_mem_nhds (by linarith : v ^ 2 / 2 < v ^ 2))
  obtain ⟨r, hr⟩ := exists_norm_of_eventually h
  refine ⟨r, fun p hp => ?_⟩
  have h1 : v ^ 2 / 2 < Complex.normSq (φ p) := hr p hp
  rw [Complex.normSq_eq_norm_sq] at h1
  by_contra hc
  rw [not_le] at hc
  have h0 : 0 ≤ ‖φ p‖ := norm_nonneg _
  have : ‖φ p‖ ^ 2 < (|v| / 2) ^ 2 := by nlinarith
  have hs : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith

/-- `|φ|² → v² ≠ 0` implies `φ ≠ 0` near infinity (the form of `hne` in `bogomolny_bound`). -/
theorem exists_ne_zero_of_tendsto_normSq {v : ℝ} (hv : v ≠ 0) {φ : ℝ × ℝ → ℂ}
    (hφ : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2))) :
    ∃ R₀ : ℝ, ∀ p : ℝ × ℝ, R₀ ≤ ‖p‖ → φ p ≠ 0 := by
  obtain ⟨r, hr⟩ := exists_norm_ge_of_tendsto_normSq hv hφ
  refine ⟨r, fun p hp h0 => ?_⟩
  have := hr p hp
  rw [h0, norm_zero] at this
  have : 0 < |v| := abs_pos.mpr hv
  linarith

/-- **Decay of the error term.** If `|φ|² → v² ≠ 0` and
`‖p‖ · ||φ|² − v²| · (|A| + ‖Dφ‖) → 0`, then `‖p‖ · |errTerm_u| → 0` for `‖u‖ ≤ 1`. -/
theorem tendsto_errTerm (e v : ℝ) (hv : v ≠ 0) {A : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} {u : ℝ × ℝ}
    (hu : ‖u‖ ≤ 1)
    (hφ : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2)))
    (h : Tendsto (fun p : ℝ × ℝ => ‖p‖ * |Complex.normSq (φ p) - v ^ 2| *
        (|A p| + ‖fderiv ℝ φ p‖)) (Bornology.cobounded (ℝ × ℝ)) (nhds 0)) :
    Tendsto (fun p : ℝ × ℝ => ‖p‖ * |errTerm e v A φ u p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0) := by
  have hav : 0 < |v| := abs_pos.mpr hv
  obtain ⟨r, hr⟩ := exists_norm_ge_of_tendsto_normSq hv hφ
  have hK : 0 ≤ |e| + 2 / |v| := by positivity
  have hlim : Tendsto (fun p : ℝ × ℝ => (|e| + 2 / |v|) * (‖p‖ * |Complex.normSq (φ p) - v ^ 2| *
        (|A p| + ‖fderiv ℝ φ p‖))) (Bornology.cobounded (ℝ × ℝ)) (nhds 0) := by
    simpa using h.const_mul (|e| + 2 / |v|)
  refine squeeze_zero' (Eventually.of_forall fun p => by positivity) ?_ hlim
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop r] with p hp
  have hφp := hr p hp
  have hne : φ p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hφp
    linarith
  have hw := abs_windingForm_mul_le φ u p hne
  have hd0 : 0 ≤ ‖fderiv ℝ φ p‖ := norm_nonneg _
  have hwf0 : 0 ≤ |windingForm φ u p| := abs_nonneg _
  have hw1 : |windingForm φ u p| * (|v| / 2) ≤ ‖fderiv ℝ φ p‖ := by
    calc |windingForm φ u p| * (|v| / 2) ≤ |windingForm φ u p| * ‖φ p‖ :=
          mul_le_mul_of_nonneg_left hφp hwf0
      _ ≤ ‖fderiv ℝ φ p‖ * ‖u‖ := hw
      _ ≤ ‖fderiv ℝ φ p‖ * 1 := mul_le_mul_of_nonneg_left hu hd0
      _ = _ := mul_one _
  have hw2 : |windingForm φ u p| ≤ 2 / |v| * ‖fderiv ℝ φ p‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hav]
    linarith
  have hw3 : |windingForm φ u p - e * A p| ≤ (|e| + 2 / |v|) * (|A p| + ‖fderiv ℝ φ p‖) := by
    have h1 := abs_sub (windingForm φ u p) (e * A p)
    rw [abs_mul] at h1
    have h2 : 0 ≤ 2 / |v| := by positivity
    have h3 : 0 ≤ |A p| := abs_nonneg _
    have h4 : 0 ≤ |e| := abs_nonneg _
    nlinarith [mul_nonneg h2 h3, mul_nonneg h4 hd0]
  rw [errTerm_eq, abs_mul]
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg _
  calc ‖p‖ * (|Complex.normSq (φ p) - v ^ 2| * |windingForm φ u p - e * A p|)
      ≤ ‖p‖ * (|Complex.normSq (φ p) - v ^ 2| *
          ((|e| + 2 / |v|) * (|A p| + ‖fderiv ℝ φ p‖))) := by
        gcongr
    _ = _ := by ring

/-- **Bogomolny bound (CO24), natural hypotheses.** `φ ∈ C²`, `A_j ∈ C¹`, `v ≠ 0`,
`|φ|² → v²` and `‖p‖ · ||φ|² − v²| · (|A_j| + ‖Dφ‖) → 0` at infinity, winding number `n`
(`∮ dθ = 2π n` on large squares) and energy in every square `[−R, R]²` at critical coupling
`λ = 2e²` at most `E`. Then `2π |n| v² ≤ E`. -/
theorem bogomolny_bound_of_decay (e v : ℝ) (n : ℤ) (E : ℝ) (hv : v ≠ 0)
    {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hinf : Tendsto (fun p => Complex.normSq (φ p)) (Bornology.cobounded (ℝ × ℝ)) (nhds (v ^ 2)))
    (h₁ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * |Complex.normSq (φ p) - v ^ 2| *
        (|A₁ p| + ‖fderiv ℝ φ p‖)) (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (h₂ : Tendsto (fun p : ℝ × ℝ => ‖p‖ * |Complex.normSq (φ p) - v ^ 2| *
        (|A₂ p| + ‖fderiv ℝ φ p‖)) (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (hw : ∀ᶠ R in atTop,
      bdy (windingForm φ (1, 0)) (windingForm φ (0, 1)) R = 2 * Real.pi * n)
    (hE : ∀ R : ℝ, 0 ≤ R →
      (∫ x in (-R)..R, ∫ y in (-R)..R, bogoEnergy e v A₁ A₂ φ (x, y)) ≤ E) :
    2 * Real.pi * |(n : ℝ)| * v ^ 2 ≤ E :=
  bogomolny_bound e v n E hφ hA₁ hA₂ (exists_ne_zero_of_tendsto_normSq hv hinf)
    (tendsto_errTerm e v hv (by simp [Prod.norm_def]) hinf h₁)
    (tendsto_errTerm e v hv (by simp [Prod.norm_def]) hinf h₂) hw hE

end Lightlike.Vortex
