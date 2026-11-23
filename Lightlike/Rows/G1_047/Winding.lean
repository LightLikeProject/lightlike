import Lightlike.Rows.G1_047.Energy

/-!
# Boundary integral of `W` and the winding number (CO24)

`bdy F₁ F₂ R` is the counter-clockwise boundary integral `∮ (F₂ dy − F₁ dx)` over the square
`[−R, R]²` (the right-hand side of `box_integral_bogoTerm` with `a = −R`, `b = R`).

The winding form of `φ` is `dθ = Im(conj φ · dφ)/|φ|²` (`windingForm`); `Wfield` splits as
`v² · windingForm + errTerm`, where `errTerm = e A (v² − |φ|²) + (|φ|² − v²) · windingForm` is
the term that decays at infinity. The bound `bdy_abs_le` says that a boundary integral of a
function bounded by `η` on the square of radius `R` is at most `8 R η`.

## Main results

* `bdy`: the boundary integral.
* `windingForm`, `errTerm`, `Wfield_eq`: `W = v² dθ + error`.
* `bdy_abs_le`: `|∮| ≤ 8 R η`.
* `bdy_lin`: linearity of `bdy` on continuous data.
* `bdy_Wfield_tendsto`: if `∮ dθ = 2π n` on large squares and the error term decays faster than
  `1/‖p‖`, then `∮ W → 2π n v²`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set

/-- The counter-clockwise boundary integral `∮ (F₂ dy − F₁ dx)` over the square `[−R, R]²`. -/
def bdy (F₁ F₂ : ℝ × ℝ → ℝ) (R : ℝ) : ℝ :=
  (((∫ x in (-R)..R, -F₁ (x, R)) - ∫ x in (-R)..R, -F₁ (x, -R)) +
      ∫ y in (-R)..R, F₂ (R, y)) - ∫ y in (-R)..R, F₂ (-R, y)

/-- The winding form `dθ = Im(conj φ · ∂_uφ)/|φ|²` of a complex scalar along the direction `u`. -/
def windingForm (φ : ℝ × ℝ → ℂ) (u : ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  ((starRingEnd ℂ) (φ p) * fderiv ℝ φ p u).im / Complex.normSq (φ p)

/-- The part of `W_u` that is expected to decay at infinity:
`e A (v² − |φ|²) + (|φ|² − v²) dθ`. -/
def errTerm (e v : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u : ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  e * A p * (v ^ 2 - Complex.normSq (φ p)) +
    (Complex.normSq (φ p) - v ^ 2) * windingForm φ u p

/-- `W_u = v² dθ + errTerm`. -/
theorem Wfield_eq (e v : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u p : ℝ × ℝ) :
    Wfield e v A φ u p = v ^ 2 * windingForm φ u p + errTerm e v A φ u p := by
  have hJ : current e A φ u p =
      ((starRingEnd ℂ) (φ p) * fderiv ℝ φ p u).im - e * A p * Complex.normSq (φ p) := by
    simp only [current, covD]
    rw [mul_sub, Complex.sub_im]
    congr 1
    have : (starRingEnd ℂ) (φ p) * (I * ((e * A p : ℝ) : ℂ) * φ p) =
        (((e * A p) * Complex.normSq (φ p) : ℝ) : ℂ) * I := by
      have h := Complex.mul_conj (φ p)
      push_cast
      linear_combination (I * (e : ℂ) * (A p : ℂ)) * h
    rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have hns : Complex.normSq (φ p) * windingForm φ u p =
      ((starRingEnd ℂ) (φ p) * fderiv ℝ φ p u).im := by
    unfold windingForm
    by_cases h : Complex.normSq (φ p) = 0
    · have hz : φ p = 0 := Complex.normSq_eq_zero.mp h
      simp [hz]
    · field_simp
  unfold Wfield errTerm
  rw [hJ]
  linear_combination (-1 : ℝ) * hns

/-- A boundary integral of functions bounded by `η` on the sphere `‖p‖ = R` is at most `8 R η`. -/
theorem bdy_abs_le {F₁ F₂ : ℝ × ℝ → ℝ} {R η : ℝ} (hR : 0 ≤ R)
    (h : ∀ p : ℝ × ℝ, ‖p‖ = R → |F₁ p| ≤ η ∧ |F₂ p| ≤ η) :
    |bdy F₁ F₂ R| ≤ 8 * R * η := by
  have hη : 0 ≤ η := by
    have := (h (0, R) (by simp [Prod.norm_def, abs_of_nonneg hR, hR])).1
    exact (abs_nonneg _).trans this
  have edge : ∀ (g : ℝ → ℝ × ℝ) (F : ℝ × ℝ → ℝ), (∀ t ∈ Icc (-R) R, ‖g t‖ = R) →
      (∀ p : ℝ × ℝ, ‖p‖ = R → |F p| ≤ η) →
      |∫ t in (-R)..R, F (g t)| ≤ 2 * R * η := by
    intro g F hg hF
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := R) (C := η)
      (f := fun t => F (g t)) (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hF _ (hg t (by
          rw [uIoc_of_le (by linarith)] at ht
          exact ⟨ht.1.le, ht.2⟩)))
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ R - -R)] at this
    linarith
  have hn : ∀ t ∈ Icc (-R) R, |t| ≤ R := fun t ht => abs_le.mpr ⟨ht.1, ht.2⟩
  have e1 := edge (fun x => (x, R)) (fun p => -F₁ p) (fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]) (fun p hp => by simpa using (h p hp).1)
  have e2 := edge (fun x => (x, -R)) (fun p => -F₁ p) (fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]) (fun p hp => by simpa using (h p hp).1)
  have e3 := edge (fun y => (R, y)) F₂ (fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]) (fun p hp => (h p hp).2)
  have e4 := edge (fun y => (-R, y)) F₂ (fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]) (fun p hp => (h p hp).2)
  unfold bdy
  have := abs_add_le (((∫ x in (-R)..R, -F₁ (x, R)) - ∫ x in (-R)..R, -F₁ (x, -R)) +
      ∫ y in (-R)..R, F₂ (R, y)) (-∫ y in (-R)..R, F₂ (-R, y))
  have h2 := abs_add_le ((∫ x in (-R)..R, -F₁ (x, R)) - ∫ x in (-R)..R, -F₁ (x, -R))
    (∫ y in (-R)..R, F₂ (R, y))
  have h3 := abs_sub (∫ x in (-R)..R, -F₁ (x, R)) (∫ x in (-R)..R, -F₁ (x, -R))
  rw [← sub_eq_add_neg, abs_neg] at this
  beta_reduce at e1 e2 e3 e4
  linarith

/-- The winding form is continuous where `φ ≠ 0` (for `φ ∈ C¹`). -/
theorem continuousAt_windingForm {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (u : ℝ × ℝ)
    {p : ℝ × ℝ} (hp : φ p ≠ 0) : ContinuousAt (windingForm φ u) p := by
  have hd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hnum : Continuous fun q => ((starRingEnd ℂ) (φ q) * fderiv ℝ φ q u).im :=
    Complex.continuous_im.comp
      ((Complex.continuous_conj.comp hφ.continuous).mul (hd.clm_apply continuous_const))
  have hden : Continuous fun q => Complex.normSq (φ q) :=
    Complex.continuous_normSq.comp hφ.continuous
  exact hnum.continuousAt.div hden.continuousAt (Complex.normSq_pos.mpr hp).ne'

/-- `bdy` in terms of plain edge integrals (no integrability needed). -/
theorem bdy_eq (F₁ F₂ : ℝ × ℝ → ℝ) (R : ℝ) :
    bdy F₁ F₂ R = (((-∫ x in (-R)..R, F₁ (x, R)) - -∫ x in (-R)..R, F₁ (x, -R)) +
      ∫ y in (-R)..R, F₂ (R, y)) - ∫ y in (-R)..R, F₂ (-R, y) := by
  simp [bdy, intervalIntegral.integral_neg]

/-- A function continuous on the sphere `‖p‖ = R` is interval integrable along an edge of the
square `[−R, R]²`. -/
theorem edge_ii {F : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R) (hF : ContinuousOn F {p | ‖p‖ = R})
    {g : ℝ → ℝ × ℝ} (hg : Continuous g) (hgR : ∀ t ∈ Icc (-R) R, ‖g t‖ = R) :
    IntervalIntegrable (fun t => F (g t)) volume (-R) R := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith)]
  exact hF.comp hg.continuousOn fun t ht => hgR t ht

/-- Linearity of `bdy` for functions continuous on the sphere `‖p‖ = R`. -/
theorem bdy_lin (c : ℝ) {G₁ G₂ H₁ H₂ : ℝ × ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hG₁ : ContinuousOn G₁ {p | ‖p‖ = R}) (hG₂ : ContinuousOn G₂ {p | ‖p‖ = R})
    (hH₁ : ContinuousOn H₁ {p | ‖p‖ = R}) (hH₂ : ContinuousOn H₂ {p | ‖p‖ = R}) :
    bdy (fun p => c * G₁ p + H₁ p) (fun p => c * G₂ p + H₂ p) R =
      c * bdy G₁ G₂ R + bdy H₁ H₂ R := by
  have hn : ∀ t ∈ Icc (-R) R, |t| ≤ R := fun t ht => abs_le.mpr ⟨ht.1, ht.2⟩
  have n1 : ∀ t ∈ Icc (-R) R, ‖((t, R) : ℝ × ℝ)‖ = R := fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]
  have n2 : ∀ t ∈ Icc (-R) R, ‖((t, -R) : ℝ × ℝ)‖ = R := fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]
  have n3 : ∀ t ∈ Icc (-R) R, ‖((R, t) : ℝ × ℝ)‖ = R := fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]
  have n4 : ∀ t ∈ Icc (-R) R, ‖((-R, t) : ℝ × ℝ)‖ = R := fun t ht => by
    simp [Prod.norm_def, abs_of_nonneg hR, hn t ht]
  have c1 : Continuous fun x : ℝ => ((x, R) : ℝ × ℝ) := by fun_prop
  have c2 : Continuous fun x : ℝ => ((x, -R) : ℝ × ℝ) := by fun_prop
  have c3 : Continuous fun y : ℝ => ((R, y) : ℝ × ℝ) := by fun_prop
  have c4 : Continuous fun y : ℝ => ((-R, y) : ℝ × ℝ) := by fun_prop
  have lin : ∀ (g : ℝ → ℝ × ℝ) (G H : ℝ × ℝ → ℝ), Continuous g →
      (∀ t ∈ Icc (-R) R, ‖g t‖ = R) → ContinuousOn G {p | ‖p‖ = R} →
      ContinuousOn H {p | ‖p‖ = R} →
      ∫ t in (-R)..R, (c * G (g t) + H (g t)) =
        c * (∫ t in (-R)..R, G (g t)) + ∫ t in (-R)..R, H (g t) := by
    intro g G H hg hgR hG hH
    rw [intervalIntegral.integral_add (((edge_ii hR hG hg hgR)).const_mul c) (edge_ii hR hH hg hgR),
      intervalIntegral.integral_const_mul]
  rw [bdy_eq, bdy_eq, bdy_eq]
  rw [lin _ G₁ H₁ c1 n1 hG₁ hH₁, lin _ G₁ H₁ c2 n2 hG₁ hH₁, lin _ G₂ H₂ c3 n3 hG₂ hH₂,
    lin _ G₂ H₂ c4 n4 hG₂ hH₂]
  ring

/-- Extract an `ε`–radius statement from a limit `→ 0` at infinity of `ℝ × ℝ`. -/
theorem decay_bound {f : ℝ × ℝ → ℝ} (h : Filter.Tendsto f (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    {c : ℝ} (hc : 0 < c) : ∃ r : ℝ, ∀ p : ℝ × ℝ, r ≤ ‖p‖ → |f p| < c := by
  have h1 := (Metric.tendsto_nhds.mp h) c hc
  obtain ⟨r, -, hr⟩ := ((Metric.hasBasis_cobounded_compl_closedBall (0 : ℝ × ℝ)).eventually_iff).mp h1
  refine ⟨r + 1, fun p hp => ?_⟩
  have := hr (x := p) (by
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    linarith)
  simpa [Real.dist_eq] using this

/-- **Boundary integral of `W` at infinity.** Let `φ ∈ C¹`, `A_j` continuous, `φ ≠ 0` near
infinity, with `‖p‖ · |errTerm| → 0` at infinity (decay of `e A (v² − |φ|²)` and of
`(|φ|² − v²) dθ`), and winding number `n`, i.e. `∮ dθ = 2π n` on all large squares. Then
`∮_{∂[−R,R]²} (W₂ dy − W₁ dx) → 2π n v²`. -/
theorem bdy_Wfield_tendsto (e v : ℝ) (n : ℤ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hA₁ : Continuous A₁) (hA₂ : Continuous A₂)
    (hne : ∃ R₀ : ℝ, ∀ p : ℝ × ℝ, R₀ ≤ ‖p‖ → φ p ≠ 0)
    (h₁ : Filter.Tendsto (fun p : ℝ × ℝ => ‖p‖ * |errTerm e v A₁ φ (1, 0) p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (h₂ : Filter.Tendsto (fun p : ℝ × ℝ => ‖p‖ * |errTerm e v A₂ φ (0, 1) p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (hw : ∀ᶠ R in Filter.atTop,
      bdy (windingForm φ (1, 0)) (windingForm φ (0, 1)) R = 2 * Real.pi * n) :
    Filter.Tendsto (fun R => bdy (Wfield e v A₁ φ (1, 0)) (Wfield e v A₂ φ (0, 1)) R)
      Filter.atTop (nhds (2 * Real.pi * n * v ^ 2)) := by
  obtain ⟨R₀, hR₀⟩ := hne
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hw
  have hW₁ : Wfield e v A₁ φ (1, 0) =
      fun p => v ^ 2 * windingForm φ (1, 0) p + errTerm e v A₁ φ (1, 0) p :=
    funext (Wfield_eq e v A₁ φ (1, 0))
  have hW₂ : Wfield e v A₂ φ (0, 1) =
      fun p => v ^ 2 * windingForm φ (0, 1) p + errTerm e v A₂ φ (0, 1) p :=
    funext (Wfield_eq e v A₂ φ (0, 1))
  rw [hW₁, hW₂]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r₁, hr₁⟩ := decay_bound h₁ (c := ε / 16) (by positivity)
  obtain ⟨r₂, hr₂⟩ := decay_bound h₂ (c := ε / 16) (by positivity)
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
  have hnS : Continuous fun p => Complex.normSq (φ p) :=
    Complex.continuous_normSq.comp hφ.continuous
  have herr : ∀ (A : ℝ × ℝ → ℝ) (u : ℝ × ℝ), Continuous A →
      ContinuousOn (errTerm e v A φ u) {p | ‖p‖ = R} := fun A u hA => by
    unfold errTerm
    exact ((continuous_const.mul hA).mul (continuous_const.sub hnS)).continuousOn.add
      ((hnS.sub continuous_const).continuousOn.mul (hwf u))
  rw [bdy_lin (v ^ 2) hRpos.le (hwf _) (hwf _) (herr _ _ hA₁) (herr _ _ hA₂),
    hN₁ R hRN]
  have hb : |bdy (errTerm e v A₁ φ (1, 0)) (errTerm e v A₂ φ (0, 1)) R| ≤ 8 * R * (ε / 16 / R) := by
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
  have : v ^ 2 * (2 * Real.pi * n) + bdy (errTerm e v A₁ φ (1, 0)) (errTerm e v A₂ φ (0, 1)) R -
      2 * Real.pi * n * v ^ 2 = bdy (errTerm e v A₁ φ (1, 0)) (errTerm e v A₂ φ (0, 1)) R := by
    ring
  rw [this]
  linarith

end Lightlike.Vortex
