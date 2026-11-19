import Lightlike.Asymptotics.Tauberian.Window2
import Lightlike.Asymptotics.Tauberian.FourierBound
import Lightlike.Asymptotics.Tauberian.Remainder
import Lightlike.Asymptotics.Tauberian.CrossingMeasure
import Lightlike.Asymptotics.Tauberian.Negligible

/-!
# The local bound (MZ (5.14)), upper side

For `σ` satisfying MZ's hypotheses and `δ > 0`: `σ [Δ - δ, Δ + δ] ≤ K Δ^{-3/4} e^{2 √(a Δ)}` for large `Δ`
(`a = 4π² v`).
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

/-- **The difference of two Fourier representations.** -/
lemma difference_representation (σ ρ : Measure ℝ) [SFinite σ] [SFinite ρ] {β b Δ : ℝ}
    (hσ : Integrable (fun x : ℝ => Real.exp (-β * x)) σ)
    (hρ : Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {g : ℝ → ℝ} (hgi : Integrable g)
    (hg : ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ)) (hβ : 0 < β) :
    (((∫ x, (2 * b * Real.sinc (b * (x - Δ))) ^ 4 * Real.exp (-β * x) ∂σ) -
        ∫ x, (2 * b * Real.sinc (b * (x - Δ))) ^ 4 * Real.exp (-β * x) ∂ρ : ℝ) : ℂ) =
      ∫ t, (g t : ℂ) * Complex.exp (t * Δ * Complex.I) *
        (laplaceC σ (β + t * Complex.I) - laplaceC ρ (β + t * Complex.I)) := by
  have hgt : Integrable (fun t : ℝ => (g t : ℂ) * Complex.exp (t * Δ * Complex.I)) := by
    refine hgi.ofReal.mul_bdd (by fun_prop : Continuous fun t : ℝ => Complex.exp (t * Δ * Complex.I)).aestronglyMeasurable
      (c := 1) (Filter.Eventually.of_forall fun t => ?_)
    rw [Complex.norm_exp]; simp
  have h1 := fourier_representation σ hβ hσ hgi hg (Δ := Δ)
  have h2 := fourier_representation ρ hβ hρ hgi hg (Δ := Δ)
  have i1 := integrable_fourier_laplace σ hσ hgt
  have i2 := integrable_fourier_laplace ρ hρ hgt
  push_cast
  rw [h1, h2, ← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring

/-- **The difference of the Laplace transforms is exponentially smaller.** -/
lemma delta_bound {σ : Measure ℝ} {v g C β₀ : ℝ} (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z))
    {Λ β₁ : ℝ} (hΛ : 0 ≤ Λ) (hq : (β₁ ^ 2 + Λ ^ 2) / (4 * Real.pi ^ 2) < 1) (hβ₁ : 0 < β₁) :
    ∃ θ K : ℝ, θ < 1 ∧ 0 ≤ K ∧ ∀ β t : ℝ, 0 < β → β ≤ β₁ → |t| ≤ Λ →
      ‖laplaceC σ (β + t * Complex.I) - laplaceC (rho0 (4 * Real.pi ^ 2 * v)) (β + t * Complex.I)‖ ≤
        K * Real.exp (θ * (4 * Real.pi ^ 2 * v) / β) := by
  obtain ⟨θ, K, hθ, hK, hbd⟩ := H.psi_bound hΛ hq hβ₁
  refine ⟨θ, K, hθ, hK, fun β t hβ hββ₁ ht => ?_⟩
  have hre : (β + t * Complex.I : ℂ).re = β := by simp
  have hpos : 0 < (β + t * Complex.I : ℂ).re := by rw [hre]; exact hβ
  have ha : 0 < 4 * Real.pi ^ 2 * v := by have := H.hv; positivity
  rw [laplaceC_rho0 ha hpos]
  have h1 := complex_remainder H hmodC hpos
  have e : (((4 * Real.pi ^ 2 * v : ℝ) : ℂ)) = 4 * (Real.pi : ℂ) ^ 2 * v := by push_cast; ring
  rw [e]
  refine h1.trans ?_
  rw [hre, Complex.normSq_add_mul_I]
  exact hbd β t hβ hββ₁ ht

lemma sqrt_div_mul (a Δ : ℝ) (ha : 0 < a) (hΔ : 0 < Δ) :
    Real.sqrt (a / Δ) * Δ = Real.sqrt (a * Δ) ∧ a / Real.sqrt (a / Δ) = Real.sqrt (a * Δ) := by
  have hs : 0 < Real.sqrt (a / Δ) := Real.sqrt_pos.2 (by positivity)
  have h2 : Real.sqrt (a / Δ) ^ 2 = a / Δ := Real.sq_sqrt (by positivity)
  have h3 : Real.sqrt (a * Δ) ^ 2 = a * Δ := Real.sq_sqrt (by positivity)
  have h4 : 0 < Real.sqrt (a * Δ) := Real.sqrt_pos.2 (by positivity)
  constructor
  · refine (sq_eq_sq₀ (by positivity) h4.le).1 ?_
    rw [mul_pow, h2, h3]; field_simp
  · rw [div_eq_iff hs.ne']
    refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
    rw [mul_pow, h2, h3]; field_simp

/-- **The local bound (MZ (5.14), upper side).** -/
theorem local_bound {σ : Measure ℝ} [IsFiniteMeasureOnCompacts σ] {v g C β₀ : ℝ}
    (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z))
    {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hbδ : b * δ < Real.pi) (hΛ : 4 * b < 2 * Real.pi) :
    ∃ K Δ₀ : ℝ, 0 ≤ K ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      (σ (Icc (Δ - δ) (Δ + δ))).toReal ≤
        K * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Real.sqrt (4 * Real.pi ^ 2 * v * Δ)) := by
  have hv := H.hv
  have hπ : 0 < Real.pi := Real.pi_pos
  set a : ℝ := 4 * Real.pi ^ 2 * v with ha
  have ha0 : 0 < a := by positivity
  have hs : 0 < Real.sinc (b * δ) := Real.sinc_pos (by rw [abs_of_pos (by positivity)]; exact hbδ)
  set s4 : ℝ := Real.sinc (b * δ) ^ 4 with hs4
  have hs40 : 0 < s4 := by positivity
  -- the parameters of the remainder estimate
  set Λ : ℝ := 4 * b with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  set β₁ : ℝ := Real.sqrt ((4 * Real.pi ^ 2 - Λ ^ 2) / 2) with hβ₁
  have hpos : 0 < 4 * Real.pi ^ 2 - Λ ^ 2 := by nlinarith
  have hβ₁0 : 0 < β₁ := Real.sqrt_pos.2 (by positivity)
  have hq : (β₁ ^ 2 + Λ ^ 2) / (4 * Real.pi ^ 2) < 1 := by
    rw [hβ₁, Real.sq_sqrt (by positivity), div_lt_one (by positivity)]
    linarith
  obtain ⟨θ, K1, hθ, hK1, hδb⟩ := delta_bound H hmodC hΛ0 hq hβ₁0
  obtain ⟨g1, hgi, hg0, hgs, hgt⟩ := exists_fourier_kernel hb
  obtain ⟨C2, hC2, hmain⟩ := main_term_bound (a := a) (b := b) (δ := δ) ha0 hb hδ hbδ
  -- the bound at a fixed `Δ`
  have key : ∀ Δ : ℝ, 1 ≤ Δ → Real.sqrt (a / Δ) ≤ β₁ →
      (σ (Icc (Δ - δ) (Δ + δ))).toReal ≤ Real.exp (β₁ * δ) *
        (Real.exp (Real.sqrt (a * Δ)) / s4 + C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Real.sqrt (a * Δ)) +
          K1 * Real.exp ((1 + θ) * Real.sqrt (a * Δ)) / s4) := by
    intro Δ hΔ hβle
    have hΔ0 : 0 < Δ := by linarith
    set β : ℝ := Real.sqrt (a / Δ) with hβdef
    have hβ : 0 < β := Real.sqrt_pos.2 (by positivity)
    obtain ⟨hβΔ, haβ⟩ := sqrt_div_mul a Δ ha0 hΔ0
    set Y : ℝ := Real.sqrt (a * Δ) with hY
    have hint : Integrable (fun x : ℝ => Real.exp (-β * x)) σ := H.hint β hβ
    -- the majorant and its bound
    set φ : ℝ → ℝ := fun x => majorant (b * δ) (b * (x - Δ)) with hφ
    have hφ0 : ∀ x, 0 ≤ φ x := fun x => majorant_nonneg _ _
    have hφb : ∀ x, φ x ≤ 1 / s4 := by
      intro x
      simp only [hφ, majorant]
      refine div_le_div_of_nonneg_right ?_ hs40.le
      have := Real.abs_sinc_le_one (b * (x - Δ))
      calc Real.sinc (b * (x - Δ)) ^ 4 = |Real.sinc (b * (x - Δ))| ^ 4 := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        _ ≤ 1 := pow_le_one₀ (abs_nonneg _) this
    have hφc : Continuous φ := by simp only [hφ, majorant]; fun_prop
    -- the crossing measure side
    have hρ := integral_rho0 (a := a) (β := β) (M := 1) ha0 hβ
      (F := fun x => Real.exp (-β * x)) (by fun_prop) (fun x hx => by
        rw [abs_of_pos (Real.exp_pos _), one_mul])
    have hρint : Integrable (fun x : ℝ => Real.exp (-β * x)) (rho0 a) := hρ.1
    have hFρ := integral_rho0 (a := a) (β := β) (M := 1 / s4) ha0 hβ
      (F := fun x => φ x * Real.exp (-β * x)) (by simp only [hφ, majorant]; fun_prop) (fun x hx => by
        rw [abs_of_nonneg (mul_nonneg (hφ0 x) (Real.exp_pos _).le)]
        exact mul_le_mul_of_nonneg_right (hφb x) (Real.exp_pos _).le)
    have hΦ : ∀ x : ℝ, (2 * b * Real.sinc (b * (x - Δ))) ^ 4 = (16 * b ^ 4 * s4) * φ x := by
      intro x
      simp only [hφ, majorant, hs4]
      have : 0 < Real.sinc (b * δ) ^ 4 := by positivity
      field_simp
      ring
    have hΦint : ∀ μ : Measure ℝ, ∫ x, (2 * b * Real.sinc (b * (x - Δ))) ^ 4 * Real.exp (-β * x) ∂μ =
        (16 * b ^ 4 * s4) * ∫ x, φ x * Real.exp (-β * x) ∂μ := by
      intro μ
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [hΦ x]; ring
    have hd := difference_representation σ (rho0 a) hint hρint hgi hgt hβ (Δ := Δ)
    have hgint : ∫ t, g1 t = 16 * b ^ 4 := by
      have := hgt 0
      simp [char, Real.sinc_zero] at this
      have h2 : ((∫ t, g1 t : ℝ) : ℂ) = (((2 * b) ^ 4 : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal, this]; push_cast; ring
      have h3 := Complex.ofReal_injective h2
      rw [h3]; ring
    have hM0 : 0 ≤ K1 * Real.exp (θ * a / β) := by positivity
    have hnorm := norm_kernel_integral_le (g := g1) (Λ := 4 * b) (M := K1 * Real.exp (θ * a / β)) hg0 hgs hgi
      (D := fun t => laplaceC σ (β + t * Complex.I) - laplaceC (rho0 a) (β + t * Complex.I))
      (fun t ht => hδb β t hβ hβle ht) hM0 Δ
    rw [← hd, hgint, Complex.norm_real, Real.norm_eq_abs] at hnorm
    rw [hΦint σ, hΦint (rho0 a), ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 16 * b ^ 4 * s4)] at hnorm
    have hAσρ : (∫ x, φ x * Real.exp (-β * x) ∂σ) - ∫ x, φ x * Real.exp (-β * x) ∂(rho0 a) ≤
        K1 * Real.exp (θ * a / β) / s4 := by
      have h1 : 16 * b ^ 4 * s4 * ((∫ x, φ x * Real.exp (-β * x) ∂σ) -
          ∫ x, φ x * Real.exp (-β * x) ∂(rho0 a)) ≤ 16 * b ^ 4 * (K1 * Real.exp (θ * a / β)) :=
        le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)) hnorm
      rw [le_div_iff₀ hs40]
      have hb4 : 0 < 16 * b ^ 4 := by positivity
      nlinarith [h1]
    -- the main term
    have hmainΔ := hmain Δ hΔ
    rw [← hβdef] at hmainΔ
    have hAρ : ∫ x, φ x * Real.exp (-β * x) ∂(rho0 a) =
        φ 0 + ∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x)) := by
      have := hFρ.2
      simpa using this
    have hshift : Real.exp (β * Δ) * ∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x)) =
        ∫ x in Ioi (0 : ℝ), crossingDensity a x * Real.exp (-β * (x - Δ)) *
          majorant (b * δ) (b * (x - Δ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hφ]
      have : Real.exp (β * Δ) * Real.exp (-β * x) = Real.exp (-β * (x - Δ)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp (β * Δ) * (crossingDensity a x * (majorant (b * δ) (b * (x - Δ)) * Real.exp (-β * x)))
          = crossingDensity a x * (Real.exp (β * Δ) * Real.exp (-β * x)) * majorant (b * δ) (b * (x - Δ)) := by ring
        _ = _ := by rw [this]
    -- the window bound
    have hwin := window_le σ hβ hb hδ hbδ hint (Δ := Δ)
    have hcalc : (σ (Icc (Δ - δ) (Δ + δ))).toReal ≤ Real.exp (β * (Δ + δ)) *
        (φ 0 + (∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x))) +
          K1 * Real.exp (θ * a / β) / s4) := by
      refine hwin.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      have : ∫ x, majorant (b * δ) (b * (x - Δ)) * Real.exp (-β * x) ∂σ =
          ∫ x, φ x * Real.exp (-β * x) ∂σ := rfl
      rw [this]
      rw [hAρ] at hAσρ
      linarith
    refine hcalc.trans ?_
    have hexpΔ : Real.exp (β * (Δ + δ)) = Real.exp Y * Real.exp (β * δ) := by
      rw [← Real.exp_add, mul_add, hβΔ]
    have hβδ : Real.exp (β * δ) ≤ Real.exp (β₁ * δ) := Real.exp_le_exp.2 (by nlinarith)
    have hφ0b : φ 0 ≤ 1 / s4 := hφb 0
    have hI0 : 0 ≤ ∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x)) :=
      integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (crossingDensity_nonneg ha0 (le_of_lt hx)) (mul_nonneg (hφ0 x) (Real.exp_pos _).le)))
    have hI1 : Real.exp Y * ∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x)) ≤
        C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
      have := hshift
      rw [hβΔ] at this
      rw [this]
      exact hmainΔ
    have hmain2 : Real.exp (β * (Δ + δ)) * (φ 0 + (∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x))) +
          K1 * Real.exp (θ * a / β) / s4) ≤ Real.exp (β₁ * δ) *
        (Real.exp Y / s4 + C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) + K1 * Real.exp ((1 + θ) * Y) / s4) := by
      rw [hexpΔ]
      have hθa : Real.exp (θ * a / β) = Real.exp (θ * Y) := by rw [mul_div_assoc, haβ]
      have e1 : Real.exp Y * Real.exp (θ * Y) = Real.exp ((1 + θ) * Y) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hθa]
      have hE : 0 ≤ Real.exp (β * δ) := (Real.exp_pos _).le
      have hEY : 0 < Real.exp Y := Real.exp_pos _
      calc Real.exp Y * Real.exp (β * δ) * (φ 0 + (∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x))) +
            K1 * Real.exp (θ * Y) / s4)
          = Real.exp (β * δ) * (Real.exp Y * φ 0 + Real.exp Y * (∫ x in Ioi (0 : ℝ), crossingDensity a x * (φ x * Real.exp (-β * x))) +
            K1 * (Real.exp Y * Real.exp (θ * Y)) / s4) := by ring
        _ ≤ Real.exp (β * δ) * (Real.exp Y / s4 + C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) +
            K1 * Real.exp ((1 + θ) * Y) / s4) := by
            rw [e1]
            refine mul_le_mul_of_nonneg_left ?_ hE
            have : Real.exp Y * φ 0 ≤ Real.exp Y / s4 := by
              calc Real.exp Y * φ 0 ≤ Real.exp Y * (1 / s4) := mul_le_mul_of_nonneg_left hφ0b hEY.le
                _ = Real.exp Y / s4 := by ring
            linarith
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right hβδ ?_
            have : 0 ≤ C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by positivity
            positivity
    exact hmain2
  -- the eventual bound
  have hε1 : 0 < 1 - θ := by linarith
  have h1 := eventually_le_rpow_neg_mul_exp (a := a) (ε := 1) ha0 one_pos
  have h2 := eventually_le_rpow_neg_mul_exp (a := a) (ε := 1 - θ) ha0 hε1
  have h3 : ∀ᶠ Δ : ℝ in Filter.atTop, Real.sqrt (a / Δ) ≤ β₁ := by
    have : Filter.Tendsto (fun Δ : ℝ => Real.sqrt (a / Δ)) Filter.atTop (nhds (Real.sqrt 0)) := by
      have h0 : Filter.Tendsto (fun Δ : ℝ => a / Δ) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop Filter.tendsto_id
      exact (Real.continuous_sqrt.tendsto 0).comp h0
    rw [Real.sqrt_zero] at this
    exact this.eventually (ge_mem_nhds hβ₁0)
  obtain ⟨Δ₀, hΔ₀⟩ := Filter.eventually_atTop.1 (h1.and (h2.and (h3.and (Filter.eventually_ge_atTop 1))))
  refine ⟨Real.exp (β₁ * δ) * (1 / s4 + C2 + K1 / s4), Δ₀, by positivity, fun Δ hΔ => ?_⟩
  obtain ⟨hA, hB, hC, hD⟩ := hΔ₀ Δ hΔ
  refine (key Δ hD hC).trans ?_
  have hΔ0 : 0 < Δ := by linarith
  set Y := Real.sqrt (a * Δ) with hY
  set T := Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) with hT
  have hT0 : 0 ≤ T := by positivity
  have e1 : Real.exp Y ≤ T := by
    have : (2 - 1 : ℝ) * Y = Y := by ring
    rw [this] at hA; exact hA
  have e2 : Real.exp ((1 + θ) * Y) ≤ T := by
    have : (2 - (1 - θ)) * Y = (1 + θ) * Y := by ring
    rw [this] at hB; exact hB
  calc Real.exp (β₁ * δ) * (Real.exp Y / s4 + C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) +
        K1 * Real.exp ((1 + θ) * Y) / s4)
      ≤ Real.exp (β₁ * δ) * (T / s4 + C2 * T + K1 * T / s4) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have a1 : Real.exp Y / s4 ≤ T / s4 := div_le_div_of_nonneg_right e1 hs40.le
        have a2 : C2 * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) = C2 * T := by rw [hT]; ring
        have a3 : K1 * Real.exp ((1 + θ) * Y) / s4 ≤ K1 * T / s4 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hK1) hs40.le
        linarith
    _ = Real.exp (β₁ * δ) * (1 / s4 + C2 + K1 / s4) * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
        rw [hT]; ring

end Lightlike.Tauberian
