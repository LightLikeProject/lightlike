import Lightlike.Asymptotics.Tauberian.Vacuum
import Lightlike.Asymptotics.Tauberian.ComplexLaplace
import Lightlike.Asymptotics.Tauberian.FourierExchange

/-!
# The non-vacuum part of the partition function

With the vacuum atom `σ{-v} = 1` and no mass below `-v` (`Vacuum.lean`), `Z = e^{-vβ·(-1)} + Z'` with
`Z'(β) = ∫_{x > -v} e^{-β x} dσ`. This file bounds `R(β) = e^{-vβ} Z'(β) = ∫_{x>-v} e^{-β (x+v)} dσ`
for all `β > 0` from the high-temperature form of MZ and modular invariance.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- `R(β) = ∫_{x > -v} e^{-β (x + v)} dσ`. -/
def remainderR (σ : Measure ℝ) (v β : ℝ) : ℝ := ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ

lemma remainderR_nonneg (σ : Measure ℝ) (v β : ℝ) : 0 ≤ remainderR σ v β :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- `R` is decreasing in `β`. -/
lemma remainderR_antitone (σ : Measure ℝ) {v β₁ β₂ : ℝ} (h : β₁ ≤ β₂) (hβ₁ : 0 < β₁)
    (hint : Integrable (fun x : ℝ => Real.exp (-β₁ * x)) σ) :
    remainderR σ v β₂ ≤ remainderR σ v β₁ := by
  have hint' : IntegrableOn (fun x : ℝ => Real.exp (-β₁ * (x + v))) (Ioi (-v)) σ := by
    have h1 : ∀ x : ℝ, Real.exp (-(v * β₁)) * Real.exp (-β₁ * x) = Real.exp (-β₁ * (x + v)) := fun x => by
      rw [← Real.exp_add]; congr 1; ring
    exact (((hint).const_mul (Real.exp (-(v * β₁)))).congr (Filter.Eventually.of_forall fun x => h1 x)).integrableOn
  unfold remainderR
  refine setIntegral_mono_on ?_ hint' measurableSet_Ioi fun x hx => ?_
  · refine hint'.mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-β₂ * (x + v))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : 0 < x + v := by simp only [mem_Ioi] at hx; linarith
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 (by nlinarith)
  · have hx' : 0 < x + v := by simp only [mem_Ioi] at hx; linarith
    exact Real.exp_le_exp.2 (by nlinarith)

/-- **MZ's hypotheses** on a positive measure `σ` (in the variable `x = Δ - c/12`, `v = c/12`,
`a = 4π² v`): `Z(β) = ∫ e^{-β x} dσ` is finite, real modular invariance, and the high-temperature
form. -/
structure SpectralHyp (σ : Measure ℝ) (v g C β₀ : ℝ) : Prop where
  hv : 0 < v
  hg : 0 < g
  hβ₀ : 0 < β₀
  hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) σ
  hmod : ∀ β : ℝ, 0 < β → ∫ x, Real.exp (-β * x) ∂σ = ∫ x, Real.exp (-(4 * Real.pi ^ 2 / β) * x) ∂σ
  hasym : ∀ β : ℝ, 0 < β → β < β₀ →
    |(∫ x, Real.exp (-β * x) ∂σ) - Real.exp (4 * Real.pi ^ 2 * v / β)| ≤
      C * Real.exp ((4 * Real.pi ^ 2 * v - g) / β)

namespace SpectralHyp

variable {σ : Measure ℝ} {v g C β₀ : ℝ}

/-- The consequences of `vacuum_gap_of_modular`. -/
lemma vacuum_gap (H : SpectralHyp σ v g C β₀) : σ (Iio (-v)) = 0 ∧ σ.real {-v} = 1 ∧
    σ (Ioo (-v) (-v + g / (4 * Real.pi ^ 2))) = 0 :=
  vacuum_gap_of_modular σ H.hv H.hg H.hβ₀ H.hint H.hmod H.hasym

/-- `R(β) = e^{-vβ} Z(β) - 1`. -/
lemma remainder_eq (H : SpectralHyp σ v g C β₀) {β : ℝ} (hβ : 0 < β) :
    remainderR σ v β = Real.exp (-(v * β)) * (∫ x, Real.exp (-β * x) ∂σ) - 1 := by
  have h := exp_mul_Z_eq σ H.vacuum_gap.1 hβ (H.hint β hβ)
  rw [H.vacuum_gap.2.1] at h
  unfold remainderR
  linarith

lemma C_nonneg (H : SpectralHyp σ v g C β₀) : 0 ≤ C := by
  have h := H.hasym (β₀ / 2) (by linarith [H.hβ₀]) (by linarith [H.hβ₀])
  have h0 := abs_nonneg ((∫ x, Real.exp (-(β₀ / 2) * x) ∂σ) -
    Real.exp (4 * Real.pi ^ 2 * v / (β₀ / 2)))
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_neg_of_pos hneg (Real.exp_pos ((4 * Real.pi ^ 2 * v - g) / (β₀ / 2)))]

/-- **`R(β) ≤ C₁ e^{a/β}` for every `β > 0`** (`a = 4π² v`). -/
lemma remainder_le_exp (H : SpectralHyp σ v g C β₀) {β : ℝ} (hβ : 0 < β) :
    remainderR σ v β ≤ (1 + C) * Real.exp (2 * (4 * Real.pi ^ 2 * v) / β₀) *
      Real.exp (4 * Real.pi ^ 2 * v / β) := by
  have hC := H.C_nonneg
  have hπv : 0 < 4 * Real.pi ^ 2 * v := by have := H.hv; positivity
  -- the case `β < β₀`
  have small : ∀ β : ℝ, 0 < β → β < β₀ →
      remainderR σ v β ≤ (1 + C) * Real.exp (4 * Real.pi ^ 2 * v / β) := by
    intro β hβ hlt
    have h1 := H.hasym β hβ hlt
    have h2 : (∫ x, Real.exp (-β * x) ∂σ) ≤
        (1 + C) * Real.exp (4 * Real.pi ^ 2 * v / β) := by
      have := (abs_le.1 h1).2
      have h3 : Real.exp ((4 * Real.pi ^ 2 * v - g) / β) ≤ Real.exp (4 * Real.pi ^ 2 * v / β) :=
        Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [H.hg]) hβ.le)
      nlinarith [mul_le_mul_of_nonneg_left h3 hC]
    have hZ0 : 0 ≤ ∫ x, Real.exp (-β * x) ∂σ := integral_nonneg fun _ => (Real.exp_pos _).le
    rw [H.remainder_eq hβ]
    have hv0 : Real.exp (-(v * β)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [H.hv])
    nlinarith [mul_le_mul_of_nonneg_right hv0 hZ0]
  have hbig : 1 ≤ Real.exp (2 * (4 * Real.pi ^ 2 * v) / β₀) :=
    Real.one_le_exp (by have := H.hβ₀; positivity)
  have hbig2 : 1 ≤ Real.exp (4 * Real.pi ^ 2 * v / β) := Real.one_le_exp (by positivity)
  by_cases hlt : β < β₀
  · refine (small β hβ hlt).trans ?_
    have : 0 ≤ (1 + C) * Real.exp (4 * Real.pi ^ 2 * v / β) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hbig this]
  · push Not at hlt
    have hhalf : 0 < β₀ / 2 := by linarith [H.hβ₀]
    have h1 := small (β₀ / 2) hhalf (by linarith [H.hβ₀])
    have h2 := remainderR_antitone σ (v := v) (by linarith [H.hβ₀] : β₀ / 2 ≤ β) hhalf (H.hint _ hhalf)
    have e : 4 * Real.pi ^ 2 * v / (β₀ / 2) = 2 * (4 * Real.pi ^ 2 * v) / β₀ := by
      field_simp
    rw [e] at h1
    refine h2.trans (h1.trans ?_)
    have h4 : 0 ≤ (1 + C) * Real.exp (2 * (4 * Real.pi ^ 2 * v) / β₀) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hbig2 h4]

/-- **`R(β) ≤ C e^{-(g/4π²) β}` at low temperature.** -/
lemma remainder_le_large (H : SpectralHyp σ v g C β₀) {β : ℝ} (hβ : 4 * Real.pi ^ 2 / β₀ + 1 ≤ β) :
    remainderR σ v β ≤ C * Real.exp (-(g / (4 * Real.pi ^ 2) * β)) := by
  have hβ0 : 0 < β := by
    have : 0 < 4 * Real.pi ^ 2 / β₀ := by have := H.hβ₀; positivity
    linarith
  rw [H.remainder_eq hβ0]
  exact (le_abs_self _).trans (low_temp_bound σ H.hv H.hβ₀ H.hmod H.hasym hβ)

end SpectralHyp

/-- The real part of `4π²/z` for `z = β + i t`: `4π² β / (β² + t²)`. -/
lemma re_four_pi_sq_div (z : ℂ) : (4 * (Real.pi : ℂ) ^ 2 / z).re = 4 * Real.pi ^ 2 * z.re / Complex.normSq z := by
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
  norm_num

/-- **The complex decomposition.** For a measure with no mass below `-v` and an atom of mass `1` at `-v`,
`Z(w) = e^{w v} + Z'(w)` with `Z'(w) = ∫_{x > -v} e^{-w x} dσ`, for `Re w > 0`. -/
lemma laplaceC_eq_atom_add (σ : Measure ℝ) {v : ℝ} (hno : σ (Iio (-v)) = 0) (hatom : σ.real {-v} = 1)
    {w : ℂ} (hw : 0 < w.re) (hint : Integrable (fun x : ℝ => Real.exp (-w.re * x)) σ) :
    laplaceC σ w = Complex.exp (w * v) + ∫ x in Ioi (-v), Complex.exp (-(w * x)) ∂σ := by
  have hae : ∀ᵐ x ∂σ, x ∉ Iio (-v) := measure_eq_zero_iff_ae_notMem.1 hno
  have hintC : Integrable (fun x : ℝ => Complex.exp (-(w * x))) σ := by
    refine (integrable_norm_iff ?_).mp ?_
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(w * x))).aestronglyMeasurable
    · refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [Complex.norm_exp]
  have hsplit : Set.univ =ᵐ[σ] ({-v} ∪ Ioi (-v) : Set ℝ) := by
    filter_upwards [hae] with x hx
    simp only [mem_Iio, not_lt] at hx
    simp only [eq_iff_iff, mem_univ, mem_union, mem_singleton_iff, mem_Ioi, true_iff]
    rcases eq_or_lt_of_le hx with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hres : σ.restrict ({-v} ∪ Ioi (-v)) = σ := by
    rw [← Measure.restrict_congr_set hsplit, Measure.restrict_univ]
  unfold laplaceC
  have hU : ∫ x, Complex.exp (-(w * x)) ∂σ =
      ∫ x in ({-v} ∪ Ioi (-v) : Set ℝ), Complex.exp (-(w * x)) ∂σ := by rw [hres]
  rw [hU, setIntegral_union (by simp) measurableSet_Ioi hintC.integrableOn hintC.integrableOn]
  congr 1
  have h1 : ∫ x in ({-v} : Set ℝ), Complex.exp (-(w * x)) ∂σ =
      ∫ x in ({-v} : Set ℝ), Complex.exp (w * v) ∂σ := by
    refine setIntegral_congr_fun (measurableSet_singleton _) fun x hx => ?_
    rw [mem_singleton_iff.1 hx]
    congr 1
    push_cast
    ring
  rw [h1, setIntegral_const, hatom, one_smul]

/-- `‖Z'(w)‖ ≤ e^{v β} R(β)` with `β = Re w`. -/
lemma norm_Ioi_le (σ : Measure ℝ) (v : ℝ) {w : ℂ}
    (hint : Integrable (fun x : ℝ => Real.exp (-w.re * x)) σ) :
    ‖∫ x in Ioi (-v), Complex.exp (-(w * x)) ∂σ‖ ≤ Real.exp (v * w.re) * remainderR σ v w.re := by
  refine (norm_integral_le_integral_norm _).trans ?_
  unfold remainderR
  rw [← integral_const_mul]
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
  simp only [Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp
  ring

/-- **The remainder estimate** (MZ (5.18)): under complex modular invariance,
`‖Z(z) - e^{4π² v / z}‖ ≤ e^{v β'} R(β')` with `β' = Re (4π²/z) = 4π² Re z/|z|²`. -/
theorem complex_remainder {σ : Measure ℝ} {v g C β₀ : ℝ} (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z))
    {z : ℂ} (hz : 0 < z.re) :
    ‖laplaceC σ z - Complex.exp (4 * (Real.pi : ℂ) ^ 2 * v / z)‖ ≤
      Real.exp (v * (4 * Real.pi ^ 2 * z.re / Complex.normSq z)) *
        remainderR σ v (4 * Real.pi ^ 2 * z.re / Complex.normSq z) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  set w : ℂ := 4 * (Real.pi : ℂ) ^ 2 / z with hw
  have hre : w.re = 4 * Real.pi ^ 2 * z.re / Complex.normSq z := re_four_pi_sq_div z
  have hwpos : 0 < w.re := by
    rw [hre]
    have : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
    positivity
  have hint := H.hint w.re hwpos
  have h1 := laplaceC_eq_atom_add σ H.vacuum_gap.1 H.vacuum_gap.2.1 hwpos hint
  have h2 : Complex.exp (w * v) = Complex.exp (4 * (Real.pi : ℂ) ^ 2 * v / z) := by
    rw [hw]; congr 1; ring
  have h3 : laplaceC σ z - Complex.exp (4 * (Real.pi : ℂ) ^ 2 * v / z) =
      ∫ x in Ioi (-v), Complex.exp (-(w * x)) ∂σ := by
    rw [hmodC z hz, h1, h2]; ring
  rw [h3]
  have := norm_Ioi_le σ v hint
  rw [hre] at this
  exact this

namespace SpectralHyp

variable {σ : Measure ℝ} {v g C β₀ : ℝ}

/-- **The remainder is exponentially smaller than the vacuum term.** For `0 ≤ Λ` and `β₁ > 0` with
`q = (β₁² + Λ²)/(4π²) < 1` there are `θ < 1` and `K ≥ 0` such that, with `β' = 4π² β/(β² + t²)`,
`e^{v β'} R(β') ≤ K e^{θ a/β}` for `0 < β ≤ β₁` and `|t| ≤ Λ` (`a = 4π² v`). -/
lemma psi_bound (H : SpectralHyp σ v g C β₀) {Λ β₁ : ℝ} (hΛ : 0 ≤ Λ)
    (hq : (β₁ ^ 2 + Λ ^ 2) / (4 * Real.pi ^ 2) < 1) (hβ₁ : 0 < β₁) :
    ∃ θ K : ℝ, θ < 1 ∧ 0 ≤ K ∧ ∀ β t : ℝ, 0 < β → β ≤ β₁ → |t| ≤ Λ →
      Real.exp (v * (4 * Real.pi ^ 2 * β / (β ^ 2 + t ^ 2))) *
        remainderR σ v (4 * Real.pi ^ 2 * β / (β ^ 2 + t ^ 2)) ≤
        K * Real.exp (θ * (4 * Real.pi ^ 2 * v) / β) := by
  have hv := H.hv
  have hg := H.hg
  have hC := H.C_nonneg
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  set a : ℝ := 4 * Real.pi ^ 2 * v with ha
  have ha0 : 0 < a := by positivity
  set q : ℝ := (β₁ ^ 2 + Λ ^ 2) / (4 * Real.pi ^ 2) with hqdef
  have hq0 : 0 ≤ q := by positivity
  set θ : ℝ := max (1 - g / a) q with hθ
  have hθ1 : θ < 1 := max_lt (by have : 0 < g / a := by positivity
                                 linarith) hq
  have hθ0 : 0 ≤ θ := le_trans hq0 (le_max_right _ _)
  set B : ℝ := 4 * Real.pi ^ 2 / β₀ + 1 with hB
  set C1 : ℝ := (1 + C) * Real.exp (2 * a / β₀) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨θ, C + C1 * Real.exp (v * B), hθ1, by positivity, fun β t hβ hββ₁ ht => ?_⟩
  have hden : 0 < β ^ 2 + t ^ 2 := by positivity
  set β' : ℝ := 4 * Real.pi ^ 2 * β / (β ^ 2 + t ^ 2) with hβ'
  have hβ'pos : 0 < β' := by positivity
  have hβ'le : β' ≤ 4 * Real.pi ^ 2 / β := by
    rw [hβ', div_le_div_iff₀ hden hβ]
    nlinarith [sq_nonneg t, mul_pos hπ hβ]
  have hexpa : Real.exp (θ * a / β) = Real.exp (θ * (a / β)) := by rw [mul_div_assoc]
  by_cases hbig : B ≤ β'
  · -- low temperature: `R ≤ C e^{-g'' β'}`
    have h1 := H.remainder_le_large hbig
    have h2 : Real.exp (v * β') * remainderR σ v β' ≤ C * Real.exp ((v - g / (4 * Real.pi ^ 2)) * β') := by
      calc Real.exp (v * β') * remainderR σ v β' ≤ Real.exp (v * β') * (C * Real.exp (-(g / (4 * Real.pi ^ 2) * β'))) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = C * Real.exp ((v - g / (4 * Real.pi ^ 2)) * β') := by
            rw [← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]; congr 2; ring
    have h3 : (v - g / (4 * Real.pi ^ 2)) * β' ≤ θ * a / β := by
      by_cases hs : 0 ≤ v - g / (4 * Real.pi ^ 2)
      · have h4 : (v - g / (4 * Real.pi ^ 2)) * β' ≤ (v - g / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2 / β) :=
          mul_le_mul_of_nonneg_left hβ'le hs
        refine h4.trans ?_
        have h5 : (v - g / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2 / β) = (1 - g / a) * a / β := by
          rw [ha]; field_simp
        rw [h5]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ha0.le) hβ.le
      · push Not at hs
        have : (v - g / (4 * Real.pi ^ 2)) * β' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hβ'pos.le
        exact this.trans (by positivity)
    calc Real.exp (v * β') * remainderR σ v β' ≤ C * Real.exp ((v - g / (4 * Real.pi ^ 2)) * β') := h2
      _ ≤ C * Real.exp (θ * a / β) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC
      _ ≤ (C + C1 * Real.exp (v * B)) * Real.exp (θ * a / β) := by
          have : 0 ≤ C1 * Real.exp (v * B) := by positivity
          nlinarith [Real.exp_pos (θ * a / β)]
  · push Not at hbig
    have h1 := H.remainder_le_exp hβ'pos
    have h2 : Real.exp (v * β') ≤ Real.exp (v * B) := Real.exp_le_exp.2 (by nlinarith)
    have h3 : a / β' ≤ θ * a / β := by
      have e : a / β' = v * (β ^ 2 + t ^ 2) / β := by rw [hβ', ha]; field_simp
      rw [e]
      have h4 : v * (β ^ 2 + t ^ 2) / β ≤ v * (β₁ ^ 2 + Λ ^ 2) / β := by
        refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hv.le) hβ.le
        have : t ^ 2 ≤ Λ ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
        have : β ^ 2 ≤ β₁ ^ 2 := by nlinarith
        linarith
      refine h4.trans ?_
      have e2 : v * (β₁ ^ 2 + Λ ^ 2) / β = q * a / β := by rw [hqdef, ha]; field_simp
      rw [e2]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ha0.le) hβ.le
    calc Real.exp (v * β') * remainderR σ v β'
        ≤ Real.exp (v * B) * (C1 * Real.exp (a / β')) := by
          refine mul_le_mul h2 ?_ (remainderR_nonneg σ v β') (Real.exp_pos _).le
          have e : C1 * Real.exp (a / β') =
              (1 + C) * Real.exp (2 * (4 * Real.pi ^ 2 * v) / β₀) * Real.exp (4 * Real.pi ^ 2 * v / β') := by
            rw [hC1, ha]
          rw [e]; exact h1
      _ ≤ Real.exp (v * B) * (C1 * Real.exp (θ * a / β)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC10
      _ ≤ (C + C1 * Real.exp (v * B)) * Real.exp (θ * a / β) := by
          have : 0 ≤ C * Real.exp (θ * a / β) := by positivity
          nlinarith [mul_comm (Real.exp (v * B)) (C1 * Real.exp (θ * a / β))]

end SpectralHyp

end Lightlike.Tauberian
