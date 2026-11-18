import Lightlike.Asymptotics.Tauberian.BoxConv
import Lightlike.Asymptotics.Tauberian.FourierExchange
import Lightlike.Asymptotics.Tauberian.Majorant

/-!
# The window bound through the Fourier representation (MZ (4.1)–(4.4))

For a positive measure `σ` and the kernel `g ≥ 0` with `ĝ(x) = (2 b sinc(b x))⁴` supported in
`|t| ≤ 4 b`:

* `window_le`: `σ [Δ - δ, Δ + δ] ≤ e^{β (Δ + δ)} ∫ φ₊(x) e^{-β x} dσ(x)` with
  `φ₊ x = sinc(b (x - Δ))⁴ / sinc(b δ)⁴`;
* `fourier_representation`: `16 b⁴ ∫ sinc(b (x - Δ))⁴ e^{-β x} dσ = ∫ g(t) e^{i t Δ} L(β + i t) dt`.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

variable (σ : Measure ℝ)

/-- **The window bound** (MZ (4.4), upper side). -/
theorem window_le [IsFiniteMeasureOnCompacts σ] {β b δ Δ : ℝ} (hβ : 0 < β) (hb : 0 < b) (hδ : 0 < δ)
    (hbδ : b * δ < Real.pi) (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) σ) :
    (σ (Icc (Δ - δ) (Δ + δ))).toReal ≤
      Real.exp (β * (Δ + δ)) * ∫ x, majorant (b * δ) (b * (x - Δ)) * Real.exp (-β * x) ∂σ := by
  have hHc : Continuous fun x : ℝ => majorant (b * δ) (b * (x - Δ)) := by
    unfold majorant; fun_prop
  have hsp : 0 < Real.sinc (b * δ) := Real.sinc_pos (by rw [abs_of_pos (by positivity)]; exact hbδ)
  have hbdd : ∀ x : ℝ, ‖majorant (b * δ) (b * (x - Δ))‖ ≤ 1 / Real.sinc (b * δ) ^ 4 := by
    intro x
    unfold majorant
    rw [Real.norm_of_nonneg (by positivity)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := Real.abs_sinc_le_one (b * (x - Δ))
    calc Real.sinc (b * (x - Δ)) ^ 4 = |Real.sinc (b * (x - Δ))| ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) this
  have hI : Integrable (fun x : ℝ => majorant (b * δ) (b * (x - Δ)) * Real.exp (-β * x)) σ := by
    have := hint.bdd_mul hHc.aestronglyMeasurable (c := 1 / Real.sinc (b * δ) ^ 4)
      (Filter.Eventually.of_forall hbdd)
    exact this.congr (Filter.Eventually.of_forall fun x => by ring)
  rw [← integral_const_mul]
  have hind : (σ (Icc (Δ - δ) (Δ + δ))).toReal =
      ∫ x, (Icc (Δ - δ) (Δ + δ)).indicator (fun _ => (1 : ℝ)) x ∂σ := by
    rw [integral_indicator_const _ measurableSet_Icc]
    simp [Measure.real]
  rw [hind]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hI.const_mul _)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  · by_cases hx : x ∈ Icc (Δ - δ) (Δ + δ)
    · rw [Set.indicator_of_mem hx]
      have h1 : 1 ≤ majorant (b * δ) (b * (x - Δ)) := by
        refine one_le_majorant (by positivity) hbδ ?_
        rw [abs_le]
        constructor <;> nlinarith [hx.1, hx.2]
      have h2 : 1 ≤ Real.exp (β * (Δ + δ)) * Real.exp (-β * x) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [hx.2])
      calc (1 : ℝ) ≤ 1 * 1 := by norm_num
        _ ≤ majorant (b * δ) (b * (x - Δ)) * (Real.exp (β * (Δ + δ)) * Real.exp (-β * x)) :=
            mul_le_mul h1 h2 zero_le_one (by linarith)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (majorant_nonneg _ _) (Real.exp_pos _).le)

/-- **The Fourier representation** (MZ (4.4)): `16 b⁴ ∫ sinc(b (x - Δ))⁴ e^{-β x} dσ(x)` equals
`∫ g(t) e^{i t Δ} L(β + i t) dt`. -/
theorem fourier_representation [SFinite σ] (hσ : σ (Iio 0) = 0) {β b Δ : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) σ) {g : ℝ → ℝ} (hgi : Integrable g)
    (hg : ∀ x : ℝ, ∫ t, (g t : ℂ) * char x t = (((2 * b * Real.sinc (b * x)) ^ 4 : ℝ) : ℂ)) :
    ((∫ x, (2 * b * Real.sinc (b * (x - Δ))) ^ 4 * Real.exp (-β * x) ∂σ : ℝ) : ℂ) =
      ∫ t, (g t : ℂ) * Complex.exp (t * Δ * Complex.I) * laplaceC σ (β + t * Complex.I) := by
  have hgt : Integrable (fun t : ℝ => (g t : ℂ) * Complex.exp (t * Δ * Complex.I)) := by
    refine hgi.ofReal.mul_bdd (by fun_prop : Continuous fun t : ℝ => Complex.exp (t * Δ * Complex.I)).aestronglyMeasurable
      (c := 1) (Filter.Eventually.of_forall fun t => ?_)
    rw [Complex.norm_exp]; simp
  have h := integral_fourier_mul_exp σ hσ hβ hint hgt
  rw [← integral_complex_ofReal]
  have e1 : ∀ x : ℝ, (∫ t, ((g t : ℂ) * Complex.exp (t * Δ * Complex.I)) *
      Complex.exp (-(t * x * Complex.I))) = (((2 * b * Real.sinc (b * (x - Δ))) ^ 4 : ℝ) : ℂ) := by
    intro x
    rw [← hg (x - Δ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [char]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [e1] at h
  have e2 : ∀ x : ℝ, ((((2 * b * Real.sinc (b * (x - Δ))) ^ 4 * Real.exp (-β * x) : ℝ)) : ℂ) =
      (((2 * b * Real.sinc (b * (x - Δ))) ^ 4 : ℝ) : ℂ) * (Real.exp (-β * x) : ℂ) := fun x => by push_cast; ring
  simp_rw [e2]
  rw [h]

end Lightlike.Tauberian
