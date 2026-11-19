import Lightlike.Asymptotics.Tauberian.CardyRelative

/-!
# A spectrum satisfying MZ's hypotheses (non-vacuity of `cardy_counting`)

`σ = δ_{-v} + ρ₀` with `a = 4π² v`: its Laplace transform is `e^{v z} + e^{a/z}`, invariant under
`z ↦ 4π²/z`, with the vacuum at `-v` and the next state at `0` (gap `v`); it satisfies `SpectralHyp`
with `g = a/2`, `C = e^v`, `β₀ = 1` (`exampleSpectrum_hyp`), so `cardy_mz` applies to it.
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- The example spectrum `δ_{-v} + ρ₀` with `a = 4π² v`. -/
def exampleSpectrum (v : ℝ) : Measure ℝ := Measure.dirac (-v) + rho0 (4 * π ^ 2 * v)

instance (v : ℝ) : SFinite (exampleSpectrum v) := by unfold exampleSpectrum; infer_instance

/-- The real Laplace transform of the example: `e^{vβ} + e^{a/β}`. -/
lemma exampleSpectrum_laplace {v β : ℝ} (hv : 0 < v) (hβ : 0 < β) :
    Integrable (fun x : ℝ => Real.exp (-β * x)) (exampleSpectrum v) ∧
      ∫ x, Real.exp (-β * x) ∂(exampleSpectrum v) = Real.exp (v * β) + Real.exp (4 * π ^ 2 * v / β) := by
  have ha : 0 < 4 * π ^ 2 * v := by positivity
  have hd : Integrable (fun x : ℝ => Real.exp (-β * x)) (Measure.dirac (-v)) :=
    integrable_dirac' (by fun_prop : Continuous fun x : ℝ => Real.exp (-β * x)).stronglyMeasurable (by simp)
  obtain ⟨hr, hr'⟩ := integral_exp_rho0 ha hβ
  refine ⟨hd.add_measure hr, ?_⟩
  unfold exampleSpectrum
  rw [integral_add_measure hd hr, integral_dirac, hr']
  congr 1; congr 1; ring

/-- The complex Laplace transform of the example: `e^{v z} + e^{a/z}`. -/
lemma exampleSpectrum_laplaceC {v : ℝ} (hv : 0 < v) {z : ℂ} (hz : 0 < z.re) :
    laplaceC (exampleSpectrum v) z = Complex.exp (v * z) + Complex.exp (((4 * π ^ 2 * v : ℝ) : ℂ) / z) := by
  have ha : 0 < 4 * π ^ 2 * v := by positivity
  have hd : Integrable (fun x : ℝ => Complex.exp (-(z * x))) (Measure.dirac (-v)) :=
    integrable_dirac' (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(z * x))).stronglyMeasurable (by simp)
  have hr : Integrable (fun x : ℝ => Complex.exp (-(z * x))) (rho0 (4 * π ^ 2 * v)) := by
    unfold rho0
    exact (integrable_cexp_dirac z).add_measure (integrable_cexp_density ha hz)
  have h2 := laplaceC_rho0 ha hz
  unfold laplaceC at h2 ⊢
  unfold exampleSpectrum
  rw [integral_add_measure hd hr, integral_dirac, h2]
  congr 2; push_cast; ring

/-- **The example satisfies MZ's hypotheses.** -/
theorem exampleSpectrum_hyp {v : ℝ} (hv : 0 < v) :
    SpectralHyp (exampleSpectrum v) v (4 * π ^ 2 * v / 2) (Real.exp v) 1 := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨hv, by positivity, one_pos, fun β hβ => (exampleSpectrum_laplace hv hβ).1, fun β hβ => ?_, fun β hβ hβ1 => ?_⟩
  · have h4 : 0 < 4 * π ^ 2 / β := by positivity
    rw [(exampleSpectrum_laplace hv hβ).2, (exampleSpectrum_laplace hv h4).2]
    have e1 : v * (4 * π ^ 2 / β) = 4 * π ^ 2 * v / β := by ring
    have e2 : 4 * π ^ 2 * v / (4 * π ^ 2 / β) = v * β := by field_simp
    rw [e1, e2]; ring
  · rw [(exampleSpectrum_laplace hv hβ).2]
    rw [show Real.exp (v * β) + Real.exp (4 * π ^ 2 * v / β) - Real.exp (4 * π ^ 2 * v / β) = Real.exp (v * β) by ring,
      abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (v * β) ≤ Real.exp v := Real.exp_le_exp.2 (by nlinarith)
    have h2 : 1 ≤ Real.exp ((4 * π ^ 2 * v - 4 * π ^ 2 * v / 2) / β) :=
      Real.one_le_exp (by
        have : 0 ≤ 4 * π ^ 2 * v - 4 * π ^ 2 * v / 2 := by nlinarith [sq_nonneg π]
        positivity)
    nlinarith [Real.exp_pos v]

/-- The example is invariant under `z ↦ 4π²/z` on `Re z > 0`. -/
theorem exampleSpectrum_modC {v : ℝ} (hv : 0 < v) :
    ∀ z : ℂ, 0 < z.re → laplaceC (exampleSpectrum v) z =
      laplaceC (exampleSpectrum v) (4 * (Real.pi : ℂ) ^ 2 / z) := by
  intro z hz
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hre : 0 < (4 * (Real.pi : ℂ) ^ 2 / z).re := by
    rw [re_four_pi_sq_div]
    have : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
    have := Real.pi_pos
    positivity
  rw [exampleSpectrum_laplaceC hv hz, exampleSpectrum_laplaceC hv hre]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have e1 : (v : ℂ) * (4 * (Real.pi : ℂ) ^ 2 / z) = ((4 * π ^ 2 * v : ℝ) : ℂ) / z := by push_cast; ring
  have e2 : ((4 * π ^ 2 * v : ℝ) : ℂ) / (4 * (Real.pi : ℂ) ^ 2 / z) = v * z := by
    push_cast; field_simp
  rw [e1, e2]; ring

/-- **Trust check**: the counting function of the example is exactly `1 + I₀(2√(a x))` for `x ≥ 0`
(the vacuum plus the crossing measure), the main term of `cardy_counting`. -/
theorem exampleSpectrum_real_Iic {v x : ℝ} (hv : 0 < v) (hx : 0 ≤ x) :
    (exampleSpectrum v).real (Iic x) =
      1 + (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (2 * √(4 * π ^ 2 * v * x) * Real.cos θ) := by
  have ha : 0 < 4 * π ^ 2 * v := by positivity
  have hfin : (rho0 (4 * π ^ 2 * v)) (Iic x) ≠ ⊤ := by
    have hi := (integral_exp_rho0 ha one_pos).1
    refine ne_top_of_le_ne_top (hi.measure_norm_ge_lt_top (Real.exp_pos (-1 * x))).ne (measure_mono ?_)
    intro y hy
    have hy' : y ≤ x := hy
    show Real.exp (-1 * x) ≤ ‖Real.exp (-1 * y)‖
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by linarith)
  unfold exampleSpectrum
  rw [measureReal_add_apply (measure_ne_top (Measure.dirac (-v)) _) hfin, rho0_real_Iic ha hx]
  have : (Measure.dirac (-v)).real (Iic x) = 1 := by
    rw [Measure.real, Measure.dirac_apply' _ measurableSet_Iic,
      Set.indicator_of_mem (by simp only [mem_Iic]; linarith : -v ∈ Iic x)]
    simp
  rw [this]

/-- **Non-vacuity**: `cardy_mz` applies to the example spectrum. -/
example {v : ℝ} (hv : 0 < v) :
    ∃ K Δ₁ : ℝ, 0 ≤ K ∧ ∀ Δ : ℝ, Δ₁ ≤ Δ →
      |(exampleSpectrum v).real (Iic (Δ - v)) *
          (√(4 * π * √(4 * π ^ 2 * v * Δ)) * Real.exp (-(2 * √(4 * π ^ 2 * v * Δ)))) - 1| ≤
        K * Δ ^ (-(1 / 2 : ℝ)) :=
  cardy_mz (exampleSpectrum_hyp hv) (exampleSpectrum_modC hv)

end Lightlike.Tauberian
