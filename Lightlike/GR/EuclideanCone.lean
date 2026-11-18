import Mathlib

/-!
# The conical angle at the Euclidean Schwarzschild horizon

Near `r = 2M` put `r = 2M + σ²`. The Euclidean Schwarzschild metric with `τ` of period `β` has, at
the circle of coordinate radius `σ`, circumference `β σ / √(2M + σ²)` (`coneCirc`) and proper radial
distance `∫₀^σ 2 √(2M + s²) ds` from the horizon (`coneRadius`). The ratio circumference / radius tends
to `β/(4M)` as `σ → 0` (`tendsto_cone_ratio`). A smooth tip needs the ratio `2π` of the Euclidean
plane, so a period other than `8πM` leaves a conical singularity (`cone_ratio_eq_two_pi_iff`), and the
inverse of the smooth period is the Hawking temperature `1/(8πM)` (`hawkingTemperature`).

Gap row G1-058, follow-ups (a) and (b). Comparison with Gibbons–Hawking (1977) pending.
-/

open Real Filter Topology intervalIntegral Set

noncomputable section

namespace Lightlike

variable (M β : ℝ)

/-- The circumference of the `τ`-circle at `r = 2M + σ²`: `β σ / √(2M + σ²)`. -/
def coneCirc (σ : ℝ) : ℝ := β * σ / √(2 * M + σ ^ 2)

/-- The proper radial distance from `r = 2M` to `r = 2M + σ²`: `∫₀^σ 2 √(2M + s²) ds`. -/
def coneRadius (σ : ℝ) : ℝ := ∫ s in (0 : ℝ)..σ, 2 * √(2 * M + s ^ 2)

/-- **The cone ratio.** Circumference over proper radius tends to `β/(4M)` at the tip. -/
theorem tendsto_cone_ratio (hM : 0 < M) :
    Tendsto (fun σ => coneCirc M β σ / coneRadius M σ) (𝓝[≠] 0) (𝓝 (β / (4 * M))) := by
  have hq : 0 < √(2 * M) := Real.sqrt_pos.2 (by linarith)
  have hqq : √(2 * M) * √(2 * M) = 2 * M := Real.mul_self_sqrt (by linarith)
  have hcont : Continuous fun s : ℝ => 2 * √(2 * M + s ^ 2) := by fun_prop
  have hD : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, 2 * √(2 * M + s ^ 2))
      (2 * √(2 * M + 0 ^ 2)) 0 := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hD' : Tendsto (fun σ => coneRadius M σ / σ) (𝓝[≠] 0) (𝓝 (2 * √(2 * M))) := by
    have h := hD.tendsto_slope_zero
    rw [show 2 * √(2 * M + 0 ^ 2) = 2 * √(2 * M) by rw [zero_pow two_ne_zero, add_zero]] at h
    refine h.congr' ?_
    filter_upwards with t
    simp [coneRadius, div_eq_inv_mul]
  have hN : Tendsto (fun σ => coneCirc M β σ / σ) (𝓝[≠] 0) (𝓝 (β / √(2 * M))) := by
    have hc : ContinuousAt (fun σ : ℝ => β / √(2 * M + σ ^ 2)) 0 :=
      (continuousAt_const.div (by fun_prop) (by rw [zero_pow two_ne_zero, add_zero]; exact hq.ne'))
    have h1 : Tendsto (fun σ : ℝ => β / √(2 * M + σ ^ 2)) (𝓝[≠] 0) (𝓝 (β / √(2 * M))) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : σ ≠ 0 := hσ
    unfold coneCirc
    field_simp
  have := hN.div hD' (by positivity)
  refine (this.congr' ?_).trans_eq ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have : σ ≠ 0 := hσ
    simp only [Pi.div_apply]
    field_simp
  · rw [div_div, show √(2 * M) * (2 * √(2 * M)) = 4 * M by nlinarith [hqq]]

/-- **A smooth tip forces the period `8πM`.** The limiting ratio is `2π` iff `β = 8πM`; for any other
period the horizon is a conical singularity. -/
theorem cone_ratio_eq_two_pi_iff (hM : 0 < M) : β / (4 * M) = 2 * π ↔ β = 8 * π * M := by
  constructor <;> intro h <;> field_simp at * <;> linarith

/-- The Hawking temperature `1/β` at the smooth period `β = 8πM`. -/
def hawkingTemperature : ℝ := 1 / (8 * π * M)

/-- **Hawking temperature.** If the period of `τ` makes the tip smooth, the temperature `1/β` is
`1/(8πM)`. -/
theorem temperature_of_smooth_tip (hM : 0 < M) (h : β / (4 * M) = 2 * π) :
    1 / β = hawkingTemperature M := by
  rw [(cone_ratio_eq_two_pi_iff M β hM).1 h]; rfl

end Lightlike
