import Lightlike.GR.HawkingRadiation.Wronskian
import Lightlike.GR.EuclideanCone

/-!
# Thermality of the collapse state at `T = κ/2π` (SC4, part 3)

Row G1-068 (milestone SC4).  In the 1+1 collapse model `u = -(1/κ) log(-v/C)` the Bogoliubov
kernels between the late-time outgoing modes and the in-modes are Mellin transforms, whose closed
forms are `α = c Γ(is)(iw)^{-is}`, `β = c Γ(is)(-iw)^{-is}` with `s = ω/κ` (`kernelPlus`,
`kernelMinus`).  With the normalisation `‖c‖² = s/(2π)` forced by `|α|² - |β|² = 1`, the mean
occupation `|β|²` is the Planck law at temperature `T = κ/(2π)`.  For Schwarzschild
`κ = 1/(4M)` and `T = 1/(8πM) = hawkingTemperature M`.

Compared with Hollands–Wald 2015 §2.2 and Carlip 2014 §3.2 only in outline (not read
equation by equation).  Not covered: the Boulware-state check and the full QFT on the collapse
spacetime (SC2, SC6).

## Main statements

* `hawking_collapse_thermal`: `|α|² - |β|² = 1` and `|β|² = 1/(exp(ω/T) - 1)` with `T = κ/(2π)`.
* `schwarzschild_surfaceGravity_temperature`: `κ = 1/(4M)` gives `T = hawkingTemperature M`.
* `hawking_schwarzschild_thermal`: the combination, `|β|² = 1/(exp(ω/T_H) - 1)`.
-/

namespace Lightlike.Rows.G1_068

noncomputable section

/-- **Thermal late-time state of the collapse model.**  For surface gravity `κ > 0`, frequency
`ω > 0` and `T = κ/(2π)`, the normalised collapse Bogoliubov kernels satisfy
`|α|² - |β|² = 1` and the occupation `|β|²` equals the Planck law `1/(exp(ω/T) - 1)`. -/
theorem hawking_collapse_thermal {κ ω w : ℝ} (hκ : 0 < κ) (hω : 0 < ω) (hw : 0 < w) (c : ℂ)
    (hc : ‖c‖ ^ 2 = (ω / κ) / (2 * Real.pi)) :
    ‖c * kernelPlus (ω / κ) w‖ ^ 2 - ‖c * kernelMinus (ω / κ) w‖ ^ 2 = 1 ∧
    ‖c * kernelMinus (ω / κ) w‖ ^ 2 = 1 / (Real.exp (ω / (κ / (2 * Real.pi))) - 1) := by
  have hs : 0 < ω / κ := div_pos hω hκ
  obtain ⟨h1, h2⟩ := normalized_kernels_planck hs hw c hc
  refine ⟨h1, ?_⟩
  rw [h2]
  have hpi := Real.pi_pos
  have : ω / (κ / (2 * Real.pi)) = 2 * Real.pi * (ω / κ) := by
    field_simp
  rw [this]

/-- For Schwarzschild, surface gravity `κ = 1/(4M)` gives `κ/(2π) = 1/(8πM)`. -/
theorem schwarzschild_surfaceGravity_temperature {M : ℝ} (hM : 0 < M) :
    (1 / (4 * M)) / (2 * Real.pi) = Lightlike.hawkingTemperature M := by
  have hpi := Real.pi_pos
  unfold Lightlike.hawkingTemperature
  field_simp
  ring

/-- **Hawking radiation from collapse, Schwarzschild case.**  With `κ = 1/(4M)` the occupation is
the Planck law at the Hawking temperature `1/(8πM)`. -/
theorem hawking_schwarzschild_thermal {M ω w : ℝ} (hM : 0 < M) (hω : 0 < ω) (hw : 0 < w) (c : ℂ)
    (hc : ‖c‖ ^ 2 = (ω / (1 / (4 * M))) / (2 * Real.pi)) :
    ‖c * kernelPlus (ω / (1 / (4 * M))) w‖ ^ 2 - ‖c * kernelMinus (ω / (1 / (4 * M))) w‖ ^ 2 = 1 ∧
    ‖c * kernelMinus (ω / (1 / (4 * M))) w‖ ^ 2 =
      1 / (Real.exp (ω / Lightlike.hawkingTemperature M) - 1) := by
  have hκ : 0 < 1 / (4 * M) := by positivity
  have := hawking_collapse_thermal hκ hω hw c hc
  rwa [schwarzschild_surfaceGravity_temperature hM] at this

end

end Lightlike.Rows.G1_068
