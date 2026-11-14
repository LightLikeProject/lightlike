import Lightlike.Asymptotics.UniformValley
import Lightlike.Asymptotics.Tests
import Lightlike.Asymptotics.ContourTests
import Lightlike.Asymptotics.ValleyTests

/-!
# Trust checks for the valleys with explicit constants

* **Known value.** For the regular unit tetrahedron, `‖ψ''(s)‖ = 8√2`, so `‖b‖ = 4√2`
  (`norm_saddleCoeff_regular`), and `Im s = √2/6`. The radius of `valley_bounds` is then
  `min (√2/18) (4√2 · (1/18)/256) = √2/1152` (`valleyRadius_regular`).
* **Wrong input fails.** The vertical direction `v = i` is no valley direction: for every `t > 0`,
  `Re ψ(s + t i) > Re ψ(s)`, so the descent bound of `valley_bounds` fails along it
  (`IsEuclid.vertical_not_valley`).
* **Non-vacuity.** For the regular tetrahedron the uniform valley bounds of
  `IsEuclid.eventually_valley_bounds` hold at `m = l` with a positive radius `r`, and at `t = r`
  the phase has strictly dropped below its saddle value (`valley_bounds_regular`).
* **Junk values.** For `β = 0` the radius degenerates, `valleyRadius y 0 = 0`
  (`valleyRadius_zero`), so `valley_bounds` with `β = 0` covers only `t = 0`. The uniform version
  takes `β = ‖b_l‖/2 > 0` from `IsEuclid.saddleCoeff_ne_zero`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `‖b‖ = 4√2` for the regular tetrahedron. -/
theorem norm_saddleCoeff_regular : ‖saddleCoeff (fun _ => 1)‖ = 4 * √2 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [saddleCoeff, norm_div, norm_d2phaseC_saddle_regular, h2]
  ring

/-- **Known value**: the valley radius of the regular tetrahedron is `√2/1152`. -/
theorem valleyRadius_regular :
    valleyRadius (saddle (fun _ => 1)).im ‖saddleCoeff (fun _ => 1)‖ = √2 / 1152 := by
  rw [norm_saddleCoeff_regular, saddle_regular]
  show min (√2 / 6 / 3) (4 * √2 * (√2 / 6) ^ 2 / 256) = √2 / 1152
  have h2 : (√2 / 6) ^ 2 = 1 / 18 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs : 0 < √2 := by positivity
  rw [h2, min_eq_right (by linarith)]
  ring

/-- **Wrong input**: the vertical direction is no valley direction. For `t > 0`,
`Re ψ(s + t i) > Re ψ(s)`, so the descent bound `Re ψ(s + t v) ≤ Re ψ(s) − ‖b‖ t²/4` fails for
`v = i`. -/
theorem IsEuclid.vertical_not_valley {l : Fin 6 → ℝ} (h : IsEuclid l) {t : ℝ} (ht : 0 < t) :
    (phaseC (faceSum l) (quadSum l) (saddle l)).re <
        (phaseC (faceSum l) (quadSum l) (saddle l + t * I)).re ∧
      ¬ (phaseC (faceSum l) (quadSum l) (saddle l + t * I)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖saddleCoeff l‖ / 4 * t ^ 2 := by
  have hz : 0 < (saddle l + t * I).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    linarith [h.saddle_im_pos]
  have hre : (saddle l + t * I).re = (saddle l).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]; ring
  have hne : saddle l + t * I ≠ saddle l := by
    intro he
    have := congrArg Complex.im he
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im] at this
    linarith
  have hlt := h.re_phaseC_saddle_lt_of_re_eq hz hre hne
  refine ⟨hlt, fun hle => ?_⟩
  nlinarith [norm_nonneg (saddleCoeff l), sq_nonneg t]

/-- **Non-vacuity**: for the regular tetrahedron the uniform valley bounds hold at `m = l` with a
radius `r > 0`, and at the end of the ray along `saddleDir` the real part of the phase lies strictly
below its saddle value. -/
theorem valley_bounds_regular : ∃ r β : ℝ, 0 < r ∧ 0 < β ∧
    β ≤ ‖saddleCoeff (fun _ => 1)‖ ∧
    (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
        (saddle (fun _ => 1) + r * valleyDir (saddleDir (fun _ => 1)) 1 0)).re <
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re := by
  obtain ⟨r, K, β, hr, hβ, hev⟩ := isEuclid_regular.eventually_valley_bounds
  obtain ⟨-, hb, hv⟩ := hev.self_of_nhds
  have hle := (hv 1 (by norm_num) 0 (by norm_num) r ⟨hr.le, le_rfl⟩).2.2
  refine ⟨r, β, hr, hβ, hb, ?_⟩
  have : 0 < ‖saddleCoeff (fun _ => (1 : ℝ))‖ / 4 * r ^ 2 := by
    have := hβ.trans_le hb
    positivity
  linarith

/-- **Junk value**: for `β = 0` the valley radius is `0`. -/
theorem valleyRadius_zero {y : ℝ} (hy : 0 ≤ y) : valleyRadius y 0 = 0 := by
  unfold valleyRadius
  rw [zero_mul, zero_div]
  exact min_eq_right (by positivity)

end Lightlike.Asymptotics
