import Mathlib
import Lightlike.Regge.CMS.Hyperbolic

/-!
# Distances along the `x`-lines of the hyperbolic plane `dx² + e^{2x} dy²`

The lines `y = const` are geodesics of `hypMetric`. This file proves that the chart distance
(`Geodesic.dist`) between `(a, y)` and `(b, y)` is exactly `|b - a|`: the straight segment has this
length, and every admissible curve has at least this length because
`g(v, v) = v₀² + e^{2x} v₁² ≥ v₀²`.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic
open scoped ContDiff

namespace Lightlike.CMS

noncomputable section

/-- `g(v, v) = v₀² + e^{2x} v₁²` for the hyperbolic metric. -/
lemma normSq_hyp (p v : Fin 2 → ℝ) :
    normSq hypMetric p v = v 0 ^ 2 + exp (2 * p 0) * v 1 ^ 2 := by
  simp [normSq, hypMetric, hypD, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two, sq]
  ring

/-- The straight segment from `(a, y)` to `(b, y)`, parametrised on `[0, 1]`. -/
def xSegment (a b y : ℝ) (t : ℝ) : Fin 2 → ℝ := ![a + t * (b - a), y]

lemma xSegment_hasDerivAt (a b y t : ℝ) :
    HasDerivAt (xSegment a b y) ![b - a, 0] t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [xSegment] using ((hasDerivAt_id t).mul_const (b - a)).const_add a
  · simpa [xSegment] using hasDerivAt_const t y

lemma xSegment_admissible (a b y : ℝ) :
    IsAdmissible Set.univ (xSegment a b y) ![a, y] ![b, y] where
  smooth := by
    unfold xSegment
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  mem := fun _ _ => mem_univ _
  start := by simp [xSegment]
  finish := by ext i; fin_cases i <;> simp [xSegment]

/-- The segment has length `|b - a|`. -/
lemma length_xSegment (a b y : ℝ) : length hypMetric (xSegment a b y) 0 1 = |b - a| := by
  unfold length
  have : ∀ t, √(normSq hypMetric (xSegment a b y t) (deriv (xSegment a b y) t)) = |b - a| := by
    intro t
    rw [(xSegment_hasDerivAt a b y t).deriv, normSq_hyp]
    simp [Real.sqrt_sq_eq_abs]
  simp [this]

/-- Every admissible curve is at least as long as the horizontal displacement. -/
lemma abs_sub_le_length {c : ℝ → Fin 2 → ℝ} {p q : Fin 2 → ℝ}
    (hc : IsAdmissible Set.univ c p q) : |q 0 - p 0| ≤ length hypMetric c 0 1 := by
  have hd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.smooth.differentiable one_ne_zero) t).hasDerivAt
  have hd0 : ∀ t, HasDerivAt (fun s => c s 0) (deriv c t 0) t := fun t =>
    (hasDerivAt_pi.mp (hd t)) 0
  have hcont : Continuous fun t => deriv c t 0 :=
    (continuous_apply 0).comp (hc.smooth.continuous_deriv le_rfl)
  have hftc : ∫ t in (0:ℝ)..1, deriv c t 0 = c 1 0 - c 0 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd0 t)
      (hcont.intervalIntegrable 0 1)
  have hsp : IntervalIntegrable (fun t => √(normSq hypMetric (c t) (deriv c t))) volume 0 1 :=
    isRiemMetric_hyp.intervalIntegrable_speed hc
  calc |q 0 - p 0| = |∫ t in (0:ℝ)..1, deriv c t 0| := by rw [hftc, hc.start, hc.finish]
    _ ≤ ∫ t in (0:ℝ)..1, |deriv c t 0| := by
        exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ length hypMetric c 0 1 := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (hcont.abs.intervalIntegrable 0 1) hsp fun t _ => ?_
        rw [normSq_hyp]
        exact Real.abs_le_sqrt (by
          nlinarith [mul_nonneg (exp_pos (2 * c t 0)).le (sq_nonneg (deriv c t 1))])

/-- **Distance along an `x`-line.** The chart distance of the hyperbolic plane between `(a, y)`
and `(b, y)` is `|b - a|`. -/
theorem dist_hyp_xline (a b y : ℝ) : dist hypMetric Set.univ ![a, y] ![b, y] = |b - a| := by
  refine le_antisymm ?_ ?_
  · calc _ ≤ length hypMetric (xSegment a b y) 0 1 := dist_le_length (xSegment_admissible a b y)
      _ = |b - a| := length_xSegment a b y
  · refine le_csInf ⟨_, xSegment a b y, xSegment_admissible a b y, rfl⟩ ?_
    rintro L ⟨c, hc, rfl⟩
    simpa using abs_sub_le_length hc

end

end Lightlike.CMS
