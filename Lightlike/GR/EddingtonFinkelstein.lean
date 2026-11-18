import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# The ingoing Eddington–Finkelstein chart of Schwarzschild

In ingoing Eddington–Finkelstein coordinates `(v, r, θ, φ) = (y 0, y 1, y 2, y 3)` the Schwarzschild
metric is
`ds² = -(1 - 2M/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²`,
smooth and Lorentzian for every `r > 0`, in particular across the horizon `r = 2M`
(`efMetric`, `isCoordMetric_ef`, `ef_isLorentzian`).

Gap row G1-020 (Kruskal–Szekeres, Eddington–Finkelstein, event horizon, interior). The comparison
with Carroll, *Spacetime and Geometry*, ch. 5 and 7, and Wald, ch. 6, is pending (not read at a
location).
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The ingoing Eddington–Finkelstein metric in coordinates `(v, r, θ, φ)`. -/
def efMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(1 - 2 * M / y 1), 1, 0, 0;
     1, 0, 0, 0;
     0, 0, y 1 ^ 2, 0;
     0, 0, 0, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The domain `r > 0`, `0 < θ < π` of the chart. -/
def efU : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_efU : IsOpen (efU) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

/-- The determinant of the Eddington–Finkelstein metric is `-r⁴ sin²θ`. -/
lemma det_efMetric (y : Fin 4 → ℝ) : (efMetric M y).det = -(y 1 ^ 4 * sin (y 2) ^ 2) := by
  simp [efMetric, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **The ingoing Eddington–Finkelstein metric is a coordinate metric for every `r > 0`**: smooth,
symmetric and invertible, also at the horizon `r = 2M`. -/
theorem isCoordMetric_ef : IsCoordMetric (efMetric M) efU where
  isOpen := isOpen_efU
  symm := fun y _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [efMetric]
  isUnit_det := fun y hy => by
    rw [det_efMetric]
    have hs := sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2
    have hr := hy.1
    exact (neg_ne_zero.2 (mul_pos (pow_pos hr 4) (pow_pos hs 2)).ne').isUnit
  smooth := fun i j => by
    have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) efU :=
      (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
    have hθ : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) := by fun_prop
    have hr0 : ∀ y ∈ efU, y 1 ≠ 0 := fun y hy => hy.1.ne'
    fin_cases i <;> fin_cases j <;> simp [efMetric]
    · exact (contDiffOn_const.div hr hr0).sub contDiffOn_const
    all_goals first
      | exact contDiffOn_const
      | exact hr.pow 2
      | exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn

/-- **Signature.** The Eddington–Finkelstein metric has Lorentzian signature for every `r > 0`, also
at `r = 2M`: with `f = 1 - 2M/r`, `g = Pᵀ η P` for the block matrix `P` with the `2 × 2` block
`[[-(1+f)/2, 1], [(1-f)/2, 1]]` and `r`, `r sin θ` on the rest of the diagonal. -/
theorem ef_isLorentzian : IsLorentzianCoordMetric (efMetric M) efU := by
  refine ⟨isCoordMetric_ef M, fun y hy => ?_⟩
  obtain ⟨hr, h2, h3⟩ := hy
  have hs := sin_pos_of_pos_of_lt_pi h2 h3
  set f : ℝ := 1 - 2 * M / y 1 with hf
  refine ⟨!![-(1 + f) / 2, 1, 0, 0;
             (1 - f) / 2, 1, 0, 0;
             0, 0, y 1, 0;
             0, 0, 0, y 1 * sin (y 2)], ?_, ?_⟩
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    have hK : 0 < y 1 * (y 1 * sin (y 2)) := mul_pos hr (mul_pos hr hs)
    intro h
    have : (-f + -1) / 2 * (y 1 * (y 1 * sin (y 2))) + -((1 - f) / 2 * (y 1 * (y 1 * sin (y 2)))) =
        -(y 1 * (y 1 * sin (y 2))) := by ring
    rw [this] at h
    exact hK.ne' (neg_eq_zero.1 h)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [efMetric, eta, etaDiag, Matrix.mul_apply, Fin.sum_univ_four, hf] <;> ring

end Lightlike
