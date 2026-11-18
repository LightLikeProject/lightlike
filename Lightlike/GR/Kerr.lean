import Lightlike.GR.Schwarzschild

/-!
# The Kerr metric in Boyer–Lindquist coordinates

`ds² = -(1 - 2Mr/Σ) dt² - (4Mar sin²θ/Σ) dt dφ + (Σ/Δ) dr² + Σ dθ² + (r² + a² + 2Ma²r sin²θ/Σ) sin²θ dφ²`
with `Σ = r² + a² cos²θ`, `Δ = r² - 2Mr + a²`, in coordinates `(t, r, θ, φ)` (`kerrMetric`). On
`r > 0`, `Δ ≠ 0`, `0 < θ < π` it is a coordinate metric (`isCoordMetric_kerr`) with determinant
`-Σ² sin²θ` (`det_kerrMetric`), and for `a = 0` it is the Schwarzschild metric
(`kerrMetric_zero`).

Gap row GE6, first stage. The Ricci-flatness, the Killing horizons `κ = √(M²-a²)/(2Mr₊)` and `Ω_H = a/(2Mr₊)`
are not yet proved. Comparison with Boyer–Lindquist (1967) and Carroll, ch. 6: pending.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M a : ℝ)

/-- `Σ = r² + a² cos²θ`. -/
def kerrS (y : Fin 4 → ℝ) : ℝ := y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2

/-- `Δ = r² - 2Mr + a²`. -/
def kerrD (y : Fin 4 → ℝ) : ℝ := y 1 ^ 2 - 2 * M * y 1 + a ^ 2

/-- The Kerr metric in Boyer–Lindquist coordinates `(t, r, θ, φ)`. -/
def kerrMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(1 - 2 * M * y 1 / kerrS a y), 0, 0, -(2 * M * a * y 1 * sin (y 2) ^ 2 / kerrS a y);
     0, kerrS a y / kerrD M a y, 0, 0;
     0, 0, kerrS a y, 0;
     -(2 * M * a * y 1 * sin (y 2) ^ 2 / kerrS a y), 0, 0,
       (y 1 ^ 2 + a ^ 2 + 2 * M * a ^ 2 * y 1 * sin (y 2) ^ 2 / kerrS a y) * sin (y 2) ^ 2]

/-- The domain `r > 0`, `Δ ≠ 0`, `0 < θ < π`. -/
def kerrU : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ kerrD M a y ≠ 0 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_kerrU : IsOpen (kerrU M a) := by
  refine (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_ne_fun (by unfold kerrD; fun_prop) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))

lemma kerrS_pos {y : Fin 4 → ℝ} (hy : 0 < y 1) : 0 < kerrS a y := by
  unfold kerrS; positivity

/-- **The determinant of the Kerr metric is `-Σ² sin²θ`.** -/
lemma det_kerrMetric {y : Fin 4 → ℝ} (hy : 0 < y 1) (hD : kerrD M a y ≠ 0) :
    (kerrMetric M a y).det = -(kerrS a y ^ 2 * sin (y 2) ^ 2) := by
  have hS : kerrS a y ≠ 0 := (kerrS_pos a hy).ne'
  have hS2 : kerrS a y = y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 := rfl
  have hD2 : kerrD M a y = y 1 ^ 2 - 2 * M * y 1 + a ^ 2 := rfl
  have hc := sin_sq_add_cos_sq (y 2)
  simp [kerrMetric, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  rw [hS2, hD2, show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]
  ring

/-- **The Kerr metric is a coordinate metric on `r > 0`, `Δ ≠ 0`, `0 < θ < π`.** -/
theorem isCoordMetric_kerr : IsCoordMetric (kerrMetric M a) (kerrU M a) where
  isOpen := isOpen_kerrU M a
  symm := fun y _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [kerrMetric]
  isUnit_det := fun y hy => by
    rw [det_kerrMetric M a hy.1 hy.2.1]
    have hS := kerrS_pos a hy.1
    have hs := sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2
    exact (neg_ne_zero.2 (by positivity)).isUnit
  smooth := fun i j => by
    intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hS : kerrS a y ≠ 0 := (kerrS_pos a hy.1).ne'
    have hSc : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => kerrS a y := by unfold kerrS; fun_prop
    have hDc : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => kerrD M a y := by unfold kerrD; fun_prop
    have hsc : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => sin (y 2) := by fun_prop
    have hr : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1 := by fun_prop
    have hq : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => 1 / kerrS a y) y :=
      contDiffAt_const.div hSc.contDiffAt hS
    have hq' : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => kerrS a y / kerrD M a y) y :=
      hSc.contDiffAt.div hDc.contDiffAt hy.2.1
    have e1 : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => 2 * M * y 1 * sin (y 2) ^ 2 / kerrS a y) y :=
      ((contDiff_const.mul hr).mul (hsc.pow 2)).contDiffAt.div hSc.contDiffAt hS
    have e2 : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => 2 * M * y 1 / kerrS a y) y :=
      ((contDiff_const.mul hr)).contDiffAt.div hSc.contDiffAt hS
    have e3 : ContDiffAt ℝ ∞
        (fun y : Fin 4 → ℝ => 2 * M * a ^ 2 * y 1 * sin (y 2) ^ 2 / kerrS a y) y :=
      ((contDiff_const.mul hr).mul (hsc.pow 2)).contDiffAt.div hSc.contDiffAt hS
    have e4 : ContDiffAt ℝ ∞
        (fun y : Fin 4 → ℝ => 2 * M * a * y 1 * sin (y 2) ^ 2 / kerrS a y) y :=
      ((contDiff_const.mul hr).mul (hsc.pow 2)).contDiffAt.div hSc.contDiffAt hS
    fin_cases i <;> fin_cases j <;> simp only [kerrMetric] <;> simp <;>
      first
      | exact contDiffAt_const
      | exact e2.sub contDiffAt_const
      | exact e4.neg
      | exact hq'
      | exact hSc.contDiffAt
      | exact ((((hr.pow 2).add contDiff_const).contDiffAt).add e3).mul (hsc.pow 2).contDiffAt

/-- **`a = 0` is Schwarzschild.** -/
theorem kerrMetric_zero {y : Fin 4 → ℝ} (hr : y 1 ≠ 0) : kerrMetric M 0 y = schMetric M y := by
  have hS : kerrS 0 y = y 1 ^ 2 := by simp [kerrS]
  have hD : kerrD M 0 y = y 1 ^ 2 - 2 * M * y 1 := by simp [kerrD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kerrMetric, schMetric, schD, hS, hD, diagonal_apply] <;>
    field_simp <;> ring

/-- The inverse of the Kerr metric, in closed form. -/
def kerrInv (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let S := kerrS a y
  let D := kerrD M a y
  !![-((y 1 ^ 2 + a ^ 2) ^ 2 - D * a ^ 2 * sin (y 2) ^ 2) / (S * D), 0, 0,
      -(2 * M * a * y 1) / (S * D);
     0, D / S, 0, 0;
     0, 0, 1 / S, 0;
     -(2 * M * a * y 1) / (S * D), 0, 0, (D - a ^ 2 * sin (y 2) ^ 2) / (S * D * sin (y 2) ^ 2)]

/-- **The closed form is the inverse** of the Kerr metric on `kerrU`. -/
theorem kerrMetric_mul_kerrInv {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) :
    kerrMetric M a y * kerrInv M a y = 1 := by
  have hS : kerrS a y ≠ 0 := (kerrS_pos a hy.1).ne'
  have hD : kerrD M a y ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hS2 : kerrS a y = y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 := rfl
  have hD2 : kerrD M a y = y 1 ^ 2 - 2 * M * y 1 + a ^ 2 := rfl
  have hc := sin_sq_add_cos_sq (y 2)
  have hc2 : cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerrMetric, kerrInv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    field_simp <;> (try rw [hS2, hD2, hc2]) <;> ring

end Lightlike
