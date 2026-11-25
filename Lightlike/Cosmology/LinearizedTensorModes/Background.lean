import Lightlike.Spacetime.VariationRiemann
import Lightlike.Cosmology.FLRW

/-!
# The spatially flat FLRW background in conformal time (row G1-031, milestone CO4)

The metric `a(η)² η_{μν}` in the chart `(η, x, y, z)` with `η_{μν} = diag(-1, 1, 1, 1)`, `a : ℝ → ℝ`.
* `confMetric a` : this metric; `sgn μ` : the sign `η_{μμ}`.
* `cc i j k` : the integer coefficients of the Christoffel symbols, `Γ^i_{jk} = cc i j k · 𝓗` with the
  conformal Hubble rate `𝓗 = a'/a` (`Cosmology.Hf`), `christoffel_conf`.

The first-order perturbations of this background, their linearized Einstein tensor and the tensor and
scalar sectors are in the later files of this folder.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Cosmology.LinearizedTensorModes

open Lightlike Lightlike.Cosmology

/-- The sign `η_{μμ}` of the Minkowski metric `diag(-1, 1, 1, 1)`. -/
def sgn (μ : Fin 4) : ℝ := if μ = 0 then -1 else 1

/-- The spatially flat FLRW metric in conformal time, `a(η)² diag(-1, 1, 1, 1)`. -/
def confMetric (a : ℝ → ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal fun μ => sgn μ * a (y 0) ^ 2

/-- The coefficient of `𝓗 = a'/a` in the Christoffel symbol `Γ^i_{jk}` of `confMetric a`. -/
def cc (i j k : Fin 4) : ℝ :=
  (if j = 0 ∧ k = i then 1 else 0) + (if k = 0 ∧ j = i then 1 else 0) +
    (if i = 0 ∧ j = k then sgn j else 0)

variable {a : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- The entries of `confMetric a`. -/
theorem confMetric_apply (y : Fin 4 → ℝ) (l k : Fin 4) :
    confMetric a y l k = if l = k then sgn l * a (y 0) ^ 2 else 0 := by
  simp [confMetric, Matrix.diagonal_apply]

/-- The partial derivatives of the entries of `confMetric a`. -/
theorem pd_confMetric (ha : DifferentiableAt ℝ a (x 0)) (j l k : Fin 4) :
    pd j (fun y => confMetric a y l k) x =
      if l = k then (if j = 0 then sgn l * (2 * a (x 0) * deriv a (x 0)) else 0) else 0 := by
  by_cases hlk : l = k
  · subst hlk
    have hd : HasDerivAt (fun t => sgn l * a t ^ 2) (sgn l * (2 * a (x 0) * deriv a (x 0))) (x 0) := by
      have := (ha.hasDerivAt.pow 2).const_mul (sgn l)
      convert this using 1
      simp
    have h := (hasPd_comp0 (j := j) (x := x) (φ := fun t => sgn l * a t ^ 2) hd.differentiableAt).2
    rw [hd.deriv] at h
    simp only [confMetric_apply, ite_true]
    exact h
  · simp only [confMetric_apply, hlk, ite_false]
    exact pd_const _ _ _

/-- The Christoffel symbols of the conformal FLRW metric: `Γ^i_{jk} = cc i j k · 𝓗`. -/
theorem christoffel_conf (ha : DifferentiableAt ℝ a (x 0)) (hpos : a (x 0) ≠ 0) (i j k : Fin 4) :
    christoffel (confMetric a) i j k x = cc i j k * Hf a x := by
  have hd : ∀ μ, sgn μ * a (x 0) ^ 2 ≠ 0 := by
    intro μ; unfold sgn; split_ifs <;> simp [hpos]
  rw [christoffel_diag (confMetric a) (fun y μ => sgn μ * a (y 0) ^ 2) (fun y => rfl) x hd]
  simp only [pd_confMetric ha]
  unfold Hf
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [cc, sgn] <;> field_simp

end Lightlike.Cosmology.LinearizedTensorModes

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.cc := _root_.Lightlike.Cosmology.LinearizedTensorModes.cc
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.christoffel_conf := _root_.Lightlike.Cosmology.LinearizedTensorModes.christoffel_conf
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.confMetric := _root_.Lightlike.Cosmology.LinearizedTensorModes.confMetric
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.confMetric_apply := _root_.Lightlike.Cosmology.LinearizedTensorModes.confMetric_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.pd_confMetric := _root_.Lightlike.Cosmology.LinearizedTensorModes.pd_confMetric
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.sgn := _root_.Lightlike.Cosmology.LinearizedTensorModes.sgn
