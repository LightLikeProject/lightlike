import Mathlib
import Lightlike.GR.Schwarzschild
import Lightlike.Regge.Geodesic.Metric

/-!
# The round 2-sphere in the chart `(θ, φ)`

The metric `g = diag(1, sin² x₀)` on the open strip `0 < x₀ < π` of `ℝ²` is the round unit
2-sphere with a meridian removed. This file proves that it is a Riemannian metric on the strip,
that its scalar curvature is the constant `2`, computed from the library's `christoffel`,
`riemann`, `ricci` and `scalarCurvature`, and that the curvature integral
`∫ (R / 2) √det g` over the chart cell `(0, π) × (0, 2π)` is `4π`, the Gauss–Bonnet value.
-/

open Matrix Real Lightlike Lightlike.Geodesic MeasureTheory Set
open scoped ContDiff

namespace Lightlike.CMS

noncomputable section

/-- The diagonal entries `(1, sin² x₀)`. -/
def sphD (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![1, sin (y 0) ^ 2]

/-- The round 2-sphere metric `dθ² + sin² θ dφ²` in the chart `(θ, φ)`. -/
def sphMetric : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun y => diagonal (sphD y)

/-- The open strip `0 < θ < π`, the chart domain. -/
def sphDom : Set (Fin 2 → ℝ) := {y | 0 < y 0 ∧ y 0 < π}

lemma isOpen_sphDom : IsOpen sphDom :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)

lemma sin_pos_of_mem {y : Fin 2 → ℝ} (hy : y ∈ sphDom) : 0 < sin (y 0) :=
  sin_pos_of_pos_of_lt_pi hy.1 hy.2

/-- The expected Christoffel symbols: `Γ⁰₁₁ = -sin θ cos θ`, `Γ¹₀₁ = Γ¹₁₀ = cos θ / sin θ`. -/
def sphΓ (i j k : Fin 2) (y : Fin 2 → ℝ) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 1 then -(sin (y 0) * cos (y 0))
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then cos (y 0) / sin (y 0) else 0

lemma pd_sphD0 (k : Fin 2) (y : Fin 2 → ℝ) : pd k (fun y => sphD y 0) y = 0 := by
  simp [sphD, pd_const]

lemma pd_sphD1 (k : Fin 2) (y : Fin 2 → ℝ) :
    pd k (fun y => sphD y 1) y = if k = 0 then 2 * sin (y 0) * cos (y 0) else 0 := by
  have hf : HasDerivAt (fun t : ℝ => sin t ^ 2) (2 * sin (y 0) * cos (y 0)) (y 0) := by
    have := (hasDerivAt_sin (y 0)).pow 2
    convert this using 1
    simp
  simpa [sphD] using pd_coord (n := 2) 0 k hf

lemma christoffel_sph (y : Fin 2 → ℝ) (hy : sin (y 0) ≠ 0) (i j k : Fin 2) :
    christoffel sphMetric i j k y = sphΓ i j k y := by
  have hd : ∀ i, sphD y i ≠ 0 := by
    intro i; fin_cases i <;> simp [sphD, hy]
  change christoffel (fun y => diagonal (sphD y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [sphΓ, pd_sphD0, pd_sphD1] <;> simp [sphD] <;> field_simp

lemma pd_sphΓ (m i j k : Fin 2) (x : Fin 2 → ℝ) (hx : sin (x 0) ≠ 0) :
    pd m (sphΓ i j k) x =
      if m = 0 ∧ i = 0 ∧ j = 1 ∧ k = 1 then -(cos (x 0) ^ 2 - sin (x 0) ^ 2)
      else if m = 0 ∧ i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then -(1 / sin (x 0) ^ 2)
      else 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -(sin t * cos t)) (-(cos (x 0) ^ 2 - sin (x 0) ^ 2)) (x 0) := by
    have := ((hasDerivAt_sin (x 0)).mul (hasDerivAt_cos (x 0))).neg
    convert this using 1; ring
  have h2 : HasDerivAt (fun t : ℝ => cos t / sin t) (-(1 / sin (x 0) ^ 2)) (x 0) := by
    have := (hasDerivAt_cos (x 0)).div (hasDerivAt_sin (x 0)) hx
    convert this using 1
    field_simp
    nlinarith [sin_sq_add_cos_sq (x 0)]
  have c1 := pd_coord (n := 2) 0 m h1
  have c2 := pd_coord (n := 2) 0 m h2
  rw [show sphΓ i j k = fun y => sphΓ i j k y from rfl]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
    simp [sphΓ, pd_const] <;>
    first | (simp at c1; linarith) | (simp at c2; linarith)

lemma christoffel_sph_eventually {x : Fin 2 → ℝ} (hx : x ∈ sphDom) (i j k : Fin 2) :
    christoffel sphMetric i j k =ᶠ[nhds x] sphΓ i j k := by
  filter_upwards [isOpen_sphDom.mem_nhds hx] with y hy
  exact christoffel_sph y (sin_pos_of_mem hy).ne' i j k

theorem ricci_sph {x : Fin 2 → ℝ} (hx : x ∈ sphDom) :
    ricci sphMetric 0 0 x = 1 ∧ ricci sphMetric 1 1 x = sin (x 0) ^ 2 ∧
      ricci sphMetric 0 1 x = 0 ∧ ricci sphMetric 1 0 x = 0 := by
  have hs : sin (x 0) ≠ 0 := (sin_pos_of_mem hx).ne'
  have hp : ∀ m i j k, pd m (christoffel sphMetric i j k) x = pd m (sphΓ i j k) x :=
    fun m i j k => pd_congr (christoffel_sph_eventually hx i j k) m
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [ricci, riemann, Fin.sum_univ_two, hp, pd_sphΓ _ _ _ _ x hs, christoffel_sph x hs, sphΓ]
    try field_simp
    try nlinarith [sin_sq_add_cos_sq (x 0)]

lemma inv_sph {x : Fin 2 → ℝ} (hx : x ∈ sphDom) :
    (sphMetric x)⁻¹ = diagonal ![1, (sin (x 0) ^ 2)⁻¹] := by
  have hs : sin (x 0) ≠ 0 := (sin_pos_of_mem hx).ne'
  rw [sphMetric, inv_diagonal_of_ne]
  · congr 1; ext i; fin_cases i <;> simp [sphD]
  · intro i; fin_cases i <;> simp [sphD, hs]

/-- **The scalar curvature of the round 2-sphere in the chart is `2`.** -/
theorem scalar_sph {x : Fin 2 → ℝ} (hx : x ∈ sphDom) : scalarCurvature sphMetric x = 2 := by
  have hs : sin (x 0) ≠ 0 := (sin_pos_of_mem hx).ne'
  obtain ⟨h00, h11, h01, h10⟩ := ricci_sph hx
  simp only [scalarCurvature, Fin.sum_univ_two, inv_sph hx, h00, h11, h01, h10]
  simp
  field_simp
  ring

/-- `sphMetric` is a Riemannian metric on the strip `0 < θ < π`. -/
theorem isRiemMetric_sph : IsRiemMetric sphMetric sphDom where
  coord := by
    refine isCoordMetric_diagonal sphD isOpen_sphDom (fun i => ?_) (fun x hx i => ?_)
    · fin_cases i
      · exact contDiffOn_const
      · exact (by
          have : (fun y : Fin 2 → ℝ => sphD y 1) = fun y => sin (y 0) ^ 2 := by ext y; simp [sphD]
          rw [this]; fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => sphD y 1).contDiffOn
    · have := sin_pos_of_mem hx
      fin_cases i <;> simp [sphD, this.ne']
  posDef := fun x hx => by
    have := sin_pos_of_mem hx
    rw [sphMetric, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> simp [sphD, this]

/-- The chart cell `(0, π) × (0, 2π)`: the sphere minus one meridian. -/
def sphCell : Set (Fin 2 → ℝ) := Set.pi univ fun i => Ioo 0 (![π, 2 * π] i)

lemma sphCell_subset : sphCell ⊆ sphDom := fun _ hy =>
  ⟨(hy 0 (mem_univ _)).1, (hy 0 (mem_univ _)).2⟩

/-- On the cell the curvature density `(R / 2) √det g` is `sin θ`. -/
lemma sph_integrand {x : Fin 2 → ℝ} (hx : x ∈ sphCell) :
    scalarCurvature sphMetric x / 2 * √(sphMetric x).det = sin (x 0) := by
  have h := sin_pos_of_mem (sphCell_subset hx)
  rw [scalar_sph (sphCell_subset hx)]
  simp only [sphMetric, det_diagonal, Fin.prod_univ_two, sphD]
  simp [Real.sqrt_sq h.le]

/-- **The curvature integral of the round 2-sphere is `4π`** (Gauss–Bonnet), computed from the
library's scalar curvature in the chart. -/
theorem sph_integral :
    ∫ x in sphCell, (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
      (scalarCurvature sphMetric x / 2 * √(sphMetric x).det) = 4 * π := by
  have hm : MeasurableSet sphCell := MeasurableSet.pi countable_univ fun i _ => measurableSet_Ioo
  rw [setIntegral_congr_fun hm (fun x hx => by
    simp only [one_mul]; exact sph_integrand hx)]
  have : ∀ x : Fin 2 → ℝ, sin (x 0) = ∏ i : Fin 2, (![sin, fun _ => (1 : ℝ)] i) (x i) := by
    intro x; simp [Fin.prod_univ_two]
  simp_rw [this]
  unfold sphCell
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by positivity)]
  simp
  ring

end

end Lightlike.CMS
