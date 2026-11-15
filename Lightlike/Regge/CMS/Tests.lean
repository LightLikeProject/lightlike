import Mathlib
import Lightlike.Tests.Curvature
import Lightlike.Regge.CMS.Final

/-!
# Trust checks for the curvature side of the weighted deficit convergence (RC6b)

The right-hand side of `IsRiemMetric.cms_convergence` is `∫_Ω f (R/2) √det g`. These checks show
that this integral is the right one:

* `flat_density`: a constant metric has density 0, so the deficits of a flat triangulation must
  sum to 0 (`Fat.lean` shows a flat star has deficit 0).
* `sphere_total_curvature`: on the round unit sphere, in the latitude-longitude chart, the weight
  `f = 1` gives `4π`, the total curvature (Gauss-Bonnet).
* `sphere_unweighted_ne`: the same integral without the volume density `√det g` gives `2π²`,
  not `4π`, so a density without volume weights is rejected.
-/

open MeasureTheory Set Real Matrix Lightlike

namespace Lightlike.CMS

/-- The constant metric is flat: its scalar curvature vanishes. -/
theorem flat_scalarCurvature (x : Fin 2 → ℝ) :
    scalarCurvature (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) x = 0 := by
  have hΓ : ∀ i j k, christoffel (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j k = fun _ => 0 := by
    intro i j k; funext y
    simp [christoffel, pd]
  simp [scalarCurvature, ricci, riemann, hΓ, pd]

/-- **Flat check.** The density `(R/2) √det g` of the constant metric is identically 0. -/
theorem flat_density (x : Fin 2 → ℝ) :
    scalarCurvature (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) x / 2 *
      √(((fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) x).det) = 0 := by
  simp [flat_scalarCurvature]

/-- The chart box `(0, π) × (0, 2π)` of the sphere. -/
def sphereBox : Set (Fin 2 → ℝ) := Set.pi univ ![Ioo 0 π, Ioo 0 (2 * π)]

theorem measurableSet_sphereBox : MeasurableSet sphereBox :=
  MeasurableSet.univ_pi fun i => by fin_cases i <;> simp [measurableSet_Ioo]

/-- On the box, the density of the unit sphere is `sin θ`. -/
theorem sphere_density_eq {x : Fin 2 → ℝ} (hx : x ∈ sphereBox) :
    scalarCurvature (Test.twoMetric 1 1) x / 2 * √((Test.twoMetric 1 1 x).det) = sin (x 0) := by
  have h0 : x 0 ∈ Ioo 0 π := by simpa [sphereBox] using hx 0 (mem_univ 0)
  have hs : 0 < sin (x 0) := sin_pos_of_pos_of_lt_pi h0.1 h0.2
  have hsc := Test.scalar_two (A := 1) (B := 1) one_ne_zero one_ne_zero hs.ne'
  rw [hsc]
  have : (Test.twoMetric 1 1 x).det = sin (x 0) ^ 2 := by
    simp [Test.twoMetric, Test.twoD, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [this, Real.sqrt_sq hs.le]; ring

/-- A product-form integral over the box: `∫_box a(θ) b(φ) = (∫_0^π a)(∫_0^{2π} b)`. -/
theorem box_integral (a b : ℝ → ℝ) :
    ∫ x in sphereBox, a (x 0) * b (x 1) =
      (∫ t in Ioo 0 π, a t) * ∫ t in Ioo 0 (2 * π), b t := by
  rw [← integral_indicator measurableSet_sphereBox]
  have e : ∀ x : Fin 2 → ℝ, sphereBox.indicator (fun x => a (x 0) * b (x 1)) x =
      ∏ i, (![Ioo 0 π, Ioo 0 (2 * π)] i).indicator (![a, b] i) (x i) := by
    intro x
    by_cases hx : x ∈ sphereBox
    · rw [Set.indicator_of_mem hx]
      have h0 : x 0 ∈ Ioo 0 π := by simpa [sphereBox] using hx 0 (mem_univ 0)
      have h1 : x 1 ∈ Ioo 0 (2 * π) := by simpa [sphereBox] using hx 1 (mem_univ 1)
      simp [Fin.prod_univ_two, h0, h1]
    · rw [Set.indicator_of_notMem hx]
      have : ¬ (x 0 ∈ Ioo 0 π ∧ x 1 ∈ Ioo 0 (2 * π)) := by
        rintro ⟨h0, h1⟩
        apply hx
        intro i _
        fin_cases i
        · simpa using h0
        · simpa using h1
      simp only [Fin.prod_univ_two]
      by_cases h0 : x 0 ∈ Ioo 0 π
      · have h1 : x 1 ∉ Ioo 0 (2 * π) := fun h1 => this ⟨h0, h1⟩
        simp [h1]
      · simp [h0]
  simp_rw [e]
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (ι := Fin 2) (E := fun _ => ℝ)
    (μ := fun _ => (volume : Measure ℝ)) (fun i => (![Ioo 0 π, Ioo 0 (2 * π)] i).indicator (![a, b] i))
  rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ => (volume : Measure ℝ)) from rfl,
    this, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Ioo]

/-- **Sphere check.** With the weight `f = 1` the density integrates to `4π` over the chart of
the round unit sphere (the total curvature, Gauss-Bonnet). -/
theorem sphere_total_curvature :
    ∫ x in sphereBox, 1 * (scalarCurvature (Test.twoMetric 1 1) x / 2 *
      √((Test.twoMetric 1 1 x).det)) = 4 * π := by
  rw [setIntegral_congr_fun measurableSet_sphereBox (fun x hx => by
    simp only [one_mul]; exact sphere_density_eq hx)]
  have := box_integral sin (fun _ => 1)
  simp only [mul_one] at this
  rw [this, integral_Ioc_eq_integral_Ioo.symm, integral_Ioc_eq_integral_Ioo.symm]
  simp [← intervalIntegral.integral_of_le, pi_pos.le]
  ring

/-- **Wrong-model check.** Without the volume density `√det g` the same integral is `2π²`, not
`4π`. -/
theorem sphere_unweighted_ne :
    ∫ x in sphereBox, 1 * (scalarCurvature (Test.twoMetric 1 1) x / 2) = 2 * π ^ 2 ∧
      2 * π ^ 2 ≠ 4 * π := by
  refine ⟨?_, ?_⟩
  · rw [setIntegral_congr_fun measurableSet_sphereBox (fun x hx => by
      have h0 : x 0 ∈ Ioo 0 π := by simpa [sphereBox] using hx 0 (mem_univ 0)
      have hs := sin_pos_of_pos_of_lt_pi h0.1 h0.2
      simp only [one_mul]
      rw [Test.scalar_two (A := 1) (B := 1) one_ne_zero one_ne_zero hs.ne'])]
    have := box_integral (fun _ => (1 : ℝ)) (fun _ => 1)
    simp only [mul_one] at this
    have h2 : (2 : ℝ) / 1 / 2 = 1 := by norm_num
    simp only [h2]
    rw [this]
    simp [Real.volume_real_Ioo, pi_pos.le]
    ring
  · intro h
    have : π = 2 := by nlinarith [pi_pos]
    linarith [pi_gt_three]

end Lightlike.CMS
