import Lightlike.Spacetime.GE3Row.Conjugate
import Lightlike.Regge.CMS.Sphere

/-!
# Conjugate points on the round 2-sphere (row G1-006, GE3): the curved trust check

In the chart `(θ, φ)` of the unit 2-sphere (`Lightlike.CMS.sphMetric = diag(1, sin² θ)`), the equator
`γ t = (π/2, t)` is a geodesic with velocity `w = (0, 1)`, and `J t = (sin t, 0)` (a field of
`∂_θ`-length `sin t`) is a Jacobi field along it, with `P = D_t J = (cos t, 0)`. It vanishes at `0` and
`π`, so these are conjugate points: antipodal points are conjugate along a great circle, the
standard example of focusing in positive curvature (compare `not_isConjugateOn_const_metric`).

## Main results

* `riemann_sph_equator`: on the equator `R^0_{101} = 1`, `R^1_{101} = 0` (curvature `+1`), computed
  from the library's `Lightlike.riemann`.
* `isJacobiOn_sph_equator`: `J t = (sin t, 0)` is a Jacobi field along the equator, on all of `ℝ`.
* `isConjugateOn_sph_equator`: `0` and `π` are conjugate along the equator.
-/

open Matrix Real Lightlike Lightlike.Geodesic Lightlike.CMS Set

namespace Lightlike.Geodesic

/-- The equator of the chart, `t ↦ (π/2, t)`. -/
noncomputable def sphEquator (t : ℝ) : Fin 2 → ℝ := ![π / 2, t]

lemma sphEquator_mem (t : ℝ) : sphEquator t ∈ sphDom := by
  refine ⟨?_, ?_⟩ <;> simp [sphEquator] <;> linarith [pi_pos]

lemma sin_sphEquator (t : ℝ) : sin (sphEquator t 0) = 1 := by simp [sphEquator]

lemma cos_sphEquator (t : ℝ) : cos (sphEquator t 0) = 0 := by simp [sphEquator]

/-- On the equator all Christoffel symbols of the chart vanish. -/
lemma christoffel_sph_equator (t : ℝ) (i j k : Fin 2) :
    christoffel sphMetric i j k (sphEquator t) = 0 := by
  rw [christoffel_sph _ (by simp [sin_sphEquator]) i j k]
  simp [sphΓ, sin_sphEquator, cos_sphEquator]

/-- **Curvature on the equator**: `R^0_{101} = 1` and `R^1_{101} = 0` (sectional curvature `+1`). -/
theorem riemann_sph_equator (t : ℝ) (i : Fin 2) :
    riemann sphMetric i 1 0 1 (sphEquator t) = if i = 0 then 1 else 0 := by
  have hx := sphEquator_mem t
  have hs : sin (sphEquator t 0) ≠ 0 := (sin_pos_of_mem hx).ne'
  have hp : ∀ m i j k, pd m (christoffel sphMetric i j k) (sphEquator t) =
      pd m (sphΓ i j k) (sphEquator t) :=
    fun m i j k => pd_congr (christoffel_sph_eventually hx i j k) m
  fin_cases i <;>
  · simp [riemann, hp, pd_sphΓ _ _ _ _ _ hs, christoffel_sph _ hs, sphΓ,
      sin_sphEquator, cos_sphEquator]

/-- **A Jacobi field on the round sphere**: along the equator, `J t = (sin t, 0)` with
`P t = (cos t, 0)` satisfies `D²J = -R(J, w) w = -J`. -/
theorem isJacobiOn_sph_equator :
    IsJacobiOn sphMetric sphEquator (fun _ => ![0, 1]) (fun t => ![sin t, 0])
      (fun t => ![cos t, 0]) univ where
  geodesic := by
    refine ⟨fun t _ => ?_, fun t _ => ?_⟩
    · rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · simpa [sphEquator] using hasDerivAt_const t (π / 2)
      · simpa [sphEquator] using hasDerivAt_id' t
    · have : accel sphMetric (sphEquator t) ![0, 1] = 0 := by
        funext i
        simp [accel, christoffel_sph_equator]
      rw [this]
      exact hasDerivAt_const t _
  deriv_field := fun t _ => by
    have h : gammaApply sphMetric (sphEquator t) ![0, 1] ![sin t, 0] = 0 := by
      funext i
      simp [gammaApply, christoffel_sph_equator]
    rw [h, sub_zero, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_sin t
    · simpa using hasDerivAt_const t (0 : ℝ)
  deriv_cov := fun t _ => by
    have h1 : gammaApply sphMetric (sphEquator t) ![0, 1] ![cos t, 0] = 0 := by
      funext i
      simp [gammaApply, christoffel_sph_equator]
    have h2 : riemannApply sphMetric (sphEquator t) ![0, 1] ![sin t, 0] = ![sin t, 0] := by
      funext i
      simp only [riemannApply, Fin.sum_univ_two]
      fin_cases i <;> simp [riemann_sph_equator]
    rw [h1, h2, hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hasDerivAt_cos t
    · simpa using hasDerivAt_const t (0 : ℝ)

/-- **Trust check, positive curvature**: `0` and `π` are conjugate along the equator of the round
sphere (antipodal points), in contrast to a flat chart (`not_isConjugateOn_const_metric`). -/
theorem isConjugateOn_sph_equator :
    IsConjugateOn sphMetric sphEquator (fun _ => ![0, 1]) univ 0 π := by
  refine ⟨mem_univ _, mem_univ _, pi_pos.ne, _, _, isJacobiOn_sph_equator, ?_, ?_,
    π / 2, mem_univ _, ?_⟩
  · simp
  · simp
  · simp

end Lightlike.Geodesic
