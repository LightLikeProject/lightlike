import Lightlike.Tests.Curvature
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# The round 2-sphere on the manifold layer

`sphereOpen` is the chart domain `0 < θ < π` of the coordinates `(θ, φ)` as an open subset of `ℝ²`, and
`roundSphereMetric r hr` the smooth Riemannian metric `r² (dθ² + sin²θ dφ²)` on it, a `NondegMetric`
(`openNondegMetric`: a coordinate metric on an open set of `ℝⁿ` is a smooth symmetric nondegenerate form
on the manifold `↥U`, the same construction as `openMetric` without the signature).

* `roundSphere_coordMetric` (**the bridge**): in every chart its coordinate components are the coordinate
  metric `twoMetric (r²) (r²)` of `Lightlike/Tests/Curvature.lean`;
* `roundSphere_scalarCurvatureAt`: for every Levi-Civita connection of `roundSphereMetric r hr` the
  intrinsic scalar curvature `scalarCurvatureAt` is `2 / r²` at every point.

Proof: `scalarCurvatureAt_coord` (the intrinsic scalar curvature is the coordinate one in a chart) and the
coordinate result `sphere_scalar` on `0 < θ < π`.

**Differences from the cited statement** (comparison with Lee, *Introduction to Riemannian Manifolds*, ch. 7,
not read at the cited location: pending): the manifold is the chart domain `0 < θ < π` with `φ ∈ ℝ`
(a covering of the sphere with the poles removed), not the whole `S²`; the radius is a real `r ≠ 0`
(`r²` enters, so `-r` gives the same sphere).
-/

open Bundle Manifold Set TopologicalSpace
open Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

/-- The chart domain `0 < θ < π` of the round sphere as an open subset of `ℝ²`. -/
def sphereOpen : Opens (Fin 2 → ℝ) :=
  ⟨Test.sphereU, (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)⟩

/-- The form of a symmetric matrix is symmetric. -/
theorem matForm_symm_of_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h : Aᵀ = A) (v w : Fin n → ℝ) :
    matForm A v w = matForm A w v := by
  rw [matForm_eq_dotProduct, matForm_eq_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h,
    dotProduct_comm]

/-- The form of an invertible matrix is nondegenerate. -/
theorem eq_zero_of_matForm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hdet : IsUnit A.det)
    (v : Fin n → ℝ) (hv : ∀ w, matForm A v w = 0) : v = 0 := by
  have h0 : Matrix.vecMul v A = 0 := by
    ext j
    have := hv (Pi.single j 1)
    rw [matForm_eq_dotProduct] at this
    simpa [Matrix.mulVec, dotProduct, Matrix.vecMul, Pi.single_apply] using this
  exact (Matrix.vecMul_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr hdet)) (by simpa using h0)

/-- **A coordinate metric on an open set of `ℝⁿ` is a smooth symmetric nondegenerate form on `↥U`.** -/
def openNondegMetric {n : ℕ} (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsCoordMetric g U) : NondegMetric 𝓘(ℝ, Fin n → ℝ) U where
  g x := matForm (g x.1)
  symm x v w := matForm_symm_of_transpose (hg.symm x.1 x.2) v w
  nondegenerate x v hv := eq_zero_of_matForm (hg.isUnit_det x.1 x.2) v hv
  contMDiff := contMDiff_matForm U g hg.smooth

/-- **The bridge**: in every chart of `↥U` the coordinate components of `openNondegMetric U g hg` are `g`. -/
theorem openNondegMetric_coordMetric {n : ℕ} (U : Opens (Fin n → ℝ))
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hg : IsCoordMetric g U) (x₀ : U) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    (openNondegMetric U g hg).coordMetric x₀ y = g y := by
  ext i j
  rw [NondegMetric.coordMetric_eq _ x₀ hy, coordBasis_apply, coordBasis_apply, opens_symmL]
  show matForm (g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U).1) (Pi.single i 1) (Pi.single j 1) = g y i j
  rw [matForm_single, opens_extChartAt_symm U x₀ hy]

variable (r : ℝ) (hr : r ≠ 0)

/-- **The round 2-sphere of radius `r`** (chart domain `0 < θ < π`) as a smooth metric on a manifold. -/
def roundSphereMetric : NondegMetric 𝓘(ℝ, Fin 2 → ℝ) sphereOpen :=
  openNondegMetric sphereOpen (Test.twoMetric (r ^ 2) (r ^ 2))
    (Test.isCoordMetric_two (pow_ne_zero 2 hr) (pow_ne_zero 2 hr))

/-- **The bridge**: in every chart the coordinate components are `diag(r², r² sin²θ)`. -/
theorem roundSphere_coordMetric (x₀ : sphereOpen) {y : Fin 2 → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x₀).target) :
    (roundSphereMetric r hr).coordMetric x₀ y = Test.twoMetric (r ^ 2) (r ^ 2) y :=
  openNondegMetric_coordMetric sphereOpen _ _ x₀ hy

variable (cov : Connection 𝓘(ℝ, Fin 2 → ℝ) sphereOpen) [LocallySmoothConnection cov]

/-- **The round 2-sphere of radius `r` has scalar curvature `2 / r²`**, for the intrinsic
`scalarCurvatureAt` of any Levi-Civita connection of `roundSphereMetric r hr`. -/
theorem roundSphere_scalarCurvatureAt (h : cov.IsLeviCivita (roundSphereMetric r hr)) (x : sphereOpen) :
    cov.scalarCurvatureAt (roundSphereMetric r hr) x = 2 / r ^ 2 := by
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin 2 → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin 2 → ℝ) x).map_source hzs
  have hS := scalarCurvatureAt_coord cov x (roundSphereMetric r hr) h hy
  rw [(extChartAt 𝓘(ℝ, Fin 2 → ℝ) x).left_inv hzs] at hS
  rw [hS, scalarCurvature_congr_on (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 2 → ℝ)) x)
    (fun z hz => roundSphere_coordMetric r hr x hz) hy]
  have hx : extChartAt 𝓘(ℝ, Fin 2 → ℝ) x x ∈ Test.sphereU := by
    rw [opens_extChartAt_apply]; exact x.2
  exact Test.sphere_scalar hr (Test.sin_ne_zero_of_mem_sphereU hx)

end Lightlike
