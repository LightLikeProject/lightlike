import Lightlike.Spacetime.CurvatureSymmetries
/-!
# The Einstein equations on a manifold: basic API

* `NondegMetric.EinsteinEq g cov Λ κ T`: `cov` is the Levi-Civita connection of `g` and `G + Λ g = κ T` for a source `T`
  (a field of bilinear forms); `satisfiesEinstein_iff_einsteinEq_zero`: the equations of `Connection.lean`
  (`SatisfiesEinstein`) are the case `κ = 1`, `T = 0`.
* `scalarCurvatureAt_of_ricci_eq`: if `Ric = c g` at a point, the scalar curvature is `c d`, `d` the dimension.
* `satisfiesEinstein_iff_ricci`: in dimension `d ≠ 2`, `SatisfiesEinstein cov Λ` is `Ric = (2 Λ / (d - 2)) g` for the
  Levi-Civita connection; `satisfiesEinstein_zero_iff_ricci_eq_zero`: the vacuum equations are `Ric = 0`.

The relation to the coordinate equations in every chart is `satisfiesEinstein_iff_chart_proved` (`ChartAgreement.lean`), the
divergence-free property of `G` is `einstein_divergence_free_proved` (`DivergenceFree.lean`).

**Limits.** Boundaryless Hausdorff `C²` manifolds modelled on a finite-dimensional space (the setting of
`CurvatureSymmetries.lean`); dimension `d = finrank ≠ 2` for the Ricci forms. No statement about the source `T` (its conservation
is not proved here).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology Matrix
noncomputable section
namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] (g : NondegMetric 𝓘(ℝ, E) M)
variable (cov : Connection 𝓘(ℝ, E) M)

/-- If the Ricci tensor at `x` is `c` times the metric, the scalar curvature at `x` is `c` times the dimension. -/
theorem scalarCurvatureAt_of_ricci_eq (x : M) (c : ℝ)
    (h : ∀ v w : TangentSpace 𝓘(ℝ, E) x, cov.ricciAt x v w = c * g.g x v w) :
    cov.scalarCurvatureAt g x = c * Module.finrank ℝ E := by
  unfold Connection.scalarCurvatureAt
  have e : ∀ i j, cov.ricciAt x (Module.finBasis ℝ E i : TangentSpace 𝓘(ℝ, E) x)
      (Module.finBasis ℝ E j : TangentSpace 𝓘(ℝ, E) x) = c * metricGram g x i j := fun i j => h _ _
  simp only [e]
  have hG := Matrix.nonsing_inv_mul _ (metricGram_isUnit g x)
  have hsym : (metricGram g x)ᵀ = metricGram g x := by
    ext i j; exact g.symm x _ _
  show ∑ i, ∑ j, (metricGram g x)⁻¹ i j * (c * metricGram g x i j) = _
  have h1 : ∀ i, ∑ j, (metricGram g x)⁻¹ i j * (c * metricGram g x i j) = c * ((metricGram g x)⁻¹ * metricGram g x) i i := by
    intro i
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun hsym j) i
    simp only [Matrix.transpose_apply] at this
    rw [← this]; ring
  simp only [h1, hG, Matrix.one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The Einstein equations with a cosmological constant `Λ`, a coupling `κ` and a source `T`**: `cov` is the Levi-Civita connection of `g`
and `G + Λ g = κ T`. -/
def _root_.Lightlike.NondegMetric.EinsteinEq (cov : Connection 𝓘(ℝ, E) M) (Λ κ : ℝ)
    (T : Π x : M, TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x → ℝ) : Prop :=
  cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace 𝓘(ℝ, E) x),
    cov.einsteinField g x v w + Λ * g.g x v w = κ * T x v w

/-- The vacuum equations are the equations with no source. -/
theorem satisfiesEinstein_iff_einsteinEq_zero (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔ g.EinsteinEq cov Λ 1 (fun _ _ _ => 0) := by
  unfold NondegMetric.SatisfiesEinstein NondegMetric.EinsteinEq Connection.einsteinField
  simp

/-- **The vacuum equations with a cosmological constant are `Ric = (2 Λ / (d - 2)) g`** in dimension `d ≠ 2`. -/
theorem satisfiesEinstein_iff_ricci (Λ : ℝ) (hd : (Module.finrank ℝ E : ℝ) ≠ 2) :
    g.SatisfiesEinstein cov Λ ↔ cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace 𝓘(ℝ, E) x),
      cov.ricciAt x v w = 2 * Λ / (Module.finrank ℝ E - 2) * g.g x v w := by
  have hd' : (Module.finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 hd
  unfold NondegMetric.SatisfiesEinstein
  refine and_congr_right fun _ => forall_congr' fun x => ?_
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hdd
  constructor
  · intro H v w
    have hRic : ∀ v w : TangentSpace 𝓘(ℝ, E) x,
        cov.ricciAt x v w = (cov.scalarCurvatureAt g x / 2 - Λ) * g.g x v w := fun v w => by
      have := H v w; linarith
    have hS := scalarCurvatureAt_of_ricci_eq g cov x _ hRic
    rw [hRic v w]
    congr 1
    field_simp
    linarith
  · intro H v w
    have hS := scalarCurvatureAt_of_ricci_eq g cov x _ H
    rw [H v w, hS]
    field_simp
    ring

/-- **The vacuum Einstein equations are `Ric = 0`** in dimension `d ≠ 2`. -/
theorem satisfiesEinstein_zero_iff_ricci_eq_zero (hd : (Module.finrank ℝ E : ℝ) ≠ 2) :
    g.SatisfiesEinstein cov 0 ↔ cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace 𝓘(ℝ, E) x), cov.ricciAt x v w = 0 := by
  rw [satisfiesEinstein_iff_ricci g cov 0 hd]
  simp

end Lightlike
