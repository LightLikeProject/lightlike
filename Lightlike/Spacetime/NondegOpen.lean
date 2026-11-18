import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.VolumeMeasure

/-!
# Coordinate metrics of any signature on open subsets of `ℝⁿ`, and their volume

For an open set `U ⊆ ℝⁿ` and a coordinate metric `g` on `U` (`IsCoordMetric g U`: symmetric, invertible, smooth; any
signature, in particular positive definite for a Riemannian metric), `openNondeg U g hg` is the smooth symmetric
nondegenerate bilinear field (`NondegMetric`) of the manifold `↥U` whose components at the point `y` are `g y`. This is the
general form of `openMetric` of `OpenCoordMetric.lean`.

* `openNondeg_coordMetric` (**the bridge**): in every chart of `↥U` the coordinate components of `openNondeg U g hg` are `g`.
* `openNondeg_volumeMeasure` (**the volume on one global chart**): the volume measure of a measurable `A ⊆ ↥U` is
  `∫_A √|det g| dx` over the image of `A` in `ℝⁿ`.

**Limits.** Open subsets of `ℝⁿ` only (the manifold `↥U` has the single global chart), no boundary.
-/

open Manifold TopologicalSpace Bundle Matrix MeasureTheory Set
open scoped ContDiff ENNReal
noncomputable section
namespace Lightlike
variable {n : ℕ}

/-- The form of a symmetric invertible matrix is nondegenerate. -/
theorem matForm_nondegenerate {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (v : Fin n → ℝ)
    (h : ∀ w, matForm A v w = 0) : v = 0 := by
  have h1 := h (A⁻¹ *ᵥ v)
  rw [matForm_eq_dotProduct, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec] at h1
  simpa [dotProduct_self_eq_zero] using h1

/-- **A coordinate metric of any signature on an open set of `ℝⁿ` is a metric on the open subset.** -/
def openNondeg (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsCoordMetric g U) : NondegMetric 𝓘(ℝ, Fin n → ℝ) U where
  g x := matForm (g x.1)
  symm x v w := by
    have hs := hg.symm x.1 x.2
    have key : ∀ v w : Fin n → ℝ, matForm (g x.1) v w = matForm (g x.1) w v := fun v w => by
      rw [matForm_eq_dotProduct, matForm_eq_dotProduct, Matrix.dotProduct_mulVec,
        ← Matrix.vecMul_transpose, hs, dotProduct_comm]
    exact key v w
  nondegenerate x v h := matForm_nondegenerate (hg.isUnit_det x.1 x.2) v h
  contMDiff := contMDiff_matForm U g hg.smooth

/-- **The bridge**: in every chart of `↥U` the coordinate components of `openNondeg U g hg` are `g`. -/
theorem openNondeg_coordMetric (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsCoordMetric g U) (x₀ : U) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    (openNondeg U g hg).coordMetric x₀ y = g y := by
  ext i j
  rw [NondegMetric.coordMetric_eq _ x₀ hy, coordBasis_apply, coordBasis_apply, opens_symmL]
  show matForm (g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U).1) (Pi.single i 1) (Pi.single j 1) = g y i j
  rw [matForm_single, opens_extChartAt_symm U x₀ hy]

/-- **The volume on one global chart.** The volume measure of the metric `openNondeg U g hg` of `↥U` of a measurable
set `A` is `∫_A √|det g| dx`, over the image of `A` in `ℝⁿ`. -/
theorem openNondeg_volumeMeasure (U : Opens (Fin n → ℝ)) [MeasurableSpace U] [BorelSpace U]
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsCoordMetric g U) {A : Set U} (hA : MeasurableSet A) :
    (openNondeg U g hg).volumeMeasure A =
      ∫⁻ y in Subtype.val '' A, ENNReal.ofReal √|(g y).det| := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hsrc : A ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := fun p _ => by
    rw [extChartAt_source]; exact mem_chart_source _ p
  rw [NondegMetric.volumeMeasure_chart (openNondeg U g hg) x₀ hA hsrc]
  have himg : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A = Subtype.val '' A := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, (opens_extChartAt_apply U x₀ p).symm⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, opens_extChartAt_apply U x₀ p⟩
  have hms := measurableSet_image_extChartAt x₀ hA hsrc
  rw [himg] at hms
  rw [himg]
  refine setLIntegral_congr_fun hms fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := hy
  have hpt : p.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
    have := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (hsrc hp)
    rwa [opens_extChartAt_apply U] at this
  show ENNReal.ofReal (NondegMetric.volDensity (openNondeg U g hg) x₀ p.1) = _
  unfold NondegMetric.volDensity
  rw [openNondeg_coordMetric U g hg x₀ hpt]

end Lightlike
