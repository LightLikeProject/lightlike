import Lightlike.Spacetime.FLRWModel
import Lightlike.Spacetime.StereoConformal

/-!
# The charts of `J × S³` and their derivatives (CO30, attempt 1)

For the product manifold `↥J × S³` with the model `Fin 4 → ℝ` (`FLRWModel.lean`): the chart inverse of `I4` is the chart inverse of the product model
composed with `modelEquiv⁻¹` (`mfderiv_I4_chart_symm`: its derivative, read through `modelEquiv`, is that of the product), the derivative of the chart inverse of
the product acts as the identity on the time component (`mfderiv_chart_symm_opens`) and, through the inclusion of the sphere, as the derivative of the inverse
stereographic map on the spatial one (`chart_symm_deriv`, with the conformal factor of `StereoConformal.lean`).

**Limits.** The derivatives of the charts; the coordinate metric and the Einstein equations are later steps.
-/

open Manifold Metric Bundle TopologicalSpace Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

theorem range_IJS : range IJS = univ := by
  simp [IJS]

theorem range_I4 : range I4 = univ := by
  rw [I4, ModelWithCorners.transContinuousLinearEquiv_range, range_IJS]
  simp

/-- the chart inverse of the product model, as a map of the model `Fin 4 → ℝ` -/
theorem extChartAt_I4_symm (J : Opens ℝ) (x : ↥J × S3) (y : Fin 4 → ℝ) :
    (extChartAt I4 x).symm y = (extChartAt IJS x).symm (modelEquiv.symm y) := rfl

/-- **Step A**: the derivative of the chart inverse for `I4`, read in the coordinates of `IJS` (through `modelEquiv`), is the derivative of the
chart inverse for `IJS` on the preimages. -/
theorem mfderiv_I4_chart_symm (J : Opens ℝ) (x : ↥J × S3) {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target)
    (v : Fin 4 → ℝ) :
    modelEquiv.symm (mfderivWithin 𝓘(ℝ, Fin 4 → ℝ) I4 (extChartAt I4 x).symm (range I4) y v) =
      mfderivWithin 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3)) IJS (extChartAt IJS x).symm (range IJS) (modelEquiv.symm y)
        (modelEquiv.symm v) := by
  have hz : modelEquiv.symm y ∈ (extChartAt IJS x).target := by
    have := hy
    simp only [I4, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  have hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3)) IJS (extChartAt IJS x).symm (range IJS)
      (modelEquiv.symm y) := mdifferentiableWithinAt_extChartAt_symm hz
  rw [range_IJS] at hd ⊢
  rw [mdifferentiableWithinAt_univ] at hd
  have hD := hd.hasMFDerivAt
  have hE := (modelEquiv.symm.hasFDerivAt (x := y)).hasMFDerivAt
  have hc := hD.comp y hE
  have h4 := hasMFDerivAt_transContinuousLinearEquiv_right modelEquiv hc
  rw [range_I4, mfderivWithin_univ]
  have hfun : (extChartAt I4 x).symm = (extChartAt IJS x).symm ∘ ⇑modelEquiv.symm := rfl
  rw [hfun, h4.mfderiv]
  simp
  rfl


theorem extChartAt_IJS (J : Opens ℝ) (x : ↥J × S3) :
    extChartAt IJS x = (extChartAt 𝓘(ℝ, ℝ) x.1).prod (extChartAt (𝓡 3) x.2) := extChartAt_prod x

/-- the chart inverse of the product is the product of the chart inverses -/
theorem extChartAt_IJS_symm (J : Opens ℝ) (x : ↥J × S3) (z : ℝ × EuclideanSpace ℝ (Fin 3)) :
    (extChartAt IJS x).symm z = ((extChartAt 𝓘(ℝ, ℝ) x.1).symm z.1, (extChartAt (𝓡 3) x.2).symm z.2) := by
  rw [extChartAt_prod]; rfl

/-- **The derivative of the chart inverse of an open subset of `ℝ` is the identity.** -/
theorem mfderiv_chart_symm_opens (J : Opens ℝ) (t₀ : J) {s : ℝ} (hs : s ∈ (extChartAt 𝓘(ℝ, ℝ) t₀).target) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) t₀).symm s =
      (ContinuousLinearMap.id ℝ ℝ : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) ((extChartAt 𝓘(ℝ, ℝ) t₀).symm s)) := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) t₀).symm s := by
    have := mdifferentiableWithinAt_extChartAt_symm hs
    simpa [mdifferentiableWithinAt_univ] using this
  have h1 := (hasMFDerivAt_opens_val J ((extChartAt 𝓘(ℝ, ℝ) t₀).symm s)).comp s hd.hasMFDerivAt
  have hev : (Subtype.val ∘ (extChartAt 𝓘(ℝ, ℝ) t₀).symm) =ᶠ[nhds s] id := by
    have hmem : (extChartAt 𝓘(ℝ, ℝ) t₀).target ∈ nhds s := (isOpen_extChartAt_target (I := 𝓘(ℝ, ℝ)) t₀).mem_nhds hs
    filter_upwards [hmem] with y hy
    have h2 := OpenPartialHomeomorph.subtypeRestr_symm_apply (OpenPartialHomeomorph.refl ℝ) ⟨t₀⟩ (U := J) (y := y)
    simp [extChartAt, Opens.chartAt_eq] at hy ⊢
    exact h2 hy
  have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) s (ContinuousLinearMap.id ℝ ℝ) := hasMFDerivAt_id s
  have h4 := h1.congr_of_eventuallyEq hev.symm
  have h5 := hasMFDerivAt_unique h4 h3
  refine ContinuousLinearMap.ext fun w => ?_
  have := congrArg (fun L => L w) h5
  exact this

/-- **Steps B and C**: the derivative of the chart inverse of the product. -/
theorem chart_symm_deriv (J : Opens ℝ) (x : ↥J × S3) {z : ℝ × EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt IJS x).target) (v : ℝ × EuclideanSpace ℝ (Fin 3)) :
    (mfderivWithin 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3)) IJS (extChartAt IJS x).symm (range IJS) z v).1 = v.1 ∧
    dcoe ((extChartAt IJS x).symm z).2 (mfderivWithin 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3)) IJS (extChartAt IJS x).symm
      (range IJS) z v).2 =
      fderiv ℝ (fun u => (((stereographic' 3 (-x.2)).symm u : S3) : E4)) z.2 v.2 := by
  have hz' : z ∈ (extChartAt 𝓘(ℝ, ℝ) x.1).target ×ˢ (extChartAt (𝓡 3) x.2).target := by
    rw [extChartAt_IJS] at hz
    simpa using hz
  have hz1 : z.1 ∈ (extChartAt 𝓘(ℝ, ℝ) x.1).target := hz'.1
  have hz2 : z.2 ∈ (extChartAt (𝓡 3) x.2).target := hz'.2
  have hd1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (extChartAt 𝓘(ℝ, ℝ) x.1).symm z.1 := by
    have := mdifferentiableWithinAt_extChartAt_symm hz1
    simpa [mdifferentiableWithinAt_univ] using this
  have hd2 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (extChartAt (𝓡 3) x.2).symm z.2 := by
    have := mdifferentiableWithinAt_extChartAt_symm hz2
    simpa [mdifferentiableWithinAt_univ] using this
  have h1 := (hd1.hasMFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).hasMFDerivAt)
  have h2 := (hd2.hasMFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).hasMFDerivAt)
  have h12 := h1.prodMk h2
  have hfun : (extChartAt IJS x).symm = fun z' : ℝ × EuclideanSpace ℝ (Fin 3) =>
      (((extChartAt 𝓘(ℝ, ℝ) x.1).symm ∘ Prod.fst) z', ((extChartAt (𝓡 3) x.2).symm ∘ Prod.snd) z') := by
    funext z'; exact extChartAt_IJS_symm J x z'
  rw [range_IJS, mfderivWithin_univ, hfun, h12.mfderiv]
  have hstereo : ∀ u, (((extChartAt (𝓡 3) x.2).symm u : S3) : E4) = (((stereographic' 3 (-x.2)).symm u : S3) : E4) :=
    fun u => by simp [extChartAt]; rfl
  obtain ⟨Df, hDf, hDfa⟩ := hasFDerivAt_stereoMap (stereoW (-x.2)) ((-x.2 : S3) : E4) z.2
  have hf : (fun u => (((stereographic' 3 (-x.2)).symm u : S3) : E4)) = stereoMap (stereoW (-x.2)) ((-x.2 : S3) : E4) := by
    funext w; exact stereographic_symm_eq (-x.2) w
  constructor
  · rw [mfderiv_chart_symm_opens J x.1 hz1]
    rfl
  · have hc := (hasMFDerivAt_sphereIncl ((extChartAt (𝓡 3) x.2).symm z.2)).comp z.2 hd2.hasMFDerivAt
    have hcf : (sphereIncl ∘ (extChartAt (𝓡 3) x.2).symm) = stereoMap (stereoW (-x.2)) ((-x.2 : S3) : E4) := by
      funext u; rw [← hf]; exact hstereo u
    rw [hcf] at hc
    have hu := hasMFDerivAt_unique hc (show HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, E4) _ z.2 Df from hDf.hasMFDerivAt)
    have hfd : fderiv ℝ (fun u => (((stereographic' 3 (-x.2)).symm u : S3) : E4)) z.2 = Df := by
      rw [hf]; exact hDf.fderiv
    rw [hfd]
    have := congrArg (fun L => L v.2) hu
    exact this

end Lightlike
