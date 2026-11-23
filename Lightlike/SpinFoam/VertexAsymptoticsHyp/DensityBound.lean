import Lightlike.SpinFoam.VertexAsymptoticsHyp.EdgeKernel
import Lightlike.Lorentz.EPRL

/-!
# The modulus bound of the Lorentzian vertex integrand is integrable on `SL(2,ℂ)^4 × ℂ^10`

Second step of the joint integrability of the vertex integrand (task T-SF10-P1). Write
`D(X, w) = ∏_e lorEdgeDensity X (lorSpinor ∘ w) e`, the bound of `norm_lorIntegrand_le`.

* `integral_vertexDensity`: `∫_{ℂ^10} D(X, w) dw = ∏_e I((conj X_src)⁻¹ conj X_tgt)`
  (Fubini over the ten edges and `integral_lorEdgeDensity_eq_kernelI`);
* `integrable_kernelProd_gauge`: this product, at `X = gauge x`, is integrable over the four free
  vertices for `haar4 = haarC^4` (`Lightlike.Lorentz.integrable_linkProd_kernelI` and the
  invariance of `haarC` under `conjSL`).
-/

open MeasureTheory Matrix
open scoped ENNReal NNReal
open Lightlike Lightlike.Lorentz Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- **The `ℂ^10` integral of the modulus bound is a product of ten kernels `I`.** -/
theorem integral_vertexDensity (X : Fin 5 → SL2C) :
    ∫ w : Fin 10 → ℂ, ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e =
      ∏ e : Fin 10, kernelI ((conjSL (X (edgeSrc e)))⁻¹ * conjSL (X (edgeTgt e))) := by
  have h := integral_fintype_prod_eq_prod (ι := Fin 10) (μ := fun _ : Fin 10 => (volume : Measure ℂ))
    (fun (e : Fin 10) (w' : ℂ) => lorEdgeDensity X (fun _ => lorSpinor w') e)
  rw [← volume_pi] at h
  refine h.trans (Finset.prod_congr rfl fun e _ => ?_)
  exact integral_lorEdgeDensity_eq_kernelI _ _

/-- `conjSL` preserves the chart Haar measure `haarC`. -/
theorem map_conjSL_haarC : haarC.map conjSL = haarC := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, s = Measure.haarScalarFactor haarC SL2C.haar := ⟨_, rfl⟩
  have hC : haarC = s • SL2C.haar := by rw [hs]; exact haarC_eq_smul
  rw [hC, Measure.map_smul _ continuous_conjSL.measurable.aemeasurable, map_conjSL_haar]

/-- Conjugation of the four free variables preserves `haar4`. -/
theorem measurePreserving_conjPi_haar4 :
    MeasurePreserving (fun (x : Fin 4 → SL2C) i => conjSL (x i)) haar4 haar4 := by
  refine ⟨measurable_pi_iff.mpr fun i => continuous_conjSL.measurable.comp (measurable_pi_apply i), ?_⟩
  have hsf : SigmaFinite (Measure.map (⇑conjSL) haarC) := by
    rw [map_conjSL_haarC]; infer_instance
  unfold haar4
  rw [Measure.pi_map_pi (μ := fun _ : Fin 4 => haarC) (f := fun _ => ⇑conjSL)
    (fun _ => continuous_conjSL.measurable.aemeasurable)]
  simp only [map_conjSL_haarC]

/-- **The `ℂ^10` integral of the modulus bound is integrable over the four free vertices.** -/
theorem integrable_kernelProd_gauge :
    Integrable (fun x : Fin 4 → SL2C => ∏ e : Fin 10,
      kernelI ((conjSL (gauge x (edgeSrc e)))⁻¹ * conjSL (gauge x (edgeTgt e)))) haar4 := by
  have h := integrable_linkProd_kernelI
  have h2 := (measurePreserving_conjPi_haar4.integrable_comp_emb measurableEmbedding_conjPi).mpr h
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp]
  rw [linkProd_eq_prod_edges]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [gauge_conjSL, gauge_conjSL]

end Lightlike.Asymptotics.Lorentzian
