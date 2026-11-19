import Lightlike.Spacetime.EHManifold.CompactVariation
import Lightlike.Spacetime.EHManifold.FluxLocal

/-!
# Tests for the first variation of the Einstein–Hilbert action on a manifold

Instances showing that the hypotheses of `eh_first_variation_manifold_compact` can be met:

* `NondegMetric.toSymBilinField`: a metric is a symmetric tensor field, so rescaling the metric inside a
  compact set by a smooth function `χ` supported there is an admissible perturbation
  (`eh_first_variation_conformal`);
* `SymBilinField.zero`: the zero field; the variation along it vanishes (`eh_first_variation_zero`).

No catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Bundle
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A metric, as a symmetric tensor field. -/
def NondegMetric.toSymBilinField (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) :
    SymBilinField 𝓘(ℝ, Fin n → ℝ) M where
  h := g.g
  symm := g.symm
  contMDiff := g.contMDiff

/-- The zero symmetric tensor field. -/
def SymBilinField.zero : SymBilinField 𝓘(ℝ, Fin n → ℝ) M where
  h _ := 0
  symm _ _ _ := rfl
  contMDiff := contMDiff_zeroSection ℝ
    (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ)

variable [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Test: the variation along the zero field vanishes.** -/
theorem eh_first_variation_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K)
    (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb SymBilinField.zero t) Λ K) 0 0 := by
  have h := eh_first_variation_manifold_compact g SymBilinField.zero hK (fun _ _ => rfl) Λ
  have hz : ∫ p in K, ehIntegrand g SymBilinField.zero Λ p ∂(NondegMetric.volumeMeasure g) = 0 := by
    rw [setIntegral_congr_fun hK.measurableSet (g := fun _ => (0 : ℝ)) fun p _ =>
      ehIntegrand_eq_zero g SymBilinField.zero Λ rfl]
    simp
  rw [hz, neg_zero] at h
  exact h

/-- **Test: a conformal perturbation.** For a smooth function `χ` vanishing outside a compact set `K`, the
perturbation `χ g` of the metric `g` is admissible, and the first variation of the action along it is
`-∫_K ⟨G + Λ g, χ g⟩_g d vol_g`. -/
theorem eh_first_variation_conformal (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ) {K : Set M} (hK : IsCompact K)
    (hχK : ∀ p, p ∉ K → χ p = 0) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb (g.toSymBilinField.smulFun χ hχ) t) Λ K)
      (-∫ p in K, ehIntegrand g (g.toSymBilinField.smulFun χ hχ) Λ p
        ∂(NondegMetric.volumeMeasure g)) 0 :=
  eh_first_variation_manifold_compact g (g.toSymBilinField.smulFun χ hχ) hK
    (fun p hp => g.toSymBilinField.smulFun_eq_zero_of_fun χ hχ (hχK p hp)) Λ

end Lightlike
