import Lightlike.Spacetime.EHManifold.CompactVariation

/-!
# The Einstein–Hilbert action with matter: the first variation of the total action

Carroll (4.68) to (4.70): for the total action `S = S_H / (8πG) + S_M`, the variation with respect to the
metric gives Einstein's equation with the energy-momentum tensor `T_{μν} = -(1/√-g) δS_M/δg^{μν}`.

Here the matter action is an arbitrary function of the metric, with a prescribed first variation:
`HasMatterVariation SM g T K` says that for every perturbation `h` of the metric vanishing outside the
compact set `K`, `d/dt SM (g + t h) = ∫_K ⟨T, h⟩_g d vol_g` at `t = 0`, for a symmetric tensor field `T`
(the energy-momentum tensor with lower indices; this is Carroll's definition (4.70) rewritten for a
variation of the metric instead of its inverse, which changes the sign). Then (`hasDerivAt_total_action`)

`d/dt [ehAction (g + t h) Λ K / κ + SM (g + t h)] = -(1/κ) ∫_K ⟨G + Λ g, h⟩_g d vol_g + ∫_K ⟨T, h⟩_g d vol_g`,

so the total action is stationary for all `h` exactly when `∫_K ⟨G + Λ g - κ T, h⟩_g d vol_g = 0` for all
`h`; with `κ = 8πG` this is the weak form of `G + Λ g = 8πG T` (Carroll (4.69) with (4.70)). The pointwise
equation is not derived here.

`contractWith g A h p = ⟨A, h⟩_g (p)` is the contraction, with the inverse metric, of two symmetric tensor
fields.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.68) to
  (4.70), p. 116.
-/

open MeasureTheory Set Manifold TopologicalSpace
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **The contraction `⟨A, h⟩_g` of two symmetric tensor fields** with the inverse metric, at a point. -/
def contractWith (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (A h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (p : M) : ℝ :=
  formContract (coordBasis p (FiberBundle.mem_baseSet_trivializationAt' p)) (g.g p).toBilinForm
    (A.h p).toBilinForm (h.h p).toBilinForm

variable [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]

/-- **A matter action with energy-momentum tensor `T`**: the first variation of `SM` at `g`, for
perturbations of the metric vanishing outside `K`, is `∫_K ⟨T, h⟩_g d vol_g`. -/
def HasMatterVariation (SM : NondegMetric 𝓘(ℝ, Fin n → ℝ) M → ℝ)
    (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (T : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M) : Prop :=
  ∀ h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M, (∀ p, p ∉ K → h.h p = 0) →
    HasDerivAt (fun t : ℝ => SM (g.perturb h t))
      (∫ p in K, contractWith g T h p ∂(NondegMetric.volumeMeasure g)) 0

/-- **The first variation of the total action** `S_H / κ + S_M` (`κ = 8πG` in Carroll's (4.68)). -/
theorem hasDerivAt_total_action (SM : NondegMetric 𝓘(ℝ, Fin n → ℝ) M → ℝ)
    (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (T h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {K : Set M}
    (hK : IsCompact K) (hsupp : ∀ p, p ∉ K → h.h p = 0) (Λ κ : ℝ)
    (hM : HasMatterVariation SM g T K) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K / κ + SM (g.perturb h t))
      (-(∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) / κ +
        ∫ p in K, contractWith g T h p ∂(NondegMetric.volumeMeasure g)) 0 :=
  ((eh_first_variation_manifold_compact g h hK hsupp Λ).div_const κ).add (hM h hsupp)

end Lightlike
