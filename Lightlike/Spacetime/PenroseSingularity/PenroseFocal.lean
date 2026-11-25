import Lightlike.Spacetime.PenroseSingularity.PenroseCovering
import Lightlike.Spacetime.PenroseSingularity.Projection
import Lightlike.Spacetime.PenroseSingularity.ExpCompact

/-!
# Penrose's theorem modulo the focal bound (G1-012)

`penrose_of_focal_bound` assembles the proved steps of Penrose's argument: the causal future of the
compact trapped surface is closed (`isClosed_causalFutureSet`, from global hyperbolicity), the
boundary `∂J⁺(S)` is covered by a compact set from the normalised focal bound
(`exists_compact_cover_of_focal`), the projection along a timelike flow into the Cauchy surface is
continuous with open range (`exists_projection`), and the last topological step
(`not_open_range_of_noncompact`). The one hypothesis left is the **focal bound**
`NormalisedFocalBound T S Λ`: every future null geodesic from `S` to a point outside `I⁺(S)` has
normalised affine length at most `Λ` (the output of null focusing, step D).
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **Penrose's singularity theorem, modulo the focal bound.** -/
theorem penrose_of_focal_bound (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (T : Causal.TimeOrientation g) (hGH : Causal.IsGloballyHyperbolic T)
    {S : Set M} (hS : IsCompact S) (Sig : Set M) (hCS : Causal.IsCauchySurface T Sig)
    [ConnectedSpace Sig] [NoncompactSpace Sig]
    (hKne : (frontier (Causal.causalFutureSet T S)).Nonempty) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hfocal : NormalisedFocalBound T S Λ) : NullGeodesicallyIncomplete g := by
  have hclosed : IsClosed (Causal.causalFutureSet T S) := Causal.isClosed_causalFutureSet T hGH hS
  obtain ⟨X, hXs, hX⟩ := Causal.exists_smooth_field T
  obtain ⟨proj, hproj, hopen⟩ := exists_projection T hXs (fun x => hX x) hCS hclosed
  exact penrose_of_covering g T S Sig hKne
    (fun hc => exists_compact_cover_of_focal T hc hS hΛ hfocal hclosed) proj hproj hopen

end Lightlike.Penrose
