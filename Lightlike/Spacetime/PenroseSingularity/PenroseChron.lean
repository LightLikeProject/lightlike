import Lightlike.Spacetime.PenroseSingularity.FocalBound
import Lightlike.Spacetime.PenroseSingularity.PenroseFocal

/-!
# Penrose's singularity theorem from focusing (G1-012)

`penrose_of_focal_chron` is Penrose's theorem for a closed trapped spacelike surface, assuming the second
variation fact `FocalImpliesChron`, the null energy condition in charts `ChartNEC`, and the uniform expansion
bound `UniformExpansion` over the surface.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **Penrose's theorem, modulo `FocalImpliesChron`, `ChartNEC` and `UniformExpansion`.** -/
theorem penrose_of_focal_chron (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g)
    (hGH : Causal.IsGloballyHyperbolic T) (hn : 3 ≤ n) {S : Set M} (hS : IsCompact S)
    (htrap : IsClosedTrappedSpacelikeSurface g cov T S) (Sig : Set M)
    (hCS : Causal.IsCauchySurface T Sig) [ConnectedSpace Sig] [NoncompactSpace Sig]
    (hKne : (frontier (Causal.causalFutureSet T S)).Nonempty) (hChron : FocalImpliesChron g T S)
    (hNEC : ChartNEC g) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : UniformExpansion g cov T S Λ) :
    NullGeodesicallyIncomplete g :=
  penrose_of_focal_bound g T hGH hS Sig hCS hKne hΛ0
    (normalisedFocalBound_of_chron g hLC T hn htrap hChron hNEC hΛ)

end Lightlike.Penrose
