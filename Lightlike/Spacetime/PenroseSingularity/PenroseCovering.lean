import Lightlike.Spacetime.PenroseSingularity.Assembly
import Lightlike.Spacetime.PenroseSingularity.AchronalBoundary

/-!
# Penrose's theorem with the boundary covered by a compact set (G1-012)

`penrose_of_covering` refines `penrose_of_hypotheses`: the compactness hypothesis on `K = ∂J⁺(S)` is replaced by the
hypothesis that, under null completeness, `K` is **covered by a compact set `C`** (in the textbook proof, `C` is the
image of `S × [0, 2/|θ₀|]` under the normal exponential map: the generators of `∂J⁺(S)` leave `S` orthogonally and, by
null focusing, stop within affine length `2/|θ₀|`). Since `K` is closed (`isClosed_frontier_causalFutureSet`), `K` is
compact. The named hypotheses that remain are `hcover` (generators + focusing + continuity of the normal exponential
map), `hproj` and `hopen` (the projection to the Cauchy surface and invariance of domain), as in
`penrose_of_hypotheses`.
-/

open Set Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M]

/-- **Penrose's theorem, conditional on a compact cover of `∂J⁺(S)`**: see the module docstring. -/
theorem penrose_of_covering (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (T : Causal.TimeOrientation g)
    (S Sig : Set M) [ConnectedSpace Sig] [NoncompactSpace Sig]
    (hKne : (frontier (Causal.causalFutureSet T S)).Nonempty)
    (hcover : NullGeodesicallyComplete g →
      ∃ C : Set M, IsCompact C ∧ frontier (Causal.causalFutureSet T S) ⊆ C)
    (proj : frontier (Causal.causalFutureSet T S) → Sig) (hproj : Continuous proj)
    (hopen : IsOpen (range proj)) : NullGeodesicallyIncomplete g :=
  penrose_of_hypotheses g Sig _ hKne
    (fun hc => by
      obtain ⟨C, hC, hsub⟩ := hcover hc
      exact hC.of_isClosed_subset (Causal.isClosed_frontier_causalFutureSet T S) hsub)
    proj hproj hopen

end Lightlike.Penrose
