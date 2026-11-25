import Lightlike.Spacetime.PenroseSingularity.Defs
import Lightlike.Spacetime.PenroseSingularity.Skeleton
import Lightlike.Spacetime.Causal.Ladder

/-!
# Penrose's singularity theorem, assembled from named hypotheses (G1-012)

The statement `penrose_of_hypotheses` is the proof skeleton of Penrose's theorem (Hawking–Ellis 1973, §8.2, Prop. 8.2.1;
Senovilla–Garfinkle 2015, Thm 2) in which the geometric steps that are **not yet formalised** are explicit hypotheses:

* `hK` (step 4, **focusing + generators**): if `g` is null geodesically complete, the achronal boundary `K = ∂J⁺(S)` of the
  closed trapped surface `S` is compact (each generator leaves `S` and has a conjugate point within affine length `2/|θ|`
  by null focusing under the NEC, `raychaudhuri_null_focusing`; `K` is the image of a compact set).
* `hproj` (step 5a, **projection**): the flow of a timelike vector field maps `K` continuously into the Cauchy surface `Σ`.
* `hopen` (step 5b, **invariance of domain**): the image of that projection is open in `Σ` (`K` is a topological hypersurface,
  the projection is injective by achronality, Mathlib has no invariance of domain for manifolds).
* `Σ` is connected, non-compact and Hausdorff (the last from `T2Space M`), `K` is non-empty (it contains `S`).

What is proved is the closing step: these hypotheses give `NullGeodesicallyIncomplete g`, via
`Penrose.compactSpace_of_open_range`. Nothing here uses `P18`.
-/

open Set Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M]

/-- **Penrose's theorem, conditional on the geometric steps** (see the module docstring for the four named hypotheses):
a spacetime with a non-compact connected Cauchy surface `Σ` (taken as a subset), and a non-empty `K ⊆ M` that would
be compact under null completeness and projects continuously and openly into `Σ`, is null geodesically incomplete. -/
theorem penrose_of_hypotheses (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (Sig K : Set M)
    [ConnectedSpace Sig] [NoncompactSpace Sig] (hKne : K.Nonempty)
    (hK : NullGeodesicallyComplete g → IsCompact K)
    (proj : K → Sig) (hproj : Continuous proj) (hopen : IsOpen (range proj)) :
    NullGeodesicallyIncomplete g := by
  intro hc
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hK hc)
  have : Nonempty K := hKne.to_subtype
  exact not_open_range_of_noncompact proj hproj hopen

end Lightlike.Penrose
