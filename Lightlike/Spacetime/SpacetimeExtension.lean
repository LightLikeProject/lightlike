import Lightlike.Spacetime.Lorentzian

/-!
# Extensions of Lorentzian manifolds and inextendibility

Source read: J. Sbierski, *The C⁰-inextendibility of the Schwarzschild spacetime and the spacelike diameter in
Lorentzian geometry*, arXiv:1507.00601v2 (25 April 2016), Section 2.3, Definition 2.15 (page 11), with the standing
assumption stated there that all manifolds are connected: "A `Cᵏ`-extension of `(M, g)` is a smooth isometric
embedding `ι : M ↪ M̃` of `M` into a proper subset of a Lorentzian manifold `(M̃, g̃)`, where `M̃` is of the same
dimension as `M`, and `g̃` is a `Cᵏ`-regular metric. ... `(M, g)` is called `Cᵏ`-extendible if, and only if, there
exists a `Cᵏ`-extension of `(M, g)`. Otherwise, `(M, g)` is called `Cᵏ`-inextendible."

* `IsLorentzianExtension g g' ι`: `ι : M → M'` is a smooth open embedding with `ι^* g' = g`, the target `M'` is
  connected and `ι` is not onto.
* `IsInextendible g`: no Hausdorff extension exists (in a given universe).

**Differences from the source.**
* (kind: weaker) The metrics of the library are smooth, so `IsInextendible` is inextendibility in the class of
  smooth metrics; it is implied by the `Cᵏ`-inextendibility of the source for every `k` and does not imply it.
* (kind: representation) An embedding between manifolds of the same dimension is an open embedding; the definition
  asks for an open embedding. The source's manifolds are Hausdorff by convention; the Hausdorff property of the
  target is a hypothesis here (without it every manifold has an extension, by doubling a point of its boundary in
  a chart). The source assumes `(M, g)` time-oriented; no time orientation is asked here (its Remark 2.16 (2)
  notes that the notion does not depend on it).
-/

open Manifold
open scoped ContDiff

namespace Lightlike

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **An extension of a Lorentzian manifold** (Sbierski, arXiv:1507.00601v2, Definition 2.15): a smooth isometric
open embedding `ι` of `(M, g)` into a connected Lorentzian manifold `(M', g')` of the same dimension that is
not onto. -/
structure IsLorentzianExtension {n : ℕ} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] (g : LorentzianMetric I M n) (g' : LorentzianMetric I M' n) (ι : M → M') :
    Prop where
  /-- The embedding is smooth. -/
  contMDiff : ContMDiff I I ∞ ι
  /-- It is an open embedding. -/
  isOpenEmbedding : Topology.IsOpenEmbedding ι
  /-- It is isometric: `g'(dι v, dι w) = g(v, w)`. -/
  isometric : ∀ (x : M) (v w : TangentSpace I x),
    g'.g (ι x) (mfderiv I I ι x v) (mfderiv I I ι x w) = g.g x v w
  /-- The target is connected. -/
  connected : ConnectedSpace M'
  /-- The image is a proper subset. -/
  proper : Set.range ι ≠ Set.univ

/-- **An inextendible Lorentzian manifold**: it has no extension to a Hausdorff Lorentzian manifold (with a
smooth metric, modelled on the same space, in the universe `u`). -/
def IsInextendible {n : ℕ} (g : LorentzianMetric I M n) : Prop :=
  ∀ (M' : Type u) [TopologicalSpace M'] [T2Space M'] [ChartedSpace H M'] [IsManifold I ∞ M']
    (g' : LorentzianMetric I M' n) (ι : M → M'), ¬ IsLorentzianExtension g g' ι

end Lightlike
