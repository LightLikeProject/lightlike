import Lightlike.Spacetime.SpacetimeExtension
import Lightlike.Spacetime.OpenCoordMetric

/-!
# An isometric embedding of an open subset of `ℝⁿ`, read in a chart of the target

Bridge between extensions of Lorentzian manifolds (`IsLorentzianExtension`) and chart changes of coordinate
metrics (`IsChartChange`, `pullback`). Let `U` be an open subset of `ℝⁿ` (a manifold in one chart), `ι : U → M'`
a smooth map into a manifold `M'`, and `p` a point of `M'`. In the chart of `M'` at `p` the map `ι` becomes

`ψ y = (chart at p) (ι y)` (`extChartMap`), defined on `W = {y ∈ U : ι y ∈ chart domain}` (`extChartDom`).

* `isOpen_extChartDom`, `extChartMap_mem_target`, `contDiffOn_extChartMap`: `W` is open, `ψ` maps it into the
  chart target and is smooth on it.
-/

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} (U : Opens (Fin n → ℝ))
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (Fin n → ℝ) M'] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M']
  (ι : U → M') (p : M')

open Classical in
/-- The map `ι` read in the chart of the target at `p`: `ψ y = φ_p (ι y)` for `y ∈ U` (and `0` outside `U`). -/
def extChartMap (y : Fin n → ℝ) : Fin n → ℝ :=
  if h : y ∈ U then extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι ⟨y, h⟩) else 0

/-- The domain on which `ι` takes values in the chart at `p`. -/
def extChartDom : Set (Fin n → ℝ) :=
  {y | ∃ h : y ∈ U, ι ⟨y, h⟩ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source}

lemma extChartMap_apply (x : U) : extChartMap U ι p x.1 = extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι x) := by
  unfold extChartMap
  simp [x.2]

lemma extChartDom_eq :
    extChartDom U ι p = Subtype.val '' (ι ⁻¹' (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source) := by
  ext y
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨⟨y, h⟩, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩

lemma isOpen_extChartDom (hι : Continuous ι) : IsOpen (extChartDom U ι p) := by
  rw [extChartDom_eq]
  exact U.isOpen.isOpenMap_subtype_val _ ((isOpen_extChartAt_source p).preimage hι)

lemma extChartMap_mem_target {y : Fin n → ℝ} (hy : y ∈ extChartDom U ι p) :
    extChartMap U ι p y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target := by
  obtain ⟨h, hy⟩ := hy
  rw [extChartMap_apply U ι p ⟨y, h⟩]
  exact (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_source hy

/-- `ψ` is smooth at the points of its domain. -/
lemma contDiffAt_extChartMap (hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ι) {y : Fin n → ℝ}
    (hy : y ∈ extChartDom U ι p) : ContDiffAt ℝ ∞ (extChartMap U ι p) y := by
  obtain ⟨h, hy⟩ := hy
  set x : U := ⟨y, h⟩ with hx
  have hsrc : ι x ∈ (chartAt (Fin n → ℝ) p).source := by
    rwa [← extChartAt_source 𝓘(ℝ, Fin n → ℝ)]
  -- `φ_p ∘ ι` is smooth at `x`
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun z : U => extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι z)) x :=
    (contMDiffAt_extChartAt' hsrc).comp x (hι x)
  -- precompose with the inverse chart of `U` at `x`
  have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target := by
    have := mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x
    rwa [opens_extChartAt_apply] at this
  have hsymm : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y = x := by
    have := extChartAt_to_inv (I := 𝓘(ℝ, Fin n → ℝ)) x
    rwa [opens_extChartAt_apply] at this
  have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hyt)
  have h3 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun w : Fin n → ℝ => extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm w))) y :=
    ContMDiffAt.comp (g := fun z : U => extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι z)) y (by rw [hsymm]; exact h1) h2
  rw [contMDiffAt_iff_contDiffAt] at h3
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_target x).mem_nhds hyt] with w hw
  have hw' := opens_extChartAt_symm U x hw
  rw [← extChartMap_apply U ι p ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm w), hw']

lemma contDiffOn_extChartMap (hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ι) :
    ContDiffOn ℝ ∞ (extChartMap U ι p) (extChartDom U ι p) := fun _ hy =>
  (contDiffAt_extChartMap U ι p hι hy).contDiffWithinAt

end Lightlike
