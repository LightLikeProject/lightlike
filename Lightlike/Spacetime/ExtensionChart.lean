import Lightlike.Spacetime.SpacetimeExtension
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.ChartChange

/-!
# An isometric embedding of an open subset of `ℝⁿ`, read in a chart of the target

Bridge between extensions of Lorentzian manifolds (`IsLorentzianExtension`) and chart changes of coordinate
metrics (`IsChartChange`, `pullback`). Let `U` be an open subset of `ℝⁿ` (a manifold in one chart), `ι : U → M'`
a smooth map into a manifold `M'`, and `p` a point of `M'`. In the chart of `M'` at `p` the map `ι` becomes

`ψ y = (chart at p) (ι y)` (`extChartMap`), defined on `W = {y ∈ U : ι y ∈ chart domain}` (`extChartDom`).

* `isOpen_extChartDom`, `extChartMap_mem_target`, `contDiffOn_extChartMap`: `W` is open, `ψ` maps it into the
  chart target and is smooth on it.
* `mfderiv_eq_symm_fderiv`: `dι = d(φ_p⁻¹) ∘ dψ`.
* `pullback_coordMetric_extChartMap`: if `ι` is isometric from `(U, g)` (a Lorentzian coordinate metric, as the
  manifold `openMetric U g`) into `(M', g')`, the coordinate metric of `g'` in the chart at `p` pulls back to `g`
  under `ψ`; `isChartChange_extChartMap`: `ψ` is a chart change. So chart-independent statements about coordinate
  metrics (the Ricci tensor, the Kretschmann scalar) transfer from `g` to every chart of an extension.
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

/-- **The derivative of `ι` in the chart**: `dι_x v = d(φ_p⁻¹)_{ψ x} (dψ_x v)`. -/
lemma mfderiv_eq_symm_fderiv (hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ι) (x : U)
    (hx : ι x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source) (v : Fin n → ℝ) :
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι x v : Fin n → ℝ) =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm
        (extChartMap U ι p x.1) (fderiv ℝ (extChartMap U ι p) x.1 v) : Fin n → ℝ) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hyt : x.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target := by
    have := mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x
    rwa [opens_extChartAt_apply] at this
  have hsymm : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1 = x := by
    have := extChartAt_to_inv (I := 𝓘(ℝ, Fin n → ℝ)) x
    rwa [opens_extChartAt_apply] at this
  have hsrc : ι x ∈ (chartAt (Fin n → ℝ) p).source := by
    rwa [← extChartAt_source 𝓘(ℝ, Fin n → ℝ)]
  -- differentiability of the four maps
  have dι : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1) := (hι _).mdifferentiableAt hn
  have dsx : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1 :=
    ((contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hyt)).mdifferentiableAt hn
  have dφ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p)
      (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1)) := by
    rw [hsymm]; exact mdifferentiableAt_extChartAt hsrc
  have htgt : extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι x) ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_source hx
  have dφs : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1))) := by
    rw [hsymm]
    exact ((contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds htgt)).mdifferentiableAt hn
  -- (1) `d(ι ∘ φ_x⁻¹) v = dι v`
  have h1 := mfderiv_comp_apply (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ)) (I'' := 𝓘(ℝ, Fin n → ℝ))
    (f := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) (g := ι) (x := x.1) dι dsx v
  have h1' : (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1 v :
      Fin n → ℝ) = v := by
    rw [mfderiv_extChartAt_symm_eq x hyt, opens_symmL]
    rfl
  -- (2) `d(φ_p ∘ ι ∘ φ_x⁻¹) v = dψ v`
  have dj : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) x.1 := dι.comp x.1 dsx
  have h2 := mfderiv_comp_apply (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ)) (I'' := 𝓘(ℝ, Fin n → ℝ))
    (f := ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) (g := extChartAt 𝓘(ℝ, Fin n → ℝ) p) (x := x.1) dφ dj v
  have hev : (extChartAt 𝓘(ℝ, Fin n → ℝ) p ∘ (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm)) =ᶠ[nhds x.1]
      extChartMap U ι p := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hyt] with w hw
    have hw' := opens_extChartAt_symm U x hw
    show extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm w)) = extChartMap U ι p w
    rw [← extChartMap_apply U ι p ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm w), hw']
  have h3 : (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p ∘ (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm)) x.1 v : Fin n → ℝ) =
      fderiv ℝ (extChartMap U ι p) x.1 v := by
    rw [hev.mfderiv_eq, mfderiv_eq_fderiv]
    rfl
  -- (3) `d(φ_p⁻¹) (dφ_p u) = u`
  have hev2 : ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm ∘ extChartAt 𝓘(ℝ, Fin n → ℝ) p) =ᶠ[nhds
      (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1))] id := by
    rw [hsymm]
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hx] with q hq
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hq
  have h4 : ∀ u : Fin n → ℝ,
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm
        (extChartAt 𝓘(ℝ, Fin n → ℝ) p (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1)))
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p)
          (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1)) u) : Fin n → ℝ) = u := by
    intro u
    have h5 := mfderiv_comp_apply (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))
      (I'' := 𝓘(ℝ, Fin n → ℝ)) (f := extChartAt 𝓘(ℝ, Fin n → ℝ) p)
      (g := (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm)
      (x := ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1)) dφs dφ u
    rw [← h5, hev2.mfderiv_eq, mfderiv_id]
    rfl
  -- combine
  have h6 := h4 (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) x.1 v)
  have h2' : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p ∘ (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm)) x.1 v =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p)
        (ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1))
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) x.1 v) := h2
  have h1'' : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (ι ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) x.1 v =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm x.1 v) := h1
  rw [← h2'] at h6
  rw [h1'', h1'] at h6
  rw [h3] at h6
  rw [hsymm] at h6
  rw [extChartMap_apply U ι p x]
  exact h6.symm

/-- Expansion of a bilinear form in the standard basis, after a linear map. -/
lemma bilin_sum (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (S : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (v w : Fin n → ℝ) :
    B (S v) (S w) = ∑ μ, ∑ ν, v μ * B (S (Pi.single μ 1)) (S (Pi.single ν 1)) * w ν := by
  conv_lhs => rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- **The pull-back identity.** If `ι` is isometric from `(U, g)` into `(M', g')`, then on the domain of
`ψ = φ_p ∘ ι` the coordinate metric of `g'` in the chart at `p` pulls back to `g`. -/
theorem pullback_coordMetric_extChartMap (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsLorentzianCoordMetric g U) (g' : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M' n)
    (hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ι)
    (hiso : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      g'.g (ι x) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι x v)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι x w) = (openMetric U g hg).g x v w)
    {y : Fin n → ℝ} (hy : y ∈ extChartDom U ι p) :
    pullback (g'.coordMetric p) (extChartMap U ι p) y = g y := by
  have hy0 := hy
  obtain ⟨h, hy'⟩ := hy
  have hdiff : DifferentiableAt ℝ (extChartMap U ι p) y :=
    (contDiffAt_extChartMap U ι p hι hy0).differentiableAt (by simp)
  have hjac : ∀ μ a : Fin n, jac (extChartMap U ι p) y μ a =
      fderiv ℝ (extChartMap U ι p) y (Pi.single a 1) μ := by
    intro μ a
    have h1 := (hasFDerivAt_pi'.1 hdiff.hasFDerivAt μ).fderiv
    show fderiv ℝ (fun z => extChartMap U ι p z μ) y (Pi.single a 1) = _
    rw [h1]
    rfl
  have hq : (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartMap U ι p y) = ι ⟨y, h⟩ := by
    rw [extChartMap_apply U ι p ⟨y, h⟩]
    exact (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hy'
  have hS := mfderiv_eq_symm_fderiv U ι p hι ⟨y, h⟩ hy'
  ext a b
  -- the right side, through the isometry
  have hR : g y a b = g'.g (ι ⟨y, h⟩)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι ⟨y, h⟩ (Pi.single a 1))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι ⟨y, h⟩ (Pi.single b 1)) := by
    have h1 := hiso ⟨y, h⟩ (Pi.single a 1) (Pi.single b 1)
    have h2 : (openMetric U g hg).g ⟨y, h⟩ (Pi.single a 1) (Pi.single b 1) = g y a b :=
      matForm_single (g y) a b
    exact (h1.trans h2).symm
  rw [hR, hS, hS, ← hq]
  -- the left side
  show ∑ μ, ∑ ν, jac (extChartMap U ι p) y μ a * g'.coordMetric p (extChartMap U ι p y) μ ν *
    jac (extChartMap U ι p) y ν b = _
  simp only [hjac]
  exact (bilin_sum
    (g'.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartMap U ι p y)))
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartMap U ι p y))
    (fderiv ℝ (extChartMap U ι p) y (Pi.single a 1))
    (fderiv ℝ (extChartMap U ι p) y (Pi.single b 1))).symm

/-- **An isometric embedding read in a chart of the target is a chart change** of the coordinate metrics. -/
theorem isChartChange_extChartMap (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsLorentzianCoordMetric g U) (g' : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M' n)
    (hι : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ι)
    (hiso : ∀ (x : U) (v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      g'.g (ι x) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι x v)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ι x w) = (openMetric U g hg).g x v w) :
    IsChartChange (extChartMap U ι p) (extChartDom U ι p) (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target where
  isOpen := isOpen_extChartDom U ι p hι.continuous
  mapsTo := fun _ hy => extChartMap_mem_target U ι p hy
  smooth := fun μ => by
    have h1 := contDiffOn_extChartMap U ι p hι
    exact (contDiffOn_pi.1 h1) μ
  isUnit_det := fun y hy => by
    have h1 : IsUnit (g y).det := hg.1.isUnit_det y hy.1
    rw [← pullback_coordMetric_extChartMap U ι p g hg g' hι hiso hy, pullback_eq_mul, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose] at h1
    exact isUnit_of_mul_isUnit_right h1

end Lightlike
