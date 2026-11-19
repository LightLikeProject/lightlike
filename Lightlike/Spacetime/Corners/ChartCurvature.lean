import Lightlike.Spacetime.ChartCovariant
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.ChartCurvature
import Lightlike.Spacetime.Corners.LieDerivation

/-!
# The curvature of a connection in a chart

For a smooth connection `cov` on a manifold `M` modelled with corners on a finite-dimensional space `E` and the chart at `x₀`:

* `gamW`: the difference of `cov` with the connection `cov0W` of the trivialization (`ChartCovariant.lean`), a
  tensor (Mathlib's `IsCovariantDerivativeOn.difference`); `gamHatW` is its components, the Christoffel tensor
  `Γ̂`, which is differentiable (`mdiffAt_gamHatW`);
* `hat_covW`: `(∇_u σ)^ = D σ̂ (u) + Γ̂ σ̂ û` for the components in the trivialization;
* `hv_bracketW`: `[X, Y]^ = D Ŷ (X) - D X̂ (Y)`, from `mfderiv_mlieBracketW` applied to the coordinate functions, and
  `deriv_comm_EW`, the commutator of derivatives of an `E`-valued function;
* `curvature_hatW`: the components of `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `p` are
  `RhatW = DΓ̂(a)(c, b) - DΓ̂(b)(c, a) + Γ̂(Γ̂(c, b), a) - Γ̂(Γ̂(c, a), b)`, a function of the values `a, b, c`
  of the components of `X, Y, Z` at `p` only;
* `curvatureAt_apply_proved`: hence `Connection.curvatureAt` (defined with extensions of tangent vectors) equals
  that expression for any smooth fields with the given values, so it does not depend on the extensions.

**Limits.** Manifolds modelled with corners (any `ModelWithCorners`) on a finite-dimensional space, no Hausdorff hypothesis, and a locally smooth connection
(`LocallySmoothConnectionW`). The statement of the task `T-GE1-P2` is for any `ModelWithCorners` without the Hausdorff hypothesis; this file
proves it with derivatives in the chart taken within `range I`. The coordinate files after it (`ChartAgreement`, `ChartTensor`,
`DivergenceFree`, `LeviCivitaSmooth`, `EinsteinEquations`) still treat the model without boundary.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartCurvature.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
section
variable (x₀ : M)

/-- The vector field that is the constant `a` in the trivialization at `x₀`. -/
def cfieldW (a : E) : Π y : M, TangentSpace I y := fun y => (tTrivW (I := I) (E := E) x₀).symmL ℝ y a

theorem hat_cfieldW (a : E) {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) : hatW (I := I) x₀ (cfieldW (I := I) x₀ a) z = a := by
  unfold hatW cfieldW
  rw [Trivialization.symmL_apply _ hz]
  have := (tTrivW (I := I) (E := E) x₀).apply_mk_symm hz a
  exact congrArg Prod.snd this

theorem contMDiffAt_cfieldW (a : E) {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cfieldW (I := I) x₀ a q⟩ : TangentBundle I M)) z := by
  rw [(tTrivW (I := I) (E := E) x₀).contMDiffAt_section_iff hz]
  refine (contMDiffAt_const (c := a)).congr_of_eventuallyEq ?_
  filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hz] with q hq
  exact hat_cfieldW x₀ a hq
end

theorem contMDiffAt_clm_of_applyW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : M → E →L[ℝ] F} {p : M} (h : ∀ a : E, ContMDiffAt I 𝓘(ℝ, F) 1 (fun z => G z a) p) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) 1 G p := by
  set φ := extChartAt I p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I 1 φ.symm (range I) (φ p) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (n := 1) p (mem_extChartAt_target p)
  have hφd : ContMDiffAt I 𝓘(ℝ, E) 1 φ p := contMDiffAt_extChartAt
  have hleft : φ.symm (φ p) = p := φ.left_inv hp
  have h1 : ∀ a : E, ContDiffWithinAt ℝ 1 (fun y => G (φ.symm y) a) (range I) (φ p) := fun a => by
    have := (h a).comp_contMDiffWithinAt_of_eq hsymm hleft
    exact contMDiffWithinAt_iff_contDiffWithinAt.1 this
  have h2 : ContDiffWithinAt ℝ 1 (fun y => G (φ.symm y)) (range I) (φ p) :=
    contDiffWithinAt_clm_apply.2 h1
  have h3 : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] F) 1 (fun y => G (φ.symm y)) (range I) (φ p) :=
    contMDiffWithinAt_iff_contDiffWithinAt.2 h2
  have hmaps : Set.MapsTo φ Set.univ (range I) := fun z _ => ⟨_, rfl⟩
  have h4 := h3.comp p (hφd.contMDiffWithinAt (s := Set.univ)) hmaps
  rw [contMDiffWithinAt_univ] at h4
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hp] with z hz
  simp [φ.left_inv hz]

/-- A map into continuous linear maps is smooth (all orders) if its values on every vector are. -/
theorem contMDiffAt_clm_of_apply_inftyW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : M → E →L[ℝ] F} {p : M} (h : ∀ a : E, ContMDiffAt I 𝓘(ℝ, F) ∞ (fun z => G z a) p) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ G p := by
  set φ := extChartAt I p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (range I) (φ p) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) p (mem_extChartAt_target p)
  have hφd : ContMDiffAt I 𝓘(ℝ, E) ∞ φ p := contMDiffAt_extChartAt
  have hleft : φ.symm (φ p) = p := φ.left_inv hp
  have h1 : ∀ a : E, ContDiffWithinAt ℝ ∞ (fun y => G (φ.symm y) a) (range I) (φ p) := fun a => by
    have := (h a).comp_contMDiffWithinAt_of_eq hsymm hleft
    exact contMDiffWithinAt_iff_contDiffWithinAt.1 this
  have h2 : ContDiffWithinAt ℝ ∞ (fun y => G (φ.symm y)) (range I) (φ p) :=
    contDiffWithinAt_clm_apply.2 h1
  have h3 : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] F) ∞ (fun y => G (φ.symm y)) (range I) (φ p) :=
    contMDiffWithinAt_iff_contDiffWithinAt.2 h2
  have hmaps : Set.MapsTo φ Set.univ (range I) := fun z _ => ⟨_, rfl⟩
  have h4 := h3.comp p (hφd.contMDiffWithinAt (s := Set.univ)) hmaps
  rw [contMDiffWithinAt_univ] at h4
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hp] with z hz
  simp [φ.left_inv hz]

variable (cov : Connection I M) (x₀ : M)

/-- The Christoffel tensor of `cov` in the chart at `x₀`: the difference with the connection of the trivialization. -/
def gamW (z : M) : TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z :=
  IsCovariantDerivativeOn.difference (cov.isCovariantDerivativeOn (s := (tTrivW (I := I) (E := E) x₀).baseSet))
    (cov0_isCovW x₀) z

theorem gam_applyW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) {σ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) z) : gamW cov x₀ z (σ z) = cov σ z - cov0W (I := I) x₀ σ z :=
  IsCovariantDerivativeOn.difference_apply (cov.isCovariantDerivativeOn (s := (tTrivW (I := I) (E := E) x₀).baseSet))
    (cov0_isCovW x₀) hz hσ

/-- The Christoffel tensor `gamW` in the components of the trivialization: `Γ̂ z (a) (b)`. -/
def gamHatW (z : M) : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => ((tTrivW (I := I) (E := E) x₀).continuousLinearMapAt ℝ z).comp
        ((gamW cov x₀ z ((tTrivW (I := I) (E := E) x₀).symmL ℝ z a)).comp ((tTrivW (I := I) (E := E) x₀).symmL ℝ z))
      map_add' := fun a b => by
        ext c; simp
      map_smul' := fun c a => by
        ext d; simp }

theorem gamHat_applyW (z : M) (a b : E) :
    gamHatW cov x₀ z a b = (tTrivW (I := I) (E := E) x₀).continuousLinearMapAt ℝ z
      (gamW cov x₀ z ((tTrivW (I := I) (E := E) x₀).symmL ℝ z a) ((tTrivW (I := I) (E := E) x₀).symmL ℝ z b)) := rfl

theorem cov0_cfieldW (a : E) {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    cov0W (I := I) x₀ (cfieldW (I := I) x₀ a) z = 0 := by
  have heq : hatW (I := I) x₀ (cfieldW (I := I) x₀ a) =ᶠ[𝓝 z] fun _ => a := by
    filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hz] with q hq
    exact hat_cfieldW x₀ a hq
  unfold cov0W
  rw [mvfderiv_congrW heq, mvfderiv_const]
  simp

theorem gamHat_eqW (a b : E) {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    gamHatW cov x₀ z a b = (tTrivW (I := I) (E := E) x₀ (⟨z, cov (cfieldW (I := I) x₀ a) z (cfieldW (I := I) x₀ b z)⟩ :
      TotalSpace E (TangentSpace I : M → Type _))).2 := by
  rw [gamHat_applyW]
  have hsm : MDiffAt (T% (cfieldW (I := I) x₀ a)) z := ((contMDiffAt_cfieldW x₀ a hz).mdifferentiableAt (by simp))
  have h1 := gam_applyW cov x₀ hz hsm
  rw [cov0_cfieldW x₀ a hz] at h1
  have h2 : gamW cov x₀ z ((tTrivW (I := I) (E := E) x₀).symmL ℝ z a) = cov (cfieldW (I := I) x₀ a) z := by
    have := h1
    rw [sub_zero] at this
    exact this
  rw [h2, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz]
  rfl

section
variable [LocallySmoothConnectionW cov]

theorem contMDiffAt_gamHat_applyW (a b : E) {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (fun z => gamHatW cov x₀ z a b) p := by
  have hnear : ∀ᶠ y in 𝓝 p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cfieldW (I := I) x₀ a q⟩ : TangentBundle I M)) y := by
    filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hp] with y hy
    exact contMDiffAt_cfieldW x₀ a hy
  have h1 := contMDiffAt_covW cov hnear
  have h2 := ContMDiffAt.clm_bundle_apply (b := id) (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) h1 (contMDiffAt_cfieldW x₀ b hp)
  have h3 := (tTrivW (I := I) (E := E) x₀).contMDiffAt_section_iff hp |>.1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hp] with q hq
  exact gamHat_eqW cov x₀ a b hq

/-- **The Christoffel tensor `Γ̂` is differentiable** on the chart domain, for a smooth connection. -/
theorem mdiffAt_gamHatW {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) (gamHatW cov x₀) p := by
  have h : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) 1 (gamHatW cov x₀) p := by
    refine contMDiffAt_clm_of_applyW (G := gamHatW cov x₀) fun a => ?_
    refine contMDiffAt_clm_of_applyW (G := fun z => gamHatW cov x₀ z a) fun b => ?_
    exact (contMDiffAt_gamHat_applyW cov x₀ a b hp).of_le (by simp)
  exact h.mdifferentiableAt one_ne_zero
end

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule in the chart for a vector-valued function: the derivative is the derivative within `range I` of the function
in the chart, applied to the derivative of the chart. -/
theorem mvfderiv_eq_chartW (g : M → F) (p : M) (hg : MDiffAt g p) (u : TangentSpace I p) :
    mvfderiv I g p u =
      fderivWithin ℝ (g ∘ (extChartAt I p).symm) (range I) (extChartAt I p p)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I p) p u) := by
  set φ := extChartAt I p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have h1 : MDiffAt φ p := mdifferentiableAt_extChartAt (mem_chart_source H p)
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (range I) (φ p) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p) (φ.map_source hp)
  have h3 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ φ.symm) (range I) (φ p) := by
    refine MDifferentiableAt.comp_mdifferentiableWithinAt (φ p) ?_ h2
    rw [φ.left_inv hp]; exact hg
  have heq : g =ᶠ[nhds p] (g ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hp] with y hy
    simp [φ.left_inv hy]
  have hm : mvfderiv I g p = mvfderiv I ((g ∘ φ.symm) ∘ φ) p := mvfderiv_congrW heq
  have hc : mfderiv I 𝓘(ℝ, F) ((g ∘ φ.symm) ∘ φ) p =
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ φ.symm) (range I) (φ p)).comp (mfderiv I 𝓘(ℝ, E) φ p) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ]
    exact mfderivWithin_comp p h3 h1.mdifferentiableWithinAt (fun z _ => ⟨_, rfl⟩) (uniqueMDiffWithinAt_univ I)
  rw [hm]
  have huniq : UniqueDiffWithinAt ℝ (range I) (φ p) := I.uniqueDiffOn _ (mem_range_self _)
  simp only [mvfderiv, hc, mfderivWithin_eq_fderivWithin]
  rfl

/-- Chain rule in the chart at `x₀` for a vector-valued function, at any point `p` of the chart domain. -/
theorem mvfderiv_eq_chart_at (g : M → F) (x₀ p : M) (hpx : p ∈ (extChartAt I x₀).source) (hg : MDiffAt g p)
    (u : TangentSpace I p) :
    mvfderiv I g p u =
      fderivWithin ℝ (g ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ p)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) p u) := by
  set φ := extChartAt I x₀ with hφ
  have hp : p ∈ φ.source := hpx
  have h1 : MDiffAt φ p := mdifferentiableAt_extChartAt (by simpa [hφ] using hpx)
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (range I) (φ p) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x₀) (φ.map_source hp)
  have h3 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ φ.symm) (range I) (φ p) := by
    refine MDifferentiableAt.comp_mdifferentiableWithinAt (φ p) ?_ h2
    rw [φ.left_inv hp]; exact hg
  have heq : g =ᶠ[nhds p] (g ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hp] with y hy
    simp [φ.left_inv hy]
  have hm : mvfderiv I g p = mvfderiv I ((g ∘ φ.symm) ∘ φ) p := mvfderiv_congrW heq
  have hc : mfderiv I 𝓘(ℝ, F) ((g ∘ φ.symm) ∘ φ) p =
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ φ.symm) (range I) (φ p)).comp (mfderiv I 𝓘(ℝ, E) φ p) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ]
    exact mfderivWithin_comp p h3 h1.mdifferentiableWithinAt (fun z _ => ⟨_, rfl⟩) (uniqueMDiffWithinAt_univ I)
  rw [hm]
  have huniq : UniqueDiffWithinAt ℝ (range I) (φ p) := I.uniqueDiffOn _ (mem_range_self _)
  simp only [mvfderiv, hc, mfderivWithin_eq_fderivWithin]
  rfl

theorem mdiffAt_comp_symmW (g : M → F) (p : M) (hg : MDiffAt g p) :
    DifferentiableWithinAt ℝ (g ∘ (extChartAt I p).symm) (range I) (extChartAt I p p) := by
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (extChartAt I p p) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p) ((extChartAt I p).map_source hp)
  have h3 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, F) (g ∘ (extChartAt I p).symm) (range I) (extChartAt I p p) := by
    refine MDifferentiableAt.comp_mdifferentiableWithinAt (extChartAt I p p) ?_ h2
    rw [(extChartAt I p).left_inv hp]; exact hg
  exact mdifferentiableWithinAt_iff_differentiableWithinAt.1 h3

theorem mvfderiv_clm_applyW {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (G : M → F₁ →L[ℝ] F₂) (f : M → F₁) (p : M)
    (hG : MDiffAt G p) (hf : MDiffAt f p) (u : TangentSpace I p) :
    mvfderiv I (fun x => G x (f x)) p u =
      (mvfderiv I G p u) (f p) + G p (mvfderiv I f p u) := by
  have hGf : MDiffAt (fun x => G x (f x)) p := hG.clm_apply hf
  rw [mvfderiv_eq_chartW _ p hGf, mvfderiv_eq_chartW G p hG, mvfderiv_eq_chartW f p hf]
  have hp : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hc := mdiffAt_comp_symmW G p hG
  have hu := mdiffAt_comp_symmW f p hf
  have huniq : UniqueDiffWithinAt ℝ (range I) (extChartAt I p p) := I.uniqueDiffOn _ (mem_range_self _)
  have := fderivWithin_clm_apply huniq hc hu
  have h' : ((fun x => G x (f x)) ∘ (extChartAt I p).symm) =
      fun y => (G ∘ (extChartAt I p).symm) y ((f ∘ (extChartAt I p).symm) y) := rfl
  rw [h', this]
  simp [Pi.add_apply]
  exact add_comm _ _

end

section

/-- The component of a tangent vector in the trivialization at `x₀`. -/
abbrev hvW (z : M) (u : TangentSpace I z) : E :=
  (tTrivW (I := I) (E := E) x₀ (⟨z, u⟩ : TotalSpace E (TangentSpace I : M → Type _))).2

/-- The components of `e⁻¹ w` are `w`. -/
theorem hv_symmLW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) (w : E) :
    hvW x₀ z ((tTrivW (I := I) (E := E) x₀).symmL ℝ z w) = w := by
  rw [Trivialization.symmL_apply _ hz]
  exact congrArg Prod.snd ((tTrivW (I := I) (E := E) x₀).apply_mk_symm hz w)

/-- `e⁻¹` of the components of a tangent vector is the vector. -/
theorem symmL_hvW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) (u : TangentSpace I z) :
    (tTrivW (I := I) (E := E) x₀).symmL ℝ z (hvW x₀ z u) = u := by
  rw [Trivialization.symmL_apply _ hz]
  exact (tTrivW (I := I) (E := E) x₀).symm_apply_apply_mk hz u

/-- The components are additive on the chart domain. -/
theorem hv_addW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) (u v : TangentSpace I z) :
    hvW x₀ z (u + v) = hvW x₀ z u + hvW x₀ z v :=
  ((tTrivW (I := I) (E := E) x₀).linear ℝ hz).map_add _ _

/-- **A connection in the components of the trivialization**: `(∇_u σ)^ = D σ̂ (u) + Γ̂ σ̂ û`, with `Γ̂` the Christoffel tensor `gamHatW` of the connection. -/
theorem hat_covW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    {σ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) z) (u : TangentSpace I z) :
    hvW x₀ z (cov σ z u) = mvfderiv I (hatW (I := I) x₀ σ) z u +
      gamHatW cov x₀ z (hatW (I := I) x₀ σ z) (hvW x₀ z u) := by
  have h1 := gam_applyW cov x₀ hz hσ
  have h2 : cov σ z u = cov0W (I := I) x₀ σ z u + gamW cov x₀ z (σ z) u := by
    rw [h1]; simp
  rw [h2, hv_addW x₀ hz]
  congr 1
  · unfold cov0W
    exact hv_symmLW x₀ hz _
  · rw [gamHat_applyW, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz, symmL_hatW x₀ hz, symmL_hvW x₀ hz]

/-- A continuous linear map commutes with `mvfderiv`. -/
theorem mvfderiv_clm_compW {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (ℓ : F₁ →L[ℝ] F₂) (f : M → F₁) (p : M)
    (hf : MDiffAt f p) (u : TangentSpace I p) :
    mvfderiv I (fun x => ℓ (f x)) p u = ℓ (mvfderiv I f p u) := by
  have := mvfderiv_clm_applyW (E := E) (fun _ : M => ℓ) f p mdifferentiableAt_const hf u
  rw [this, mvfderiv_const]
  simp

/-- **The components of the Lie bracket**: `[X, Y]^ = D Ŷ (X) - D X̂ (Y)` (from `mfderiv_mlieBracketW` applied to the coordinate functions). -/
theorem hv_bracketW [IsManifold I 2 M] [CompleteSpace E] {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) p) (hY : MDiffAt (T% Y) p) :
    hvW x₀ p (mlieBracket I X Y p) =
      mvfderiv I (hatW (I := I) x₀ Y) p (X p) - mvfderiv I (hatW (I := I) x₀ X) p (Y p) := by
  refine (Module.finBasis ℝ E).ext_elem fun i => ?_
  set ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) with hℓ
  have hℓv : ∀ v : E, (Module.finBasis ℝ E).repr v i = ℓ v := fun v => by simp [hℓ]
  rw [hℓv, hℓv, map_sub]
  set φ := extChartAt I x₀ with hφ
  have hsrc : p ∈ φ.source := by
    rw [hφ, extChartAt_source]
    have := hp
    simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using this
  have hmφ : ∀ z ∈ φ.source, ∀ v : TangentSpace I z, hvW x₀ z v = mfderiv I 𝓘(ℝ, E) φ z v := by
    intro z hz v
    have hz' : z ∈ (chartAt H x₀).source := by rw [hφ, extChartAt_source] at hz; exact hz
    have := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hz'
    have hzb : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet := by
      simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hz'
    have h2 : hvW x₀ z v = (tTrivW (I := I) (E := E) x₀).continuousLinearMapAt ℝ z v := by
      rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hzb]
    rw [h2]
    exact congrArg (fun L => L v) this
  set χ : M → ℝ := fun z => ℓ (φ z) with hχ
  have hφsm : ∀ z ∈ φ.source, ContMDiffAt I 𝓘(ℝ, E) ∞ φ z := fun z hz => by
    have hz' : z ∈ (chartAt H x₀).source := by rw [hφ, extChartAt_source] at hz; exact hz
    exact contMDiffAt_extChartAt' hz'
  have hχsm : ∀ᶠ y in nhds p, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ y := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hsrc] with y hy
    exact ℓ.contDiff.contMDiff.contMDiffAt.comp y (hφsm y hy)
  have hmχ : ∀ z ∈ φ.source, ∀ v : TangentSpace I z,
      mvfderiv I χ z v = ℓ (hvW x₀ z v) := by
    intro z hz v
    have hd : MDiffAt φ z := (hφsm z hz).mdifferentiableAt (by simp)
    rw [hmφ z hz v]
    exact mvfderiv_clm_compW ℓ φ z hd v
  have hd := mfderiv_mlieBracketW χ X Y p hχsm hX hY
  have hhX : MDiffAt (hatW (I := I) x₀ X) p := (mdiffAt_hat_iffW x₀ X hp).1 hX
  have hhY : MDiffAt (hatW (I := I) x₀ Y) p := (mdiffAt_hat_iffW x₀ Y hp).1 hY
  have hder : ∀ (W : Π y : M, TangentSpace I y) (hW : MDiffAt (hatW (I := I) x₀ W) p) (u : TangentSpace I p),
      mvfderiv I (dirDerivW χ W) p u = ℓ (mvfderiv I (hatW (I := I) x₀ W) p u) := by
    intro W hW u
    have heq : dirDerivW χ W =ᶠ[nhds p] fun z => ℓ (hatW (I := I) x₀ W z) := by
      filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hsrc] with z hz
      exact hmχ z hz (W z)
    rw [mvfderiv_congrW heq]
    exact mvfderiv_clm_compW ℓ (hatW (I := I) x₀ W) p hW u
  calc ℓ (hvW x₀ p (mlieBracket I X Y p)) = mvfderiv I χ p (mlieBracket I X Y p) :=
        (hmχ p hsrc _).symm
    _ = mvfderiv I (dirDerivW χ Y) p (X p) - mvfderiv I (dirDerivW χ X) p (Y p) := hd
    _ = _ := by rw [hder Y hhY, hder X hhX]

/-- The derivative of an `E`-valued function along `[X, Y]` is the commutator of the derivatives along `X` and `Y`. -/
theorem deriv_comm_EW [IsManifold I 2 M] [CompleteSpace E] {p : M} {f : M → E}
    (hf : ∀ᶠ y in nhds p, ContMDiffAt I 𝓘(ℝ, E) ∞ f y)
    {X Y : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) p) (hY : MDiffAt (T% Y) p)
    (hDY : MDiffAt (fun z => mvfderiv I f z (Y z)) p)
    (hDX : MDiffAt (fun z => mvfderiv I f z (X z)) p) :
    mvfderiv I f p (mlieBracket I X Y p) =
      mvfderiv I (fun z => mvfderiv I f z (Y z)) p (X p) -
        mvfderiv I (fun z => mvfderiv I f z (X z)) p (Y p) := by
  refine (Module.finBasis ℝ E).ext_elem fun i => ?_
  set ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) with hℓ
  have hℓv : ∀ v : E, (Module.finBasis ℝ E).repr v i = ℓ v := fun v => by simp [hℓ]
  rw [hℓv, hℓv, map_sub]
  set g : M → ℝ := fun z => ℓ (f z) with hg
  have hgsm : ∀ᶠ y in nhds p, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ g y := by
    filter_upwards [hf] with y hy
    exact ℓ.contDiff.contMDiff.contMDiffAt.comp y hy
  have hd := mfderiv_mlieBracketW g X Y p hgsm hX hY
  have hfd : ∀ᶠ y in nhds p, MDiffAt f y := by
    filter_upwards [hf] with y hy using hy.mdifferentiableAt (by simp)
  have hder : ∀ (W : Π y : M, TangentSpace I y) (hW : MDiffAt (fun z => mvfderiv I f z (W z)) p)
      (u : TangentSpace I p),
      mvfderiv I (dirDerivW g W) p u = ℓ (mvfderiv I (fun z => mvfderiv I f z (W z)) p u) := by
    intro W hW u
    have heq : dirDerivW g W =ᶠ[nhds p] fun z => ℓ (mvfderiv I f z (W z)) := by
      filter_upwards [hfd] with z hz
      exact mvfderiv_clm_compW ℓ f z hz (W z)
    rw [mvfderiv_congrW heq]
    exact mvfderiv_clm_compW ℓ _ p hW u
  have hfp : MDiffAt f p := hfd.self_of_nhds
  calc ℓ (mvfderiv I f p (mlieBracket I X Y p)) = mvfderiv I g p (mlieBracket I X Y p) :=
        (mvfderiv_clm_compW ℓ f p hfp _).symm
    _ = mvfderiv I (dirDerivW g Y) p (X p) - mvfderiv I (dirDerivW g X) p (Y p) := hd
    _ = _ := by rw [hder Y hDY, hder X hDX]

/-- The components are subtractive on the chart domain. -/
theorem hv_subW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) (u v : TangentSpace I z) :
    hvW x₀ z (u - v) = hvW x₀ z u - hvW x₀ z v := by
  have := ((tTrivW (I := I) (E := E) x₀).linear ℝ hz)
  have h1 := this.map_add (u - v) v
  rw [sub_add_cancel] at h1
  exact eq_sub_of_add_eq h1.symm

/-- The curvature of `cov` in the components of the trivialization: `R̂(a, b, c) = DΓ̂(a)(c, b) - DΓ̂(b)(c, a) + Γ̂(Γ̂(c, b), a) - Γ̂(Γ̂(c, a), b)`. -/
def RhatW (p : M) (a b c : E) : E :=
  (mvfderiv I (gamHatW cov x₀) p ((tTrivW (I := I) (E := E) x₀).symmL ℝ p a)) c b
    - (mvfderiv I (gamHatW cov x₀) p ((tTrivW (I := I) (E := E) x₀).symmL ℝ p b)) c a
    + gamHatW cov x₀ p (gamHatW cov x₀ p c b) a - gamHatW cov x₀ p (gamHatW cov x₀ p c a) b

section
variable [LocallySmoothConnectionW cov] [IsManifold I 2 M]
  [CompleteSpace E]

/-- `∇_Y Z` is smooth at `p` for a smooth connection and fields smooth near `p`. -/
theorem contMDiffAt_covApplyW {p : M}
    {Y Z : Π y : M, TangentSpace I y}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) p)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) y) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cov Z q (Y q)⟩ : TangentBundle I M)) p :=
  ContMDiffAt.clm_bundle_apply (b := id) (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (contMDiffAt_covW cov hZ) hY

/-- The components of `∇_Y Z`. -/
theorem hat_covApplyW {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    {Y Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) z) :
    hatW (I := I) x₀ (fun y => cov Z y (Y y)) z = mvfderiv I (hatW (I := I) x₀ Z) z (Y z) +
      gamHatW cov x₀ z (hatW (I := I) x₀ Z z) (hatW (I := I) x₀ Y z) :=
  hat_covW cov x₀ hz hZ (Y z)

include cov in
/-- The derivative of the components of `Z` along `Y` is differentiable. -/
theorem mdiffAt_DYW {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    {Y Z : Π y : M, TangentSpace I y}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) p)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) y) :
    MDifferentiableAt I 𝓘(ℝ, E) (fun z => mvfderiv I (hatW (I := I) x₀ Z) z (Y z)) p := by
  have hW := contMDiffAt_covApplyW cov hY hZ
  have hWh : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ (fun y => cov Z y (Y y))) p :=
    (mdiffAt_hat_iffW x₀ _ hp).1 (hW.mdifferentiableAt (by simp))
  have hZp : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ Z) p :=
    (mdiffAt_hat_iffW x₀ Z hp).1 ((hZ.self_of_nhds).mdifferentiableAt (by simp))
  have hYp : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ Y) p :=
    (mdiffAt_hat_iffW x₀ Y hp).1 (hY.mdifferentiableAt (by simp))
  have hG : MDifferentiableAt I 𝓘(ℝ, E) (fun z => gamHatW cov x₀ z (hatW (I := I) x₀ Z z) (hatW (I := I) x₀ Y z)) p :=
    ((mdiffAt_gamHatW cov x₀ hp).clm_apply hZp).clm_apply hYp
  refine (hWh.sub hG).congr_of_eventuallyEq ?_
  filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with z hz hZz
  have := hat_covApplyW cov x₀ hz (Y := Y) (hZz.mdifferentiableAt (by simp))
  simp only [Pi.sub_apply, this]
  abel

/-- **The curvature in a chart**: for fields smooth near `p`, the components of `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `p` are `RhatW` of the components of `X, Y, Z` at `p`, a function of the values only. -/
theorem curvature_hatW {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    {X Y Z : Π y : M, TangentSpace I y}
    (hX : ∀ᶠ y in nhds p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) y)
    (hY : ∀ᶠ y in nhds p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) y)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) y) :
    hvW x₀ p (cov (fun y => cov Z y (Y y)) p (X p) - cov (fun y => cov Z y (X y)) p (Y p)
      - cov Z p (mlieBracket I X Y p)) =
      RhatW cov x₀ p (hvW x₀ p (X p)) (hvW x₀ p (Y p)) (hvW x₀ p (Z p)) := by
  have hXp := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hmX : MDiffAt (T% X) p := hXp.mdifferentiableAt (by simp)
  have hmY : MDiffAt (T% Y) p := hYp.mdifferentiableAt (by simp)
  have hmZ : MDiffAt (T% Z) p := (hZ.self_of_nhds).mdifferentiableAt (by simp)
  have hhX : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ X) p := (mdiffAt_hat_iffW x₀ X hp).1 hmX
  have hhY : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ Y) p := (mdiffAt_hat_iffW x₀ Y hp).1 hmY
  have hhZ : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ Z) p := (mdiffAt_hat_iffW x₀ Z hp).1 hmZ
  have hDY := mdiffAt_DYW cov x₀ hp hYp hZ
  have hDX := mdiffAt_DYW cov x₀ hp hXp hZ
  have hWY : MDiffAt (T% (fun y => cov Z y (Y y))) p :=
    (contMDiffAt_covApplyW cov hYp hZ).mdifferentiableAt (by simp)
  have hWX : MDiffAt (T% (fun y => cov Z y (X y))) p :=
    (contMDiffAt_covApplyW cov hXp hZ).mdifferentiableAt (by simp)
  have hΓ := mdiffAt_gamHatW cov x₀ hp
  have hG1 : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E) (fun z => gamHatW cov x₀ z (hatW (I := I) x₀ Z z)) p :=
    hΓ.clm_apply hhZ
  -- the derivative of `Γ̂ Ẑ Ŷ`
  have hGY : ∀ (V : Π y : M, TangentSpace I y) (hV : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ V) p)
      (u : TangentSpace I p),
      mvfderiv I (fun z => gamHatW cov x₀ z (hatW (I := I) x₀ Z z) (hatW (I := I) x₀ V z)) p u =
        (mvfderiv I (gamHatW cov x₀) p u (hatW (I := I) x₀ Z p)) (hatW (I := I) x₀ V p) +
        (gamHatW cov x₀ p (mvfderiv I (hatW (I := I) x₀ Z) p u)) (hatW (I := I) x₀ V p) +
        gamHatW cov x₀ p (hatW (I := I) x₀ Z p) (mvfderiv I (hatW (I := I) x₀ V) p u) := by
    intro V hV u
    rw [mvfderiv_clm_applyW _ _ p hG1 hV u, mvfderiv_clm_applyW _ _ p hΓ hhZ u]
    simp
  have hGd : ∀ (V : Π y : M, TangentSpace I y) (hV : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ V) p),
      MDifferentiableAt I 𝓘(ℝ, E) (fun z => gamHatW cov x₀ z (hatW (I := I) x₀ Z z) (hatW (I := I) x₀ V z)) p :=
    fun V hV => hG1.clm_apply hV
  -- the components of `∇_V Z` and the first covariant derivative of it
  have hcc : ∀ (V : Π y : M, TangentSpace I y)
      (hVs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, V q⟩ : TangentBundle I M)) p)
      (u : TangentSpace I p),
      hvW x₀ p (cov (fun y => cov Z y (V y)) p u) =
        (mvfderiv I (fun z => mvfderiv I (hatW (I := I) x₀ Z) z (V z)) p u +
          ((mvfderiv I (gamHatW cov x₀) p u (hatW (I := I) x₀ Z p)) (hatW (I := I) x₀ V p) +
            (gamHatW cov x₀ p (mvfderiv I (hatW (I := I) x₀ Z) p u)) (hatW (I := I) x₀ V p) +
            gamHatW cov x₀ p (hatW (I := I) x₀ Z p) (mvfderiv I (hatW (I := I) x₀ V) p u))) +
        gamHatW cov x₀ p (mvfderiv I (hatW (I := I) x₀ Z) p (V p) + gamHatW cov x₀ p (hatW (I := I) x₀ Z p) (hatW (I := I) x₀ V p))
          (hvW x₀ p u) := by
    intro V hVs u
    have hmV : MDiffAt (T% V) p := hVs.mdifferentiableAt (by simp)
    have hhV : MDifferentiableAt I 𝓘(ℝ, E) (hatW (I := I) x₀ V) p := (mdiffAt_hat_iffW x₀ V hp).1 hmV
    have hDV := mdiffAt_DYW cov x₀ hp hVs hZ
    have hW : MDiffAt (T% (fun y => cov Z y (V y))) p :=
      (contMDiffAt_covApplyW cov hVs hZ).mdifferentiableAt (by simp)
    have heq : hatW (I := I) x₀ (fun y => cov Z y (V y)) =ᶠ[nhds p]
        fun z => mvfderiv I (hatW (I := I) x₀ Z) z (V z) + gamHatW cov x₀ z (hatW (I := I) x₀ Z z) (hatW (I := I) x₀ V z) := by
      filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with z hz hZz
      exact hat_covApplyW cov x₀ hz (hZz.mdifferentiableAt (by simp))
    rw [hat_covW cov x₀ hp hW u, mvfderiv_congrW heq, mvfderiv_fun_add hDV (hGd V hhV), add_apply, hGY V hhV u,
      heq.self_of_nhds]
  have hfZ : ∀ᶠ y in nhds p, ContMDiffAt I 𝓘(ℝ, E) ∞ (hatW (I := I) x₀ Z) y := by
    filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with y hy hZy
    exact ((tTrivW (I := I) (E := E) x₀).contMDiffAt_section_iff hy).1 hZy
  have hbr := hv_bracketW x₀ hp hmX hmY
  have hcomm := deriv_comm_EW hfZ hmX hmY hDY hDX
  have hc3 := hat_covW cov x₀ hp hmZ (mlieBracket I X Y p)
  have hmZ' : hatW (I := I) x₀ Z p = hvW x₀ p (Z p) := rfl
  unfold RhatW
  rw [hv_subW x₀ hp, hv_subW x₀ hp, hcc Y hYp (X p), hcc X hXp (Y p), hc3, hbr, hcomm,
    symmL_hvW x₀ hp, symmL_hvW x₀ hp]
  simp only [map_add, map_sub, add_apply, sub_apply]
  have e1 : hatW (I := I) x₀ X p = hvW x₀ p (X p) := rfl
  have e2 : hatW (I := I) x₀ Y p = hvW x₀ p (Y p) := rfl
  have e3 : hatW (I := I) x₀ Z p = hvW x₀ p (Z p) := rfl
  simp only [e1, e2, e3]
  abel

/-- The extension of a tangent vector is smooth near the point. -/
theorem eventually_extendW (v : TangentSpace I x₀) :
    ∀ᶠ y in nhds x₀, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, FiberBundle.extend E v q⟩ : TangentBundle I M)) y := by
  obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend (I := I) (F := E) (k := ∞) v
  filter_upwards [eventually_eventually_nhds.2 hs] with y hy
  exact (hsm y hy.self_of_nhds).contMDiffAt hy

end
end

end Lightlike
