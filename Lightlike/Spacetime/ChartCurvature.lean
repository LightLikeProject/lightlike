import Lightlike.Spacetime.ChartCovariant

/-!
# The curvature of a connection in a chart

For a smooth connection `cov` on a Hausdorff manifold `M` modelled on a finite-dimensional space `E` (no
boundary) and the chart at `x₀`:

* `gam`: the difference of `cov` with the connection `cov0` of the trivialization (`ChartCovariant.lean`), a
  tensor (Mathlib's `IsCovariantDerivativeOn.difference`); `gamHat` is its components, the Christoffel tensor
  `Γ̂`, which is differentiable (`mdiffAt_gamHat`);
* `hat_cov`: `(∇_u σ)^ = D σ̂ (u) + Γ̂ σ̂ û` for the components in the trivialization;
* `hv_bracket`: `[X, Y]^ = D Ŷ (X) - D X̂ (Y)`, from `mfderiv_mlieBracket` applied to the coordinate functions, and
  `deriv_comm_E`, the commutator of derivatives of an `E`-valued function;
* `curvature_hat`: the components of `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `p` are
  `Rhat = DΓ̂(a)(c, b) - DΓ̂(b)(c, a) + Γ̂(Γ̂(c, b), a) - Γ̂(Γ̂(c, a), b)`, a function of the values `a, b, c`
  of the components of `X, Y, Z` at `p` only;
* `curvatureAt_apply_proved`: hence `Connection.curvatureAt` (defined with extensions of tangent vectors) equals
  that expression for any smooth fields with the given values, so it does not depend on the extensions.

**Former task `T-GE1-P2`, closed by `curvatureAt_apply_proved`.** Differences from the task statement (approved on 18 November 2026, updated
for GE11): no boundary and a finite-dimensional model space `E` (`ModelWithCorners` `𝓘(ℝ, E)`) instead of any `ModelWithCorners` (this matches
the source, where manifolds are charts onto open subsets of `ℝⁿ`), with a locally smooth connection and no Hausdorff hypothesis (the earlier
`[T2Space M]` convention is gone); the task also assumes `[IsManifold I 2 M]`, so that is not a difference. No metric occurs, so there is no
restriction on the signature. The general statement (any `ModelWithCorners`) is the milestone GE11. The definition `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` and
its sign are those of Carroll, *Lecture Notes on General Relativity* (1997), eq. (3.71) (read at that location, where it is given as the Riemann
tensor viewed as a map of three vector fields, in the coordinate form (3.67)).

**Limits.** Manifolds without boundary modelled on a finite-dimensional space, with a locally smooth connection
(`LocallySmoothConnection`, `ChartCovariant.lean`) and no Hausdorff hypothesis. The statement of the task `T-GE1-P2` is for any
`ModelWithCorners`; this file proves the boundaryless case.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
section
variable (x₀ : M)

/-- The vector field that is the constant `a` in the trivialization at `x₀`. -/
def cfield (a : E) : Π y : M, TangentSpace 𝓘(ℝ, E) y := fun y => (tTriv (E := E) x₀).symmL ℝ y a

theorem hat_cfield (a : E) {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) : hat x₀ (cfield x₀ a) z = a := by
  unfold hat cfield
  rw [Trivialization.symmL_apply _ hz]
  have := (tTriv (E := E) x₀).apply_mk_symm hz a
  exact congrArg Prod.snd this

theorem contMDiffAt_cfield (a : E) {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cfield x₀ a q⟩ : TangentBundle 𝓘(ℝ, E) M)) z := by
  rw [(tTriv (E := E) x₀).contMDiffAt_section_iff hz]
  refine (contMDiffAt_const (c := a)).congr_of_eventuallyEq ?_
  filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hz] with q hq
  exact hat_cfield x₀ a hq
end

theorem contMDiffAt_clm_of_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : M → E →L[ℝ] F} {p : M} (h : ∀ a : E, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 (fun z => G z a) p) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] F) 1 G p := by
  set φ := extChartAt 𝓘(ℝ, E) p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 φ.symm (φ p) := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, E)) (n := 1) p (mem_extChartAt_target p)
    simpa [hφ, contMDiffWithinAt_univ] using this
  have hφd : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 φ p := contMDiffAt_extChartAt
  have h1 : ∀ a : E, ContDiffAt ℝ 1 (fun y => G (φ.symm y) a) (φ p) := fun a => by
    have := (h a).comp_of_eq hsymm (φ.left_inv hp)
    exact contMDiffAt_iff_contDiffAt.1 this
  have h2 : ContDiffAt ℝ 1 (fun y => G (φ.symm y)) (φ p) := by
    rw [← contDiffWithinAt_univ, contDiffWithinAt_clm_apply]
    exact fun a => (contDiffWithinAt_univ).2 (h1 a)
  have h3 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] F) 1 (fun y => G (φ.symm y)) (φ p) :=
    contMDiffAt_iff_contDiffAt.2 h2
  have h4 := h3.comp_of_eq hφd rfl
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) p).mem_nhds hp] with z hz
  simp [φ.left_inv hz]

variable (cov : Connection 𝓘(ℝ, E) M) (x₀ : M)

/-- The Christoffel tensor of `cov` in the chart at `x₀`: the difference with the connection of the trivialization. -/
def gam (z : M) : TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z :=
  IsCovariantDerivativeOn.difference (cov.isCovariantDerivativeOn (s := (tTriv (E := E) x₀).baseSet))
    (cov0_isCov x₀) z

theorem gam_apply {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hσ : MDiffAt (T% σ) z) : gam cov x₀ z (σ z) = cov σ z - cov0 x₀ σ z :=
  IsCovariantDerivativeOn.difference_apply (cov.isCovariantDerivativeOn (s := (tTriv (E := E) x₀).baseSet))
    (cov0_isCov x₀) hz hσ

/-- The Christoffel tensor `gam` in the components of the trivialization: `Γ̂ z (a) (b)`. -/
def gamHat (z : M) : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => ((tTriv (E := E) x₀).continuousLinearMapAt ℝ z).comp
        ((gam cov x₀ z ((tTriv (E := E) x₀).symmL ℝ z a)).comp ((tTriv (E := E) x₀).symmL ℝ z))
      map_add' := fun a b => by
        ext c; simp
      map_smul' := fun c a => by
        ext d; simp }

theorem gamHat_apply (z : M) (a b : E) :
    gamHat cov x₀ z a b = (tTriv (E := E) x₀).continuousLinearMapAt ℝ z
      (gam cov x₀ z ((tTriv (E := E) x₀).symmL ℝ z a) ((tTriv (E := E) x₀).symmL ℝ z b)) := rfl

theorem cov0_cfield (a : E) {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    cov0 x₀ (cfield x₀ a) z = 0 := by
  have heq : hat x₀ (cfield x₀ a) =ᶠ[𝓝 z] fun _ => a := by
    filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hz] with q hq
    exact hat_cfield x₀ a hq
  unfold cov0
  rw [mvfderiv_congr heq, mvfderiv_const]
  simp

theorem gamHat_eq (a b : E) {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    gamHat cov x₀ z a b = (tTriv (E := E) x₀ (⟨z, cov (cfield x₀ a) z (cfield x₀ b z)⟩ :
      TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _))).2 := by
  rw [gamHat_apply]
  have hsm : MDiffAt (T% (cfield x₀ a)) z := ((contMDiffAt_cfield x₀ a hz).mdifferentiableAt (by simp))
  have h1 := gam_apply cov x₀ hz hsm
  rw [cov0_cfield x₀ a hz] at h1
  have h2 : gam cov x₀ z ((tTriv (E := E) x₀).symmL ℝ z a) = cov (cfield x₀ a) z := by
    have := h1
    rw [sub_zero] at this
    exact this
  rw [h2, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz]
  rfl

section
variable [LocallySmoothConnection cov]

theorem contMDiffAt_gamHat_apply (a b : E) {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z => gamHat cov x₀ z a b) p := by
  have hnear : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cfield x₀ a q⟩ : TangentBundle 𝓘(ℝ, E) M)) y := by
    filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hp] with y hy
    exact contMDiffAt_cfield x₀ a hy
  have h1 := contMDiffAt_cov cov hnear
  have h2 := ContMDiffAt.clm_bundle_apply (b := id) (F₁ := E) (F₂ := E) (E₁ := TangentSpace 𝓘(ℝ, E))
    (E₂ := TangentSpace 𝓘(ℝ, E)) h1 (contMDiffAt_cfield x₀ b hp)
  have h3 := (tTriv (E := E) x₀).contMDiffAt_section_iff hp |>.1 h2
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hp] with q hq
  exact gamHat_eq cov x₀ a b hq

/-- **The Christoffel tensor `Γ̂` is differentiable** on the chart domain, for a smooth connection. -/
theorem mdiffAt_gamHat {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) (gamHat cov x₀) p := by
  have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) 1 (gamHat cov x₀) p := by
    refine contMDiffAt_clm_of_apply (G := gamHat cov x₀) fun a => ?_
    refine contMDiffAt_clm_of_apply (G := fun z => gamHat cov x₀ z a) fun b => ?_
    exact (contMDiffAt_gamHat_apply cov x₀ a b hp).of_le (by simp)
  exact h.mdifferentiableAt one_ne_zero
end

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule in the chart for a vector-valued function. -/
theorem mvfderiv_eq_chart (g : M → F) (p : M) (hg : MDiffAt g p) (u : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) g p u =
      fderiv ℝ (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p u) := by
  set φ := extChartAt 𝓘(ℝ, E) p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have h1 : MDiffAt φ p := mdifferentiableAt_extChartAt (mem_chart_source E p)
  have h2 : MDiffAt φ.symm (φ p) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := p) (φ.map_source hp)
    simpa [hφ, mdifferentiableWithinAt_univ] using this
  have h3 : MDiffAt (g ∘ φ.symm) (φ p) := by
    refine MDifferentiableAt.comp (φ p) ?_ h2
    rw [φ.left_inv hp]; exact hg
  have heq : g =ᶠ[nhds p] (g ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) p).mem_nhds hp] with y hy
    simp [φ.left_inv hy]
  have hm : mvfderiv 𝓘(ℝ, E) g p = mvfderiv 𝓘(ℝ, E) ((g ∘ φ.symm) ∘ φ) p := mvfderiv_congr heq
  rw [hm, mvfderiv_comp p h3 h1]
  simp [mvfderiv_eq_fderiv]
  rfl

theorem mdiffAt_comp_symm (g : M → F) (p : M) (hg : MDiffAt g p) :
    DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p) := by
  have hp : p ∈ (extChartAt 𝓘(ℝ, E) p).source := mem_extChartAt_source p
  have h2 : MDiffAt (extChartAt 𝓘(ℝ, E) p).symm (extChartAt 𝓘(ℝ, E) p p) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := p)
      ((extChartAt 𝓘(ℝ, E) p).map_source hp)
    simpa [mdifferentiableWithinAt_univ] using this
  have h3 : MDiffAt (g ∘ (extChartAt 𝓘(ℝ, E) p).symm) (extChartAt 𝓘(ℝ, E) p p) := by
    refine MDifferentiableAt.comp (extChartAt 𝓘(ℝ, E) p p) ?_ h2
    rw [(extChartAt 𝓘(ℝ, E) p).left_inv hp]; exact hg
  exact mdifferentiableAt_iff_differentiableAt.1 h3

theorem mvfderiv_clm_apply {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (G : M → F₁ →L[ℝ] F₂) (f : M → F₁) (p : M)
    (hG : MDiffAt G p) (hf : MDiffAt f p) (u : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) (fun x => G x (f x)) p u =
      (mvfderiv 𝓘(ℝ, E) G p u) (f p) + G p (mvfderiv 𝓘(ℝ, E) f p u) := by
  have hGf : MDiffAt (fun x => G x (f x)) p := hG.clm_apply hf
  rw [mvfderiv_eq_chart _ p hGf, mvfderiv_eq_chart G p hG, mvfderiv_eq_chart f p hf]
  have hp : p ∈ (extChartAt 𝓘(ℝ, E) p).source := mem_extChartAt_source p
  have hc := mdiffAt_comp_symm G p hG
  have hu := mdiffAt_comp_symm f p hf
  have := fderiv_clm_apply hc hu
  have h' : ((fun x => G x (f x)) ∘ (extChartAt 𝓘(ℝ, E) p).symm) =
      fun y => (G ∘ (extChartAt 𝓘(ℝ, E) p).symm) y ((f ∘ (extChartAt 𝓘(ℝ, E) p).symm) y) := rfl
  rw [h', this]
  simp [Pi.add_apply]
  exact add_comm _ _

end

section

/-- The component of a tangent vector in the trivialization at `x₀`. -/
abbrev hv (z : M) (u : TangentSpace 𝓘(ℝ, E) z) : E :=
  (tTriv (E := E) x₀ (⟨z, u⟩ : TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _))).2

/-- The components of `e⁻¹ w` are `w`. -/
theorem hv_symmL {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) (w : E) :
    hv x₀ z ((tTriv (E := E) x₀).symmL ℝ z w) = w := by
  rw [Trivialization.symmL_apply _ hz]
  exact congrArg Prod.snd ((tTriv (E := E) x₀).apply_mk_symm hz w)

/-- `e⁻¹` of the components of a tangent vector is the vector. -/
theorem symmL_hv {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) (u : TangentSpace 𝓘(ℝ, E) z) :
    (tTriv (E := E) x₀).symmL ℝ z (hv x₀ z u) = u := by
  rw [Trivialization.symmL_apply _ hz]
  exact (tTriv (E := E) x₀).symm_apply_apply_mk hz u

/-- The components are additive on the chart domain. -/
theorem hv_add {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) (u v : TangentSpace 𝓘(ℝ, E) z) :
    hv x₀ z (u + v) = hv x₀ z u + hv x₀ z v :=
  ((tTriv (E := E) x₀).linear ℝ hz).map_add _ _

/-- **A connection in the components of the trivialization**: `(∇_u σ)^ = D σ̂ (u) + Γ̂ σ̂ û`, with `Γ̂` the Christoffel tensor `gamHat` of the connection. -/
theorem hat_cov {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet)
    {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hσ : MDiffAt (T% σ) z) (u : TangentSpace 𝓘(ℝ, E) z) :
    hv x₀ z (cov σ z u) = mvfderiv 𝓘(ℝ, E) (hat x₀ σ) z u +
      gamHat cov x₀ z (hat x₀ σ z) (hv x₀ z u) := by
  have h1 := gam_apply cov x₀ hz hσ
  have h2 : cov σ z u = cov0 x₀ σ z u + gam cov x₀ z (σ z) u := by
    rw [h1]; simp
  rw [h2, hv_add x₀ hz]
  congr 1
  · unfold cov0
    exact hv_symmL x₀ hz _
  · rw [gamHat_apply, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz, symmL_hat x₀ hz, symmL_hv x₀ hz]

/-- A continuous linear map commutes with `mvfderiv`. -/
theorem mvfderiv_clm_comp {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (ℓ : F₁ →L[ℝ] F₂) (f : M → F₁) (p : M)
    (hf : MDiffAt f p) (u : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) (fun x => ℓ (f x)) p u = ℓ (mvfderiv 𝓘(ℝ, E) f p u) := by
  have := mvfderiv_clm_apply (E := E) (fun _ : M => ℓ) f p mdifferentiableAt_const hf u
  rw [this, mvfderiv_const]
  simp

/-- **The components of the Lie bracket**: `[X, Y]^ = D Ŷ (X) - D X̂ (Y)` (from `mfderiv_mlieBracket` applied to the coordinate functions). -/
theorem hv_bracket [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet)
    {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hX : MDiffAt (T% X) p) (hY : MDiffAt (T% Y) p) :
    hv x₀ p (mlieBracket 𝓘(ℝ, E) X Y p) =
      mvfderiv 𝓘(ℝ, E) (hat x₀ Y) p (X p) - mvfderiv 𝓘(ℝ, E) (hat x₀ X) p (Y p) := by
  refine (Module.finBasis ℝ E).ext_elem fun i => ?_
  set ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) with hℓ
  have hℓv : ∀ v : E, (Module.finBasis ℝ E).repr v i = ℓ v := fun v => by simp [hℓ]
  rw [hℓv, hℓv, map_sub]
  set φ := extChartAt 𝓘(ℝ, E) x₀ with hφ
  have hsrc : p ∈ φ.source := by
    rw [hφ, extChartAt_source]
    have := hp
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using this
  have hmφ : ∀ z ∈ φ.source, ∀ v : TangentSpace 𝓘(ℝ, E) z, hv x₀ z v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ z v := by
    intro z hz v
    have hz' : z ∈ (chartAt E x₀).source := by rw [hφ, extChartAt_source] at hz; exact hz
    have := TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E)) hz'
    have hzb : z ∈ (tTriv (E := E) x₀).baseSet := by
      simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz'
    have h2 : hv x₀ z v = (tTriv (E := E) x₀).continuousLinearMapAt ℝ z v := by
      rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hzb]
    rw [h2]
    exact congrArg (fun L => L v) this
  set χ : M → ℝ := fun z => ℓ (φ z) with hχ
  have hφsm : ∀ z ∈ φ.source, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ z := fun z hz => by
    have hz' : z ∈ (chartAt E x₀).source := by rw [hφ, extChartAt_source] at hz; exact hz
    exact contMDiffAt_extChartAt' hz'
  have hχsm : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ y := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x₀).mem_nhds hsrc] with y hy
    exact ℓ.contDiff.contMDiff.contMDiffAt.comp y (hφsm y hy)
  have hmχ : ∀ z ∈ φ.source, ∀ v : TangentSpace 𝓘(ℝ, E) z,
      mvfderiv 𝓘(ℝ, E) χ z v = ℓ (hv x₀ z v) := by
    intro z hz v
    have hd : MDiffAt φ z := (hφsm z hz).mdifferentiableAt (by simp)
    rw [hmφ z hz v]
    exact mvfderiv_clm_comp ℓ φ z hd v
  have hd := mfderiv_mlieBracket χ X Y p hχsm hX hY
  have hhX : MDiffAt (hat x₀ X) p := (mdiffAt_hat_iff x₀ X hp).1 hX
  have hhY : MDiffAt (hat x₀ Y) p := (mdiffAt_hat_iff x₀ Y hp).1 hY
  have hder : ∀ (W : Π y : M, TangentSpace 𝓘(ℝ, E) y) (hW : MDiffAt (hat x₀ W) p) (u : TangentSpace 𝓘(ℝ, E) p),
      mvfderiv 𝓘(ℝ, E) (dirDeriv χ W) p u = ℓ (mvfderiv 𝓘(ℝ, E) (hat x₀ W) p u) := by
    intro W hW u
    have heq : dirDeriv χ W =ᶠ[nhds p] fun z => ℓ (hat x₀ W z) := by
      filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x₀).mem_nhds hsrc] with z hz
      exact hmχ z hz (W z)
    rw [mvfderiv_congr heq]
    exact mvfderiv_clm_comp ℓ (hat x₀ W) p hW u
  calc ℓ (hv x₀ p (mlieBracket 𝓘(ℝ, E) X Y p)) = mvfderiv 𝓘(ℝ, E) χ p (mlieBracket 𝓘(ℝ, E) X Y p) :=
        (hmχ p hsrc _).symm
    _ = mvfderiv 𝓘(ℝ, E) (dirDeriv χ Y) p (X p) - mvfderiv 𝓘(ℝ, E) (dirDeriv χ X) p (Y p) := hd
    _ = _ := by rw [hder Y hhY, hder X hhX]

/-- The derivative of an `E`-valued function along `[X, Y]` is the commutator of the derivatives along `X` and `Y`. -/
theorem deriv_comm_E [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] {p : M} {f : M → E}
    (hf : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f y)
    {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hX : MDiffAt (T% X) p) (hY : MDiffAt (T% Y) p)
    (hDY : MDiffAt (fun z => mvfderiv 𝓘(ℝ, E) f z (Y z)) p)
    (hDX : MDiffAt (fun z => mvfderiv 𝓘(ℝ, E) f z (X z)) p) :
    mvfderiv 𝓘(ℝ, E) f p (mlieBracket 𝓘(ℝ, E) X Y p) =
      mvfderiv 𝓘(ℝ, E) (fun z => mvfderiv 𝓘(ℝ, E) f z (Y z)) p (X p) -
        mvfderiv 𝓘(ℝ, E) (fun z => mvfderiv 𝓘(ℝ, E) f z (X z)) p (Y p) := by
  refine (Module.finBasis ℝ E).ext_elem fun i => ?_
  set ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i) with hℓ
  have hℓv : ∀ v : E, (Module.finBasis ℝ E).repr v i = ℓ v := fun v => by simp [hℓ]
  rw [hℓv, hℓv, map_sub]
  set g : M → ℝ := fun z => ℓ (f z) with hg
  have hgsm : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g y := by
    filter_upwards [hf] with y hy
    exact ℓ.contDiff.contMDiff.contMDiffAt.comp y hy
  have hd := mfderiv_mlieBracket g X Y p hgsm hX hY
  have hfd : ∀ᶠ y in nhds p, MDiffAt f y := by
    filter_upwards [hf] with y hy using hy.mdifferentiableAt (by simp)
  have hder : ∀ (W : Π y : M, TangentSpace 𝓘(ℝ, E) y) (hW : MDiffAt (fun z => mvfderiv 𝓘(ℝ, E) f z (W z)) p)
      (u : TangentSpace 𝓘(ℝ, E) p),
      mvfderiv 𝓘(ℝ, E) (dirDeriv g W) p u = ℓ (mvfderiv 𝓘(ℝ, E) (fun z => mvfderiv 𝓘(ℝ, E) f z (W z)) p u) := by
    intro W hW u
    have heq : dirDeriv g W =ᶠ[nhds p] fun z => ℓ (mvfderiv 𝓘(ℝ, E) f z (W z)) := by
      filter_upwards [hfd] with z hz
      exact mvfderiv_clm_comp ℓ f z hz (W z)
    rw [mvfderiv_congr heq]
    exact mvfderiv_clm_comp ℓ _ p hW u
  have hfp : MDiffAt f p := hfd.self_of_nhds
  calc ℓ (mvfderiv 𝓘(ℝ, E) f p (mlieBracket 𝓘(ℝ, E) X Y p)) = mvfderiv 𝓘(ℝ, E) g p (mlieBracket 𝓘(ℝ, E) X Y p) :=
        (mvfderiv_clm_comp ℓ f p hfp _).symm
    _ = mvfderiv 𝓘(ℝ, E) (dirDeriv g Y) p (X p) - mvfderiv 𝓘(ℝ, E) (dirDeriv g X) p (Y p) := hd
    _ = _ := by rw [hder Y hDY, hder X hDX]

/-- The components are subtractive on the chart domain. -/
theorem hv_sub {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) (u v : TangentSpace 𝓘(ℝ, E) z) :
    hv x₀ z (u - v) = hv x₀ z u - hv x₀ z v := by
  have := ((tTriv (E := E) x₀).linear ℝ hz)
  have h1 := this.map_add (u - v) v
  rw [sub_add_cancel] at h1
  exact eq_sub_of_add_eq h1.symm

/-- The curvature of `cov` in the components of the trivialization: `R̂(a, b, c) = DΓ̂(a)(c, b) - DΓ̂(b)(c, a) + Γ̂(Γ̂(c, b), a) - Γ̂(Γ̂(c, a), b)`. -/
def Rhat (p : M) (a b c : E) : E :=
  (mvfderiv 𝓘(ℝ, E) (gamHat cov x₀) p ((tTriv (E := E) x₀).symmL ℝ p a)) c b
    - (mvfderiv 𝓘(ℝ, E) (gamHat cov x₀) p ((tTriv (E := E) x₀).symmL ℝ p b)) c a
    + gamHat cov x₀ p (gamHat cov x₀ p c b) a - gamHat cov x₀ p (gamHat cov x₀ p c a) b

section
variable [LocallySmoothConnection cov] [IsManifold 𝓘(ℝ, E) 2 M]
  [CompleteSpace E]

/-- `∇_Y Z` is smooth at `p` for a smooth connection and fields smooth near `p`. -/
theorem contMDiffAt_covApply {p : M}
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hY : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, E) M)) p)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, cov Z q (Y q)⟩ : TangentBundle 𝓘(ℝ, E) M)) p :=
  ContMDiffAt.clm_bundle_apply (b := id) (F₁ := E) (F₂ := E) (E₁ := TangentSpace 𝓘(ℝ, E))
    (E₂ := TangentSpace 𝓘(ℝ, E)) (contMDiffAt_cov cov hZ) hY

/-- The components of `∇_Y Z`. -/
theorem hat_covApply {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hZ : MDiffAt (T% Z) z) :
    hat x₀ (fun y => cov Z y (Y y)) z = mvfderiv 𝓘(ℝ, E) (hat x₀ Z) z (Y z) +
      gamHat cov x₀ z (hat x₀ Z z) (hat x₀ Y z) :=
  hat_cov cov x₀ hz hZ (Y z)

include cov in
/-- The derivative of the components of `Z` along `Y` is differentiable. -/
theorem mdiffAt_DY {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hY : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, E) M)) p)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => mvfderiv 𝓘(ℝ, E) (hat x₀ Z) z (Y z)) p := by
  have hW := contMDiffAt_covApply cov hY hZ
  have hWh : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ (fun y => cov Z y (Y y))) p :=
    (mdiffAt_hat_iff x₀ _ hp).1 (hW.mdifferentiableAt (by simp))
  have hZp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ Z) p :=
    (mdiffAt_hat_iff x₀ Z hp).1 ((hZ.self_of_nhds).mdifferentiableAt (by simp))
  have hYp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ Y) p :=
    (mdiffAt_hat_iff x₀ Y hp).1 (hY.mdifferentiableAt (by simp))
  have hG : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => gamHat cov x₀ z (hat x₀ Z z) (hat x₀ Y z)) p :=
    ((mdiffAt_gamHat cov x₀ hp).clm_apply hZp).clm_apply hYp
  refine (hWh.sub hG).congr_of_eventuallyEq ?_
  filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with z hz hZz
  have := hat_covApply cov x₀ hz (Y := Y) (hZz.mdifferentiableAt (by simp))
  simp only [Pi.sub_apply, this]
  abel

/-- **The curvature in a chart**: for fields smooth near `p`, the components of `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `p` are `Rhat` of the components of `X, Y, Z` at `p`, a function of the values only. -/
theorem curvature_hat {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet)
    {X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hX : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, E) M)) y)
    (hY : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, E) M)) y)
    (hZ : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    hv x₀ p (cov (fun y => cov Z y (Y y)) p (X p) - cov (fun y => cov Z y (X y)) p (Y p)
      - cov Z p (mlieBracket 𝓘(ℝ, E) X Y p)) =
      Rhat cov x₀ p (hv x₀ p (X p)) (hv x₀ p (Y p)) (hv x₀ p (Z p)) := by
  have hXp := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hmX : MDiffAt (T% X) p := hXp.mdifferentiableAt (by simp)
  have hmY : MDiffAt (T% Y) p := hYp.mdifferentiableAt (by simp)
  have hmZ : MDiffAt (T% Z) p := (hZ.self_of_nhds).mdifferentiableAt (by simp)
  have hhX : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ X) p := (mdiffAt_hat_iff x₀ X hp).1 hmX
  have hhY : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ Y) p := (mdiffAt_hat_iff x₀ Y hp).1 hmY
  have hhZ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ Z) p := (mdiffAt_hat_iff x₀ Z hp).1 hmZ
  have hDY := mdiffAt_DY cov x₀ hp hYp hZ
  have hDX := mdiffAt_DY cov x₀ hp hXp hZ
  have hWY : MDiffAt (T% (fun y => cov Z y (Y y))) p :=
    (contMDiffAt_covApply cov hYp hZ).mdifferentiableAt (by simp)
  have hWX : MDiffAt (T% (fun y => cov Z y (X y))) p :=
    (contMDiffAt_covApply cov hXp hZ).mdifferentiableAt (by simp)
  have hΓ := mdiffAt_gamHat cov x₀ hp
  have hG1 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) (fun z => gamHat cov x₀ z (hat x₀ Z z)) p :=
    hΓ.clm_apply hhZ
  -- the derivative of `Γ̂ Ẑ Ŷ`
  have hGY : ∀ (V : Π y : M, TangentSpace 𝓘(ℝ, E) y) (hV : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ V) p)
      (u : TangentSpace 𝓘(ℝ, E) p),
      mvfderiv 𝓘(ℝ, E) (fun z => gamHat cov x₀ z (hat x₀ Z z) (hat x₀ V z)) p u =
        (mvfderiv 𝓘(ℝ, E) (gamHat cov x₀) p u (hat x₀ Z p)) (hat x₀ V p) +
        (gamHat cov x₀ p (mvfderiv 𝓘(ℝ, E) (hat x₀ Z) p u)) (hat x₀ V p) +
        gamHat cov x₀ p (hat x₀ Z p) (mvfderiv 𝓘(ℝ, E) (hat x₀ V) p u) := by
    intro V hV u
    rw [mvfderiv_clm_apply _ _ p hG1 hV u, mvfderiv_clm_apply _ _ p hΓ hhZ u]
    simp
  have hGd : ∀ (V : Π y : M, TangentSpace 𝓘(ℝ, E) y) (hV : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ V) p),
      MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => gamHat cov x₀ z (hat x₀ Z z) (hat x₀ V z)) p :=
    fun V hV => hG1.clm_apply hV
  -- the components of `∇_V Z` and the first covariant derivative of it
  have hcc : ∀ (V : Π y : M, TangentSpace 𝓘(ℝ, E) y)
      (hVs : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) p)
      (u : TangentSpace 𝓘(ℝ, E) p),
      hv x₀ p (cov (fun y => cov Z y (V y)) p u) =
        (mvfderiv 𝓘(ℝ, E) (fun z => mvfderiv 𝓘(ℝ, E) (hat x₀ Z) z (V z)) p u +
          ((mvfderiv 𝓘(ℝ, E) (gamHat cov x₀) p u (hat x₀ Z p)) (hat x₀ V p) +
            (gamHat cov x₀ p (mvfderiv 𝓘(ℝ, E) (hat x₀ Z) p u)) (hat x₀ V p) +
            gamHat cov x₀ p (hat x₀ Z p) (mvfderiv 𝓘(ℝ, E) (hat x₀ V) p u))) +
        gamHat cov x₀ p (mvfderiv 𝓘(ℝ, E) (hat x₀ Z) p (V p) + gamHat cov x₀ p (hat x₀ Z p) (hat x₀ V p))
          (hv x₀ p u) := by
    intro V hVs u
    have hmV : MDiffAt (T% V) p := hVs.mdifferentiableAt (by simp)
    have hhV : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ V) p := (mdiffAt_hat_iff x₀ V hp).1 hmV
    have hDV := mdiffAt_DY cov x₀ hp hVs hZ
    have hW : MDiffAt (T% (fun y => cov Z y (V y))) p :=
      (contMDiffAt_covApply cov hVs hZ).mdifferentiableAt (by simp)
    have heq : hat x₀ (fun y => cov Z y (V y)) =ᶠ[nhds p]
        fun z => mvfderiv 𝓘(ℝ, E) (hat x₀ Z) z (V z) + gamHat cov x₀ z (hat x₀ Z z) (hat x₀ V z) := by
      filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with z hz hZz
      exact hat_covApply cov x₀ hz (hZz.mdifferentiableAt (by simp))
    rw [hat_cov cov x₀ hp hW u, mvfderiv_congr heq, mvfderiv_fun_add hDV (hGd V hhV), add_apply, hGY V hhV u,
      heq.self_of_nhds]
  have hfZ : ∀ᶠ y in nhds p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hat x₀ Z) y := by
    filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hp, hZ] with y hy hZy
    exact ((tTriv (E := E) x₀).contMDiffAt_section_iff hy).1 hZy
  have hbr := hv_bracket x₀ hp hmX hmY
  have hcomm := deriv_comm_E hfZ hmX hmY hDY hDX
  have hc3 := hat_cov cov x₀ hp hmZ (mlieBracket 𝓘(ℝ, E) X Y p)
  have hmZ' : hat x₀ Z p = hv x₀ p (Z p) := rfl
  unfold Rhat
  rw [hv_sub x₀ hp, hv_sub x₀ hp, hcc Y hYp (X p), hcc X hXp (Y p), hc3, hbr, hcomm,
    symmL_hv x₀ hp, symmL_hv x₀ hp]
  simp only [map_add, map_sub, add_apply, sub_apply]
  have e1 : hat x₀ X p = hv x₀ p (X p) := rfl
  have e2 : hat x₀ Y p = hv x₀ p (Y p) := rfl
  have e3 : hat x₀ Z p = hv x₀ p (Z p) := rfl
  simp only [e1, e2, e3]
  abel

/-- The extension of a tangent vector is smooth near the point. -/
theorem eventually_extend (v : TangentSpace 𝓘(ℝ, E) x₀) :
    ∀ᶠ y in nhds x₀, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, FiberBundle.extend E v q⟩ : TangentBundle 𝓘(ℝ, E) M)) y := by
  obtain ⟨s, hs, hsm⟩ := FiberBundle.exists_contMDiffOn_extend (I := 𝓘(ℝ, E)) (F := E) (k := ∞) v
  filter_upwards [eventually_eventually_nhds.2 hs] with y hy
  exact (hsm y hy.self_of_nhds).contMDiffAt hy

/-- **The curvature does not depend on the extension**: `curvatureAt` at `x` of the values of smooth fields is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x`, for a smooth connection on a Hausdorff manifold modelled on a finite-dimensional space without boundary. -/
theorem curvatureAt_apply_proved
    (X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hZ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x : M) :
    cov.curvatureAt x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket 𝓘(ℝ, E) X Y x) := by
  have hx : x ∈ (tTriv (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have h1 := curvature_hat cov x hx (Filter.Eventually.of_forall hX) (Filter.Eventually.of_forall hY)
    (Filter.Eventually.of_forall hZ)
  have h2 := curvature_hat cov x hx (eventually_extend x (X x)) (eventually_extend x (Y x))
    (eventually_extend x (Z x))
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  have hE := h2.trans h1.symm
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact (symmL_hv x hx _).symm.trans ((congrArg ((tTriv (E := E) x).symmL ℝ x) hE).trans (symmL_hv x hx _))
end
end

end Lightlike
