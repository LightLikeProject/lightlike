import Mathlib

/-!
# The Lie bracket of vector fields is the commutator of derivations

For a smooth function `g` and vector fields `X, Y` of a manifold modelled on a normed space `E`
(no boundary), `[X, Y] g = X (Y g) - Y (X g)` (`mfderiv_mlieBracket`). Mathlib defines the bracket
`VectorField.mlieBracket` through charts and proves the identity for functions on a vector space
(`fderiv_apply_lieBracket`); this file transports it through the chart `extChartAt`:

* `mfderiv_eq_chart`: the derivative of a function at a point of the chart domain is the derivative of
  its expression in the chart, composed with the derivative of the chart;
* `mpullback_chart`: the pulled back vector field in the chart is the image of the field under the
  derivative of the chart (`chartField`).

The identity is the step needed to show that the curvature `∇_X ∇_Y - ∇_Y ∇_X - ∇_{[X,Y]}` is
tensorial (`Lightlike/Spacetime/Connection.lean`).

**Limits.** Manifolds without boundary modelled on a finite-dimensional real normed space, smooth
functions; vector fields differentiable at the point.
-/

open Bundle Manifold Set VectorField NormedSpace Function
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The derivative `W g` of a function along a vector field. -/
def dirDeriv (g : M → ℝ) (W : Π y : M, TangentSpace 𝓘(ℝ, E) y) : M → ℝ :=
  fun z => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g z (W z)

/-- The vector field `W` in the chart at `x₀`, as a function `E → E`. -/
def chartField (x₀ : M) (W : Π y : M, TangentSpace 𝓘(ℝ, E) y) : E → E :=
  mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm W (range 𝓘(ℝ, E))

/-- chain rule in the chart -/
theorem mfderiv_eq_chart (g : M → ℝ) (x₀ z : M) (hz : z ∈ (extChartAt 𝓘(ℝ, E) x₀).source)
    (hg : MDiffAt g z) (v : TangentSpace 𝓘(ℝ, E) z) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g z v =
      fderiv ℝ (g ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ z)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) z v) := by
  set φ := extChartAt 𝓘(ℝ, E) x₀ with hφ
  have h1 : MDiffAt φ z := mdifferentiableAt_extChartAt (by simpa [hφ] using hz)
  have h2 : MDiffAt φ.symm (φ z) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀) (φ.map_source hz)
    simpa [hφ, mdifferentiableWithinAt_univ] using this
  have h3 : MDiffAt (g ∘ φ.symm) (φ z) := by
    refine MDifferentiableAt.comp (φ z) ?_ h2
    rw [φ.left_inv hz]; exact hg
  have heq : g =ᶠ[nhds z] (g ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x₀).mem_nhds hz] with y hy
    simp [φ.left_inv hy]
  rw [heq.mfderiv_eq, mfderiv_comp z h3 h1]
  have : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (g ∘ φ.symm) (φ z) = fderiv ℝ (g ∘ φ.symm) (φ z) := mfderiv_eq_fderiv
  rw [this]
  rfl

/-- the pulled back vector field in the chart -/
theorem mpullback_chart (Y : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x₀ z : M)
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) x₀).source) :
    mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm Y (range 𝓘(ℝ, E))
        (extChartAt 𝓘(ℝ, E) x₀ z) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) z (Y z) := by
  rw [mpullbackWithin_apply, (extChartAt 𝓘(ℝ, E) x₀).left_inv hz]
  have hA := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀)
    ((extChartAt 𝓘(ℝ, E) x₀).map_source hz)
  have := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓘(ℝ, E)) (x := x₀) hz
  exact hA.inverse_apply_eq.2
    (congrArg (fun L => L (Y z)) this).symm

/-- **The Lie bracket is the commutator of derivations**: `[X, Y] g = X (Y g) - Y (X g)` for a smooth
function `g` and vector fields `X, Y` smooth at `x₀`, on a manifold modelled on a finite-dimensional space. -/
theorem mfderiv_mlieBracket [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
    (g : M → ℝ) (X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x₀ : M)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hX : MDiffAt (T% X) x₀) (hY : MDiffAt (T% Y) x₀) :
    (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀)) =
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (dirDeriv g Y) x₀ (X x₀))
        - (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (dirDeriv g X) x₀ (Y x₀)) := by
  set φ := extChartAt 𝓘(ℝ, E) x₀ with hφ
  have hx : x₀ ∈ φ.source := mem_extChartAt_source x₀
  set Xt : E → E := mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm X (range 𝓘(ℝ, E)) with hXt
  set Yt : E → E := mpullbackWithin 𝓘(ℝ, E) 𝓘(ℝ, E) φ.symm Y (range 𝓘(ℝ, E)) with hYt
  have hbr : mlieBracket 𝓘(ℝ, E) X Y x₀ = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀).inverse (lieBracket ℝ Xt Yt (φ x₀) : E) := by
    unfold mlieBracket
    rw [mlieBracketWithin_apply]
    have hs : ((extChartAt 𝓘(ℝ, E) x₀).symm ⁻¹' (univ : Set M) ∩ range 𝓘(ℝ, E)) = (univ : Set E) := by simp
    rw [hs]
    have hLB : lieBracketWithin ℝ Xt Yt univ (φ x₀) = lieBracket ℝ Xt Yt (φ x₀) := by
      rw [lieBracketWithin_univ]
    exact congrArg (fun L : E => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x₀).inverse L) hLB
  have hgs : MDiffAt g x₀ := (hg x₀).mdifferentiableAt (by norm_num)
  have hsymm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ φ.symm (φ x₀) := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, E)) (n := ∞) x₀ (mem_extChartAt_target x₀)
    simpa [hφ, contMDiffWithinAt_univ] using this
  have hgt : ContDiffAt ℝ ∞ (g ∘ φ.symm) (φ x₀) := by
    have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (g ∘ φ.symm) (φ x₀) := by
      refine ContMDiffAt.comp (φ x₀) ?_ hsymm
      rw [hφ, (extChartAt 𝓘(ℝ, E) x₀).left_inv hx]; exact hg x₀
    exact contMDiffAt_iff_contDiffAt.1 h
  have hXd : DifferentiableAt ℝ Xt (φ x₀) := by
    have := hX.mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField (s := univ)
    exact this.differentiableAt (by simp)
  have hYd : DifferentiableAt ℝ Yt (φ x₀) := by
    have := hY.mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField (s := univ)
    exact this.differentiableAt (by simp)
  have hB : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀).IsInvertible := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) hx
  have hφd : MDiffAt φ x₀ := mdifferentiableAt_extChartAt (mem_chart_source E x₀)
  have hev : ∀ᶠ z in nhds x₀, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g z := Filter.Eventually.of_forall fun z => hg z
  -- the derivative of g along a vector field, in the chart
  have key : ∀ W : Π y : M, TangentSpace 𝓘(ℝ, E) y,
      ∀ᶠ z in nhds x₀, dirDeriv g W z =
        fderiv ℝ (g ∘ φ.symm) (φ z)
          (chartField x₀ W (φ z)) := by
    intro W
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x₀).mem_nhds hx, hev] with z hz hgz
    have h1 := mpullback_chart W x₀ z hz
    show dirDeriv g W z = _
    unfold chartField
    rw [h1]
    exact mfderiv_eq_chart g x₀ z hz (hgz.mdifferentiableAt (by norm_num)) _
  have hg1 : DifferentiableAt ℝ (fderiv ℝ (g ∘ φ.symm)) (φ x₀) :=
    (hgt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hXd' : DifferentiableAt ℝ (chartField x₀ X) (φ x₀) := hXd
  have hYd' : DifferentiableAt ℝ (chartField x₀ Y) (φ x₀) := hYd
  have hterm : ∀ (W : Π y : M, TangentSpace 𝓘(ℝ, E) y)
      (Wd : DifferentiableAt ℝ (chartField x₀ W) (φ x₀))
      (v : TangentSpace 𝓘(ℝ, E) x₀),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (dirDeriv g W) x₀ v =
        fderiv ℝ (fun y => fderiv ℝ (g ∘ φ.symm) y (chartField x₀ W y)) (φ x₀)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀ v) := by
    intro W Wd v
    have hF := hg1.clm_apply Wd
    have hmd : MDiffAt (dirDeriv g W) x₀ :=
      ((hF.mdifferentiableAt).comp x₀ hφd).congr_of_eventuallyEq (key W)
    rw [mfderiv_eq_chart _ x₀ x₀ hx hmd v]
    have hev' : (dirDeriv g W ∘ φ.symm) =ᶠ[nhds (φ x₀)] (fun y => fderiv ℝ (g ∘ φ.symm) y (chartField x₀ W y)) := by
      have ht' : Filter.Tendsto φ.symm (nhds (φ x₀)) (nhds x₀) := by
        have := hsymm.continuousAt.tendsto
        rwa [φ.left_inv hx] at this
      have hk := ht'.eventually (key W)
      have ht : ∀ᶠ y in nhds (φ x₀), y ∈ φ.target :=
        (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀).mem_nhds (mem_extChartAt_target x₀)
      filter_upwards [hk, ht] with y hy hty
      show dirDeriv g W (φ.symm y) = _
      rw [hy, φ.right_inv hty]
    erw [Filter.EventuallyEq.fderiv_eq hev']
  have hXc : Xt (φ x₀) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀ (X x₀) := mpullback_chart X x₀ x₀ hx
  have hYc : Yt (φ x₀) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ x₀ (Y x₀) := mpullback_chart Y x₀ x₀ hx
  have hLie := fderiv_apply_lieBracket (𝕜 := ℝ) (V := Xt) (W := Yt) hgt (by simp) hYd hXd
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀) =
      fderiv ℝ (g ∘ φ.symm) (φ x₀) (lieBracket ℝ Xt Yt (φ x₀)) := by
    rw [hbr, mfderiv_eq_chart g x₀ x₀ hx hgs _]
    congr 1
    exact (hB.inverse_apply_eq.1 rfl).symm
  show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀) = _ - _
  rw [hL, hLie, hterm Y hYd, hterm X hXd, hXc, hYc]
  rfl
end Lightlike
