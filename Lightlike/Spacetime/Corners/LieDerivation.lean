import Mathlib

/-!
# The Lie bracket of vector fields is the commutator of derivations

For a function `g` smooth near a point and vector fields `X, Y` of a manifold modelled on a normed space `E`
(with or without boundary: any `ModelWithCorners`), `[X, Y] g = X (Y g) - Y (X g)` (`mfderiv_mlieBracketW`). Mathlib defines the bracket
`VectorField.mlieBracket` through charts and proves the identity for functions on a vector space
(`fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt`, within `range I`); this file transports it through the chart `extChartAt`:

* `mfderiv_eq_chartW`: the derivative of a function at a point of the chart domain is the derivative of
  its expression in the chart, composed with the derivative of the chart;
* `mpullback_chartW`: the pulled back vector field in the chart is the image of the field under the
  derivative of the chart (`chartFieldW`).

The identity is the step needed to show that the curvature `∇_X ∇_Y - ∇_Y ∇_X - ∇_{[X,Y]}` is
tensorial (`Lightlike/Spacetime/Connection.lean`).

**Limits.** Manifolds modelled on a finite-dimensional real normed space with corners (any `ModelWithCorners`), smooth
functions; vector fields differentiable at the point. Derivatives in a chart are taken within `range I`.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/LieDerivation.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace Function
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The derivative `W g` of a function along a vector field. -/
def dirDerivW (g : M → ℝ) (W : Π y : M, TangentSpace I y) : M → ℝ :=
  fun z => mfderiv I 𝓘(ℝ, ℝ) g z (W z)

/-- The vector field `W` in the chart at `x₀`, as a function `E → E`. -/
def chartFieldW (x₀ : M) (W : Π y : M, TangentSpace I y) : E → E :=
  mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm W (range I)

/-- **Chain rule through the chart** for a function equal to `F ∘ φ` near `x₀`, `F` differentiable within `range I`. -/
theorem mfderiv_of_eventuallyEq_chart (x₀ : M) (F : E → ℝ) (f : M → ℝ)
    (hF : DifferentiableWithinAt ℝ F (range I) (extChartAt I x₀ x₀))
    (heq : f =ᶠ[nhds x₀] F ∘ (extChartAt I x₀)) (v : TangentSpace I x₀) :
    mfderiv I 𝓘(ℝ, ℝ) f x₀ v =
      fderivWithin ℝ F (range I) (extChartAt I x₀ x₀) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ v) := by
  set φ := extChartAt I x₀ with hφ
  have h1 : MDiffAt φ x₀ := mdifferentiableAt_extChartAt (mem_chart_source H x₀)
  have h3 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (range I) (φ x₀) :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.2 hF
  have hc : mfderiv I 𝓘(ℝ, ℝ) (F ∘ φ) x₀ =
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (range I) (φ x₀)).comp (mfderiv I 𝓘(ℝ, E) φ x₀) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ]
    exact mfderivWithin_comp x₀ h3 h1.mdifferentiableWithinAt (fun z _ => ⟨_, rfl⟩) (uniqueMDiffWithinAt_univ I)
  rw [heq.mfderiv_eq, hc, mfderivWithin_eq_fderivWithin]
  rfl

/-- chain rule in the chart -/
theorem mfderiv_eq_chartW (g : M → ℝ) (x₀ z : M) (hz : z ∈ (extChartAt I x₀).source)
    (hg : MDiffAt g z) (v : TangentSpace I z) :
    mfderiv I 𝓘(ℝ, ℝ) g z v =
      fderivWithin ℝ (g ∘ (extChartAt I x₀).symm) (range I) (extChartAt I x₀ z)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z v) := by
  set φ := extChartAt I x₀ with hφ
  have h2 : MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (range I) (φ z) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x₀) (φ.map_source hz)
  have h3 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (g ∘ φ.symm) (range I) (φ z) := by
    refine MDifferentiableAt.comp_mdifferentiableWithinAt (φ z) ?_ h2
    rw [φ.left_inv hz]; exact hg
  have heq : g =ᶠ[nhds z] (g ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hz] with y hy
    simp [φ.left_inv hy]
  have h1 : MDiffAt φ z := mdifferentiableAt_extChartAt (by simpa [hφ] using hz)
  have hc : mfderiv I 𝓘(ℝ, ℝ) ((g ∘ φ.symm) ∘ φ) z =
      (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (g ∘ φ.symm) (range I) (φ z)).comp (mfderiv I 𝓘(ℝ, E) φ z) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ]
    exact mfderivWithin_comp z h3 h1.mdifferentiableWithinAt (fun w _ => ⟨_, rfl⟩) (uniqueMDiffWithinAt_univ I)
  rw [heq.mfderiv_eq, hc, mfderivWithin_eq_fderivWithin]
  rfl

/-- the pulled back vector field in the chart -/
theorem mpullback_chartW (Y : Π y : M, TangentSpace I y) (x₀ z : M)
    (hz : z ∈ (extChartAt I x₀).source) :
    mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm Y (range I)
        (extChartAt I x₀ z) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) z (Y z) := by
  rw [mpullbackWithin_apply, (extChartAt I x₀).left_inv hz]
  have hA := isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
    ((extChartAt I x₀).map_source hz)
  have := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := x₀) hz
  exact hA.inverse_apply_eq.2
    (congrArg (fun L => L (Y z)) this).symm

/-- **The Lie bracket is the commutator of derivations**: `[X, Y] g = X (Y g) - Y (X g)` for a smooth
function `g` and vector fields `X, Y` smooth at `x₀`, on a manifold modelled on a finite-dimensional space (with corners). -/
theorem mfderiv_mlieBracketW [IsManifold I 2 M] [CompleteSpace E]
    (g : M → ℝ) (X Y : Π y : M, TangentSpace I y) (x₀ : M)
    (hg : ∀ᶠ y in nhds x₀, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ g y)
    (hX : MDiffAt (T% X) x₀) (hY : MDiffAt (T% Y) x₀) :
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g x₀ (mlieBracket I X Y x₀)) =
      (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW g Y) x₀ (X x₀))
        - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW g X) x₀ (Y x₀)) := by
  set φ := extChartAt I x₀ with hφ
  have hx : x₀ ∈ φ.source := mem_extChartAt_source x₀
  have huniq : UniqueDiffOn ℝ (range I) := I.uniqueDiffOn
  have hmem : φ x₀ ∈ range I := mem_range_self _
  set Xt : E → E := mpullbackWithin 𝓘(ℝ, E) I φ.symm X (range I) with hXt
  set Yt : E → E := mpullbackWithin 𝓘(ℝ, E) I φ.symm Y (range I) with hYt
  have hbr : mlieBracket I X Y x₀ = (mfderiv I 𝓘(ℝ, E) φ x₀).inverse (lieBracketWithin ℝ Xt Yt (range I) (φ x₀) : E) := by
    unfold mlieBracket
    rw [mlieBracketWithin_apply]
    have hs : ((extChartAt I x₀).symm ⁻¹' (univ : Set M) ∩ range I) = range I := by simp
    rw [hs]
  have hgs : MDiffAt g x₀ := (hg.self_of_nhds).mdifferentiableAt (by norm_num)
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm (range I) (φ x₀) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) x₀ (mem_extChartAt_target x₀)
  have hgt : ContDiffWithinAt ℝ ∞ (g ∘ φ.symm) (range I) (φ x₀) := by
    have h : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (g ∘ φ.symm) (range I) (φ x₀) := by
      exact hg.self_of_nhds.comp_contMDiffWithinAt_of_eq hsymm (φ.left_inv hx)
    exact contMDiffWithinAt_iff_contDiffWithinAt.1 h
  have hXd : DifferentiableWithinAt ℝ Xt (range I) (φ x₀) := by
    have := hX.mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField (s := univ)
    simp only [preimage_univ, univ_inter] at this
    exact this
  have hYd : DifferentiableWithinAt ℝ Yt (range I) (φ x₀) := by
    have := hY.mdifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField (s := univ)
    simp only [preimage_univ, univ_inter] at this
    exact this
  have hB : (mfderiv I 𝓘(ℝ, E) φ x₀).IsInvertible := isInvertible_mfderiv_extChartAt (I := I) hx
  have hφd : MDiffAt φ x₀ := mdifferentiableAt_extChartAt (mem_chart_source H x₀)
  have hev : ∀ᶠ z in nhds x₀, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ g z := hg
  have key : ∀ W : Π y : M, TangentSpace I y,
      ∀ᶠ z in nhds x₀, dirDerivW g W z =
        fderivWithin ℝ (g ∘ φ.symm) (range I) (φ z) (chartFieldW x₀ W (φ z)) := by
    intro W
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds hx, hev] with z hz hgz
    have h1 := mpullback_chartW W x₀ z hz
    show dirDerivW g W z = _
    unfold chartFieldW
    rw [h1]
    exact mfderiv_eq_chartW g x₀ z hz (hgz.mdifferentiableAt (by norm_num)) _
  have hg1 : DifferentiableWithinAt ℝ (fderivWithin ℝ (g ∘ φ.symm) (range I)) (range I) (φ x₀) :=
    (hgt.fderivWithin_right (m := 1) huniq (by norm_num) hmem).differentiableWithinAt (by norm_num)
  have hterm : ∀ (W : Π y : M, TangentSpace I y)
      (Wd : DifferentiableWithinAt ℝ (chartFieldW x₀ W) (range I) (φ x₀))
      (v : TangentSpace I x₀),
      mfderiv I 𝓘(ℝ, ℝ) (dirDerivW g W) x₀ v =
        fderivWithin ℝ (fun y => fderivWithin ℝ (g ∘ φ.symm) (range I) y (chartFieldW x₀ W y)) (range I) (φ x₀)
          (mfderiv I 𝓘(ℝ, E) φ x₀ v) := by
    intro W Wd v
    have hF := hg1.clm_apply Wd
    have hev' : dirDerivW g W =ᶠ[nhds x₀]
        (fun y => fderivWithin ℝ (g ∘ φ.symm) (range I) y (chartFieldW x₀ W y)) ∘ φ := by
      filter_upwards [key W] with z hz
      simpa using hz
    exact mfderiv_of_eventuallyEq_chart x₀ _ _ hF hev' v
  have hXc : Xt (φ x₀) = mfderiv I 𝓘(ℝ, E) φ x₀ (X x₀) := mpullback_chartW X x₀ x₀ hx
  have hYc : Yt (φ x₀) = mfderiv I 𝓘(ℝ, E) φ x₀ (Y x₀) := mpullback_chartW Y x₀ x₀ hx
  have hcl : φ x₀ ∈ closure (interior (range I)) := I.range_eq_closure_interior ▸ hmem
  have hsym2 : IsSymmSndFDerivWithinAt ℝ (g ∘ φ.symm) (range I) (φ x₀) :=
    hgt.isSymmSndFDerivWithinAt (by simp [minSmoothness]) huniq hcl hmem
  have hLie := fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt (hgt.of_le (by simp)) hsym2 huniq hmem hYd hXd
  have hL : mfderiv I 𝓘(ℝ, ℝ) g x₀ (mlieBracket I X Y x₀) =
      fderivWithin ℝ (g ∘ φ.symm) (range I) (φ x₀) (lieBracketWithin ℝ Xt Yt (range I) (φ x₀)) := by
    rw [hbr, mfderiv_eq_chartW g x₀ x₀ hx hgs _]
    congr 1
    exact (hB.inverse_apply_eq.1 rfl).symm
  show mfderiv I 𝓘(ℝ, ℝ) g x₀ (mlieBracket I X Y x₀) = _ - _
  have hXd' : DifferentiableWithinAt ℝ (chartFieldW x₀ X) (range I) (φ x₀) := hXd
  have hYd' : DifferentiableWithinAt ℝ (chartFieldW x₀ Y) (range I) (φ x₀) := hYd
  rw [hL, hLie, hterm Y hYd' _, hterm X hXd' _, hXc, hYc]
  rfl

end Lightlike
