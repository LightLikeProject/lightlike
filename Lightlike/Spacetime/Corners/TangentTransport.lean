import Mathlib
import Lightlike.Spacetime.ModelTransport

/-!
# Tangent vectors and sections for a transported model

Let `I` be a model with corners on `E` and `e : E ≃L[ℝ] F`; the same manifold has the model `I' = I.transContinuousLinearEquiv e`
on `F`. Its tangent spaces are `F` instead of `E`; `e` identifies them. The change of tangent trivialisation of `I'` is the
conjugate by `e` of the one of `I` (`tangentCoordChange_transContinuousLinearEquiv`), and a section `Y` of the tangent bundle of `I`
corresponds to the section `y ↦ e (Y y)` of the one of `I'`, with the same differentiability and smoothness
(`mdifferentiableAt_transSection_iff`, `contMDiffAt_transSection_iff`). This is the first layer of the transport of the curvature
theorems to a model space that is not `Fin n → ℝ` (GE11 m4).

**Limits.** Sections and differentiability only; the Lie bracket, the covariant derivative and the curvature are transported in later files.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The change of tangent trivialisation for the transported model is the conjugate by `e`. -/
theorem tangentCoordChange_transContinuousLinearEquiv (e : E ≃L[ℝ] F) [IsManifold I 1 M] (x y z : M) (v : F) :
    tangentCoordChange (I.transContinuousLinearEquiv e) x y z v = e (tangentCoordChange I x y z (e.symm v)) := by
  rw [tangentCoordChange_def, tangentCoordChange_def]
  have hrange : range (I.transContinuousLinearEquiv e) = e.symm ⁻¹' range I := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range, e.image_eq_preimage_symm]
  have hf : (extChartAt (I.transContinuousLinearEquiv e) y ∘ (extChartAt (I.transContinuousLinearEquiv e) x).symm) =
      e ∘ ((extChartAt I y ∘ (extChartAt I x).symm) ∘ e.symm) := rfl
  have hpt : extChartAt (I.transContinuousLinearEquiv e) x z = e (extChartAt I x z) := rfl
  have hu : UniqueDiffWithinAt ℝ (e.symm ⁻¹' range I) (e (extChartAt I x z)) := by
    rw [← hrange, ← hpt]
    exact (I.transContinuousLinearEquiv e).uniqueDiffOn _ (mem_range_self _) |>.mono (le_refl _) |> fun h => h
  rw [hf, hrange, hpt, e.comp_fderivWithin hu, e.symm.comp_right_fderivWithin hu]
  simp

/-- A section of the tangent bundle of `I` as a section of the tangent bundle of the transported model: `y ↦ e (Y y)`. -/
def transSection (e : E ≃L[ℝ] F) (Y : Π y : M, TangentSpace I y) :
    Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y := fun y => e (Y y)

theorem trivializationAt_snd (b₀ b : M) (v : TangentSpace I b) [IsManifold I 1 M] :
    (trivializationAt E (TangentSpace I) b₀ (⟨b, v⟩ : TangentBundle I M)).2 = tangentCoordChange I b b₀ b v := rfl

/-- The trivialised coordinate function of a transported section is the transport of the trivialised coordinate function. -/
theorem transSection_triv (e : E ≃L[ℝ] F) [IsManifold I 1 M] (Y : Π y : M, TangentSpace I y) (b₀ b : M) :
    (trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) b₀
      (⟨b, transSection e Y b⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)).2 =
      e ((trivializationAt E (TangentSpace I) b₀ (⟨b, Y b⟩ : TangentBundle I M)).2) := by
  rw [trivializationAt_snd, trivializationAt_snd]
  change (tangentCoordChange (I.transContinuousLinearEquiv e) b b₀ b) (e (Y b)) = _
  have := tangentCoordChange_transContinuousLinearEquiv (I := I) e b b₀ b (e (Y b))
  exact this.trans (congrArg (fun z : E => e (tangentCoordChange I b b₀ b z)) (e.symm_apply_apply (Y b)))

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Differentiability of a map out of the manifold does not depend on the transported model.** -/
theorem mdifferentiableAt_transContinuousLinearEquiv_iff (e : E ≃L[ℝ] F) {f : M → N} {p : M} :
    MDifferentiableAt (I.transContinuousLinearEquiv e) J f p ↔ MDifferentiableAt I J f p := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  refine and_congr Iff.rfl ?_
  have hrange : range (I.transContinuousLinearEquiv e) = e.symm ⁻¹' range I := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range, e.image_eq_preimage_symm]
  have hf : writtenInExtChartAt (I.transContinuousLinearEquiv e) J p f =
      (writtenInExtChartAt I J p f) ∘ e.symm := rfl
  have hpt : extChartAt (I.transContinuousLinearEquiv e) p p = e (extChartAt I p p) := rfl
  rw [hf, hrange, hpt]
  have := e.symm.comp_right_differentiableWithinAt_iff (f := writtenInExtChartAt I J p f) (s := range I)
    (x := e (extChartAt I p p))
  simpa using this

theorem mdifferentiableAt_equiv_comp_iff (e : E ≃L[ℝ] F) (f : M → E) {p : M} :
    MDifferentiableAt I 𝓘(ℝ, F) (fun b => e (f b)) p ↔ MDifferentiableAt I 𝓘(ℝ, E) f p := by
  constructor
  · intro hf
    have h2 : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) (e.symm : F → E) (e (f p)) :=
      e.symm.differentiableAt.mdifferentiableAt
    exact (by simpa [Function.comp_def] using h2.comp p hf)
  · intro hf
    have h2 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) (e : E → F) (f p) :=
      e.differentiableAt.mdifferentiableAt
    exact h2.comp p hf

theorem mdifferentiableAt_transSection_iff (e : E ≃L[ℝ] F) [IsManifold I 1 M] (Y : Π y : M, TangentSpace I y) (b₀ : M) :
    MDifferentiableAt (I.transContinuousLinearEquiv e) (I.transContinuousLinearEquiv e).tangent
      (fun b => (⟨b, transSection e Y b⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)) b₀ ↔
      MDiffAt (T% Y) b₀ := by
  have h1 := mdifferentiableAt_section (IB := I.transContinuousLinearEquiv e) (F := F)
    (E := TangentSpace (I.transContinuousLinearEquiv e)) (transSection e Y) (b₀ := b₀)
  have h2 := mdifferentiableAt_section (IB := I) (F := E) (E := TangentSpace I) Y (b₀ := b₀)
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [mdifferentiableAt_transContinuousLinearEquiv_iff]
  have h : (fun b => (trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) b₀
      (⟨b, transSection e Y b⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)).2) =
      fun b => e ((trivializationAt E (TangentSpace I) b₀ (⟨b, Y b⟩ : TangentBundle I M)).2) :=
    funext fun b => transSection_triv e Y b₀ b
  rw [h]
  exact mdifferentiableAt_equiv_comp_iff e _

/-- **Smoothness of a map out of the manifold does not depend on the transported model.** -/
theorem contMDiffAt_transContinuousLinearEquiv_iff (e : E ≃L[ℝ] F) {n : WithTop ℕ∞} {f : M → N} {p : M} :
    ContMDiffAt (I.transContinuousLinearEquiv e) J n f p ↔ ContMDiffAt I J n f p := by
  rw [contMDiffAt_iff, contMDiffAt_iff]
  refine and_congr Iff.rfl ?_
  have hrange : range (I.transContinuousLinearEquiv e) = e.symm ⁻¹' range I := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range, e.image_eq_preimage_symm]
  have hf : (extChartAt J (f p) ∘ f ∘ (extChartAt (I.transContinuousLinearEquiv e) p).symm) =
      (extChartAt J (f p) ∘ f ∘ (extChartAt I p).symm) ∘ e.symm := rfl
  have hpt : extChartAt (I.transContinuousLinearEquiv e) p p = e (extChartAt I p p) := rfl
  rw [hf, hrange, hpt]
  constructor
  · intro h
    have h' := h.comp_continuousLinearMap (e : E →L[ℝ] F)
    have hpre : (e : E →L[ℝ] F) ⁻¹' (e.symm ⁻¹' range I) = range I := by
      ext x; simp
    rw [hpre] at h'
    simpa [Function.comp_def] using h'
  · intro h
    have h2 := ContDiffWithinAt.comp_continuousLinearMap (e.symm : F →L[ℝ] E)
      (x := e (extChartAt I p p)) (by simpa using h)
    exact h2

theorem contMDiffAt_equiv_comp_iff (e : E ≃L[ℝ] F) {n : WithTop ℕ∞} (f : M → E) {p : M} :
    ContMDiffAt I 𝓘(ℝ, F) n (fun b => e (f b)) p ↔ ContMDiffAt I 𝓘(ℝ, E) n f p := by
  constructor
  · intro hf
    have h2 : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) n (e.symm : F → E) (e (f p)) :=
      e.symm.contDiff.contMDiff.contMDiffAt
    exact (by simpa [Function.comp_def] using h2.comp p hf)
  · intro hf
    have h2 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n (e : E → F) (f p) :=
      e.contDiff.contMDiff.contMDiffAt
    exact h2.comp p hf

theorem contMDiffAt_transSection_iff (e : E ≃L[ℝ] F) [IsManifold I 1 M] {n : WithTop ℕ∞} (Y : Π y : M, TangentSpace I y) (b₀ : M) :
    ContMDiffAt (I.transContinuousLinearEquiv e) (I.transContinuousLinearEquiv e).tangent n
      (fun b => (⟨b, transSection e Y b⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)) b₀ ↔
      ContMDiffAt I I.tangent n (fun b => (⟨b, Y b⟩ : TangentBundle I M)) b₀ := by
  have h1 := contMDiffAt_section (IB := I.transContinuousLinearEquiv e) (F := F)
    (E := TangentSpace (I.transContinuousLinearEquiv e)) (n := n) (s := transSection e Y) b₀
  have h2 := contMDiffAt_section (IB := I) (F := E) (E := TangentSpace I) (n := n) (s := Y) b₀
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [contMDiffAt_transContinuousLinearEquiv_iff]
  have h : (fun b => (trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) b₀
      (⟨b, transSection e Y b⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)).2) =
      fun b => e ((trivializationAt E (TangentSpace I) b₀ (⟨b, Y b⟩ : TangentBundle I M)).2) :=
    funext fun b => transSection_triv e Y b₀ b
  rw [h]
  exact contMDiffAt_equiv_comp_iff e _

end Lightlike
