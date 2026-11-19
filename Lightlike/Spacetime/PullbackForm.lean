import Mathlib
import Lightlike.Spacetime.NondegMetricBase

/-!
# The pullback of a bilinear form by a smooth map is a smooth section (CO30, attempt 1)

For a smooth map `ι : M → V` into a normed space and a continuous bilinear form `L` on `V`, the pullback `p ↦ L(dι_p ·, dι_p ·)` is a
smooth section of the bundle of bilinear forms on the tangent bundle (`contMDiff_pullbackForm`). With the Euclidean inner product this is
the induced metric of a smooth immersion (`pullbackInner`); with the Minkowski form it is the induced metric of a hypersurface of
Minkowski space. This is the input for the round metric on the sphere and for the FLRW metric on `I × S³` (task CO30).

**Limits.** Smoothness only: symmetry and nondegeneracy of a given pullback are separate statements.
-/

open Manifold Bundle
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The map `D ↦ L(D ·, D ·)` from linear maps `E → V` to bilinear forms on `E` is smooth. -/
theorem contDiff_sqForm (L : V →L[ℝ] V →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun D : E →L[ℝ] V => L.bilinearComp D D) := by
  rw [contDiff_clm_apply_iff]
  intro a
  rw [contDiff_clm_apply_iff]
  intro b
  have ha : ContDiff ℝ ∞ (fun D : E →L[ℝ] V => D a) := (ContinuousLinearMap.apply ℝ V a).contDiff
  have hb : ContDiff ℝ ∞ (fun D : E →L[ℝ] V => D b) := (ContinuousLinearMap.apply ℝ V b).contDiff
  exact ((contDiff_const (c := L)).clm_apply ha).clm_apply hb

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The derivative of `ι` as a plain continuous linear map. -/
def dι (ι : M → V) (p : M) : E →L[ℝ] V := mfderiv I 𝓘(ℝ, V) ι p

/-- The pullback `L(dι_p ·, dι_p ·)` of a bilinear form `L` of `V` by `ι : M → V`. -/
def pullbackForm (L : V →L[ℝ] V →L[ℝ] ℝ) (ι : M → V) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  (L.bilinearComp (dι (I := I) ι p) (dι (I := I) ι p) : E →L[ℝ] E →L[ℝ] ℝ)

/-- The value of the pullback. -/
theorem pullbackForm_apply (L : V →L[ℝ] V →L[ℝ] ℝ) (ι : M → V) (p : M) (v w : TangentSpace I p) :
    pullbackForm (I := I) L ι p v w = L (dι (I := I) ι p v) (dι (I := I) ι p w) := rfl

/-- The pullback of a symmetric form is symmetric. -/
theorem pullbackForm_symm {L : V →L[ℝ] V →L[ℝ] ℝ} (hL : ∀ a b, L a b = L b a) (ι : M → V) (p : M) (v w : TangentSpace I p) :
    pullbackForm (I := I) L ι p v w = pullbackForm (I := I) L ι p w v := by
  rw [pullbackForm_apply, pullbackForm_apply]; exact hL _ _

/-- **The pullback of a bilinear form by a smooth map is a smooth section** of the bundle of bilinear forms of the tangent bundle. -/
theorem contMDiff_pullbackForm (L : V →L[ℝ] V →L[ℝ] ℝ) {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : M => (⟨p, pullbackForm (I := I) L ι p⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ))) := by
  intro p
  have hp : p ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) p).baseSet :=
    mem_baseSet_trivializationAt _ _ p
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun p : M => TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) p) hp]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  have hD := ContMDiffAt.mfderiv (I := I) (I' := 𝓘(ℝ, V)) (n := ∞) (m := ∞) (x₀ := p) (fun _ : M => ι) id
    (hι.contMDiffAt.comp (p, p) contMDiffAt_snd) contMDiffAt_id (by simp)
  have hS := (contDiff_sqForm (E := E) L).contMDiff.contMDiffAt.comp p hD
  refine hS.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) p).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ p),
    (trivializationAt (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) p).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ p)] with x hx1 hx2
  ext v w
  simp only [ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply,
    Trivialization.linearMapAt_apply, hx2, ite_true, hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates, Function.comp_apply, pullbackForm, dι, inTangentCoordinates]
  have hb : x ∈ (trivializationAt ℝ (fun x : M => ℝ) p).baseSet := Set.mem_univ _
  simp only [hb, ↓reduceIte]
  simp only [TangentBundle.continuousLinearMapAt_model_space, id]
  rfl

end

end Lightlike
