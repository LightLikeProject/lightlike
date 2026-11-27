import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Corners.ChartCovariant

/-!
# Smooth vector fields through an immersion

For a smooth map `ι : M → V` into a finite-dimensional normed space whose derivative is injective at `p`, a vector
field `X` of `M` is smooth at `p` as soon as the `V`-valued function `q ↦ dι_q (X q)` is: near `p`, the components
of `X` in the trivialization at `p` are recovered from `dι X` by a smooth family of left inverses of `dι`
(`contMDiffAt_section_of_immersion`). This is how vector fields of a submanifold given by ambient formulas (the
restrictions of the linear fields of the ambient space to a quadric, for example) are proved smooth.

* `inTangentCoordinates_dι`: the derivative of `ι` in the trivialization at `p` is `dι` composed with a change of
  coordinates of the tangent bundle;
* `inTangentCoordinates_dι_hat`: applied to the components of a field in that trivialization it gives `dι X`;
* `contMDiff_linearField`: non-vacuity, a linear field of `V` (with `ι` the identity).
-/

open Bundle Manifold Set FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- **The derivative of `ι` in the trivialization at `p`** is `dι_q` composed with the change of coordinates of
the tangent bundle from the chart at `p` to the chart at `q`. -/
theorem inTangentCoordinates_dι (ι : M → V) {p q : M} (hq : q ∈ (chartAt H p).source) (w : E) :
    inTangentCoordinates I 𝓘(ℝ, V) id ι (fun y => mfderiv I 𝓘(ℝ, V) ι y) p q w =
      dι (I := I) ι q ((tangentBundleCore I M).coordChange (achart H p) (achart H q) q w) := by
  rw [inTangentCoordinates_eq _ _ _ hq (by simp), TangentBundle.coordChange_model_space]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Applied to the components `hatW p Z q` of a field in the trivialization at `p`, the derivative of `ι` in that
trivialization gives `dι_q (Z q)`. -/
theorem inTangentCoordinates_dι_hat (ι : M → V) {p q : M} (hq : q ∈ (chartAt H p).source)
    (Z : Π y : M, TangentSpace I y) :
    inTangentCoordinates I 𝓘(ℝ, V) id ι (fun y => mfderiv I 𝓘(ℝ, V) ι y) p q (hatW p Z q) =
      dι (I := I) ι q (Z q) := by
  rw [inTangentCoordinates_dι ι hq]
  congr 1
  have h1 : hatW p Z q = (tangentBundleCore I M).coordChange (achart H q) (achart H p) q (Z q) := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (𝕜 := ℝ) hq]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) p) hq (Z q)).symm
  have hqq : q ∈ (chartAt H q).source := mem_chart_source H q
  rw [h1]
  exact ((tangentBundleCore I M).coordChange_comp (achart H q) (achart H p) (achart H q) q
    ⟨⟨hqq, hq⟩, hqq⟩ (Z q)).trans ((tangentBundleCore I M).coordChange_self (achart H q) q hqq (Z q))

/-- **A vector field is smooth where its image under an immersion is.** If `ι` is smooth, `dι_p` is injective and
`q ↦ dι_q (X q)` is smooth at `p`, then the field `X` is smooth at `p`. -/
theorem contMDiffAt_section_of_immersion {ι : M → V} (hι : ContMDiff I 𝓘(ℝ, V) ∞ ι) {p : M}
    (himm : Function.Injective (dι (I := I) ι p)) {X : Π q : M, TangentSpace I q}
    (hX : ContMDiffAt I 𝓘(ℝ, V) ∞ (fun q => dι (I := I) ι q (X q)) p) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) p := by
  set D := inTangentCoordinates I 𝓘(ℝ, V) id ι (fun y => mfderiv I 𝓘(ℝ, V) ι y) p with hD
  have hDs : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] V) ∞ D p := (hι p).mfderiv_const (by simp)
  have hpp : p ∈ (chartAt H p).source := mem_chart_source H p
  have hDp : ∀ w, D p w = dι (I := I) ι p w := fun w => by
    rw [hD, inTangentCoordinates_dι ι hpp, (tangentBundleCore I M).coordChange_self (achart H p) p hpp]
  have hDinj : LinearMap.ker (D p : E →ₗ[ℝ] V) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    apply himm
    simpa [hDp] using hab
  obtain ⟨P₀, hP₀⟩ := LinearMap.exists_leftInverse_of_injective (D p : E →ₗ[ℝ] V) hDinj
  set P : V →L[ℝ] E := LinearMap.toContinuousLinearMap P₀ with hP
  have hPD : ∀ w, P (D p w) = w := fun w => by
    have := congrArg (fun f : E →ₗ[ℝ] E => f w) hP₀
    simpa [hP] using this
  set B : M → E →L[ℝ] E := fun q => P.comp (D q) with hB
  have hBs : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ B p := contMDiffAt_const.clm_comp hDs
  have hBp : B p = 1 := by
    ext w
    simp [hB, hPD]
  have hinv : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun q => Ring.inverse (B q)) p := by
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (B p) := by
      rw [hBp]
      exact contDiffAt_ringInverse ℝ (1 : (E →L[ℝ] E)ˣ)
    exact h1.comp_contMDiffAt hBs
  have hPX : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun q => P (dι (I := I) ι q (X q))) p :=
    P.contMDiff.contMDiffAt.comp p hX
  have hunit : ∀ᶠ q in 𝓝 p, IsUnit (B q) := by
    have hc : ContinuousAt B p := hBs.continuousAt
    have : {x : E →L[ℝ] E | IsUnit x} ∈ 𝓝 (B p) := by
      rw [hBp]; exact Units.isOpen.mem_nhds isUnit_one
    exact hc.preimage_mem_nhds this
  have heq : hatW p X =ᶠ[𝓝 p] fun q => Ring.inverse (B q) (P (dι (I := I) ι q (X q))) := by
    filter_upwards [hunit, (chartAt H p).open_source.mem_nhds hpp] with q hu hq
    rw [← inTangentCoordinates_dι_hat ι hq X]
    have : Ring.inverse (B q) * B q = 1 := Ring.inverse_mul_cancel _ hu
    have h2 := congrArg (fun f : E →L[ℝ] E => f (hatW p X q)) this
    simpa [hB, ← hD] using h2.symm
  have hp' : p ∈ (tTrivW (I := I) (E := E) p).baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  rw [Trivialization.contMDiffAt_section_iff (tTrivW (I := I) (E := E) p) hp']
  exact ((hinv.clm_apply hPX).congr_of_eventuallyEq heq : ContMDiffAt I 𝓘(ℝ, E) ∞ (hatW p X) p)

/-- **Non-vacuity of `contMDiffAt_section_of_immersion`**: with `ι` the identity of `V`, the linear field
`q ↦ A q` is a smooth vector field. -/
theorem contMDiff_linearField (A : V →L[ℝ] V) :
    ContMDiff 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) ∞
      (fun q : V => (⟨q, A q⟩ : TangentBundle 𝓘(ℝ, V) V)) := by
  have hd : ∀ q : V, dι (I := 𝓘(ℝ, V)) (id : V → V) q = ContinuousLinearMap.id ℝ V := fun q => mfderiv_id
  intro p
  refine contMDiffAt_section_of_immersion contMDiff_id ?_ ?_
  · rw [hd]; exact fun a b h => h
  · simp only [hd]
    exact A.contMDiff.contMDiffAt

end Lightlike
