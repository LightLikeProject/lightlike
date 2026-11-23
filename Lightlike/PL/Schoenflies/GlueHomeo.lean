import Mathlib
import Lightlike.PL.Schoenflies.Glue

/-!
# Gluing homeomorphisms of compact pieces

Two homeomorphisms `A ≃ₜ A'`, `B ≃ₜ B'` of compact planar sets that agree on `A ∩ B`, and whose
images overlap only over `A ∩ B`, glue to a homeomorphism `A ∪ B ≃ₜ A' ∪ B'`.  Together with
`region_split_chain` this is the gluing step of the bump/extension plan for the Schoenflies theorem.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- Extend a homeomorphism of subtypes to a function on the plane (arbitrary off `A`). -/
noncomputable def homeoFun {A A' : Set (ℝ × ℝ)} (e : A ≃ₜ A') (x : ℝ × ℝ) : ℝ × ℝ := by
  classical
  exact if h : x ∈ A then (e ⟨x, h⟩ : ℝ × ℝ) else x

lemma homeoFun_apply {A A' : Set (ℝ × ℝ)} (e : A ≃ₜ A') {x : ℝ × ℝ} (hx : x ∈ A) :
    homeoFun e x = (e ⟨x, hx⟩ : ℝ × ℝ) := by
  simp [homeoFun, hx]

lemma homeoFun_continuousOn {A A' : Set (ℝ × ℝ)} (e : A ≃ₜ A') : ContinuousOn (homeoFun e) A := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : A.domRestrict (homeoFun e) = fun x : A => (e x : ℝ × ℝ) := by
    funext x
    exact homeoFun_apply e x.2
  rw [this]
  exact continuous_subtype_val.comp e.continuous

lemma homeoFun_bijOn {A A' : Set (ℝ × ℝ)} (e : A ≃ₜ A') : BijOn (homeoFun e) A A' := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [homeoFun_apply e hx]
    exact (e ⟨x, hx⟩).2
  · intro x hx y hy hxy
    rw [homeoFun_apply e hx, homeoFun_apply e hy] at hxy
    have := e.injective (Subtype.ext hxy)
    simpa using congrArg Subtype.val this
  · intro y hy
    refine ⟨(e.symm ⟨y, hy⟩ : ℝ × ℝ), (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [homeoFun_apply e (e.symm ⟨y, hy⟩).2]
    simp

/-- **Gluing homeomorphisms of compact sets.**  If `e₁ : A ≃ₜ A'` and `e₂ : B ≃ₜ B'` agree on `A ∩ B`
(with `A, B` compact) and every point of `A' ∩ B'` is the `e₂`-image of a point of `A ∩ B`, there is a
homeomorphism `A ∪ B ≃ₜ A' ∪ B'` restricting to `e₁` and `e₂`. -/
theorem exists_homeo_union_glue {A B A' B' : Set (ℝ × ℝ)} (hA : IsCompact A) (hB : IsCompact B)
    (e₁ : A ≃ₜ A') (e₂ : B ≃ₜ B')
    (h : ∀ (x : ℝ × ℝ) (hxA : x ∈ A) (hxB : x ∈ B), (e₁ ⟨x, hxA⟩ : ℝ × ℝ) = e₂ ⟨x, hxB⟩)
    (hAB : ∀ y, y ∈ A' → y ∈ B' → ∃ (x : ℝ × ℝ) (_ : x ∈ A) (hxB : x ∈ B),
      (e₂ ⟨x, hxB⟩ : ℝ × ℝ) = y) :
    ∃ E : (A ∪ B : Set (ℝ × ℝ)) ≃ₜ (A' ∪ B' : Set (ℝ × ℝ)),
      (∀ (x : ℝ × ℝ) (hx : x ∈ A), (E ⟨x, Or.inl hx⟩ : ℝ × ℝ) = e₁ ⟨x, hx⟩) ∧
      (∀ (x : ℝ × ℝ) (hx : x ∈ B), (E ⟨x, Or.inr hx⟩ : ℝ × ℝ) = e₂ ⟨x, hx⟩) := by
  have hfg : EqOn (homeoFun e₁) (homeoFun e₂) (A ∩ B) := fun x hx => by
    rw [homeoFun_apply e₁ hx.1, homeoFun_apply e₂ hx.2]
    exact h x hx.1 hx.2
  obtain ⟨F, hF, hFA, hFB⟩ := exists_bijOn_union_glue (homeoFun_bijOn e₁) (homeoFun_bijOn e₂) hfg
    (by
      intro y hy
      obtain ⟨x, hxA, hxB, hx⟩ := hAB y hy.1 hy.2
      exact ⟨x, ⟨hxA, hxB⟩, by rw [homeoFun_apply e₂ hxB]; exact hx⟩)
  have hc : ContinuousOn F (A ∪ B) :=
    ((homeoFun_continuousOn e₁).congr hFA).union_of_isClosed
      ((homeoFun_continuousOn e₂).congr hFB) hA.isClosed hB.isClosed
  have hcont : Continuous (hF.mapsTo.restrict F _ _) := hc.mapsToRestrict hF.mapsTo
  have : CompactSpace (A ∪ B : Set (ℝ × ℝ)) := isCompact_iff_compactSpace.1 (hA.union hB)
  let E := hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hF.bijective)
  refine ⟨E, fun x hx => ?_, fun x hx => ?_⟩
  · have : (E ⟨x, Or.inl hx⟩ : ℝ × ℝ) = F x := rfl
    rw [this, hFA hx, homeoFun_apply e₁ hx]
  · have : (E ⟨x, Or.inr hx⟩ : ℝ × ℝ) = F x := rfl
    rw [this, hFB hx, homeoFun_apply e₂ hx]

end Lightlike.PL.Schoenflies
