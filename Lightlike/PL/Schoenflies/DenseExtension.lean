import Mathlib

/-!
# A bi-uniformly continuous bijection of dense subsets extends to a homeomorphism

Row G3-188, milestone PL5 (third pass).  Closing step of the limit argument for the topological Schoenflies
theorem: if the homeomorphism from the open disc onto the open Jordan region is built so that it and its
inverse are both uniformly continuous, then it extends to a homeomorphism of the compact closures.

* `exists_homeo_of_uniformEquiv_dense`: for compact metric spaces `X`, `Y`, dense subsets `A`, `B` and a bijection
  `e : A ≃ B` with `e` and `e.symm` uniformly continuous, there is a homeomorphism `X ≃ₜ Y` extending `e`.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- **Extension of a bi-uniformly continuous bijection of dense subsets.** -/
theorem exists_homeo_of_uniformEquiv_dense {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    [CompactSpace Y] {A : Set X} {B : Set Y} (hA : Dense A) (hB : Dense B) (e : A ≃ B)
    (he : UniformContinuous e) (he' : UniformContinuous e.symm) :
    ∃ h : X ≃ₜ Y, ∀ a : A, h (a : X) = (e a : Y) := by
  have iA : IsUniformInducing (Subtype.val : A → X) := isUniformEmbedding_subtype_val.isUniformInducing
  have iB : IsUniformInducing (Subtype.val : B → Y) := isUniformEmbedding_subtype_val.isUniformInducing
  have dA : DenseRange (Subtype.val : A → X) := hA.denseRange_val
  have dB : DenseRange (Subtype.val : B → Y) := hB.denseRange_val
  have hf : UniformContinuous (fun a : A => ((e a : B) : Y)) :=
    uniformContinuous_subtype_val.comp he
  have hg : UniformContinuous (fun b : B => ((e.symm b : A) : X)) :=
    uniformContinuous_subtype_val.comp he'
  set F : X → Y := (iA.isDenseInducing dA).extend (fun a : A => ((e a : B) : Y)) with hF
  set G : Y → X := (iB.isDenseInducing dB).extend (fun b : B => ((e.symm b : A) : X)) with hG
  have hFc : Continuous F := (uniformContinuous_uniformly_extend iA dA hf).continuous
  have hGc : Continuous G := (uniformContinuous_uniformly_extend iB dB hg).continuous
  have hFe : ∀ a : A, F (a : X) = (e a : Y) := fun a =>
    (iA.isDenseInducing dA).extend_eq hf.continuous a
  have hGe : ∀ b : B, G (b : Y) = (e.symm b : X) := fun b =>
    (iB.isDenseInducing dB).extend_eq hg.continuous b
  have hGF : ∀ x, G (F x) = x := by
    have : Continuous (fun x => G (F x)) := hGc.comp hFc
    have h2 : ∀ x ∈ A, G (F x) = x := by
      intro x hx
      have := hFe ⟨x, hx⟩
      simp only at this
      rw [this, hGe, Equiv.symm_apply_apply]
    exact fun x => congrFun (Continuous.ext_on hA this continuous_id h2) x
  have hFG : ∀ y, F (G y) = y := by
    have : Continuous (fun y => F (G y)) := hFc.comp hGc
    have h2 : ∀ y ∈ B, F (G y) = y := by
      intro y hy
      have := hGe ⟨y, hy⟩
      simp only at this
      rw [this, hFe, Equiv.apply_symm_apply]
    exact fun y => congrFun (Continuous.ext_on hB this continuous_id h2) y
  exact ⟨⟨⟨F, G, hGF, hFG⟩, hFc, hGc⟩, hFe⟩

/-- The subtype of a set `A` as a subset of `closure A`, as an isometric equivalence of subtypes. -/
def denseSubEquiv {Z : Type*} [MetricSpace Z] (A : Set Z) :
    {x : closure A // (x : Z) ∈ A} ≃ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun a := ⟨⟨a.1, subset_closure a.2⟩, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma denseSubEquiv_isometry {Z : Type*} [MetricSpace Z] (A : Set Z) : Isometry (denseSubEquiv A) :=
  Isometry.of_dist_eq fun _ _ => rfl

lemma denseSubEquiv_symm_isometry {Z : Type*} [MetricSpace Z] (A : Set Z) :
    Isometry (denseSubEquiv A).symm :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- **Set form.**  A bijection `e : A ≃ B` between bounded sets of the plane (or compact-closure subsets of a
proper metric space) that is uniformly continuous in both directions extends to a homeomorphism
`closure A ≃ₜ closure B`. -/
theorem exists_homeo_closure_of_uniform {Z : Type*} [MetricSpace Z] [ProperSpace Z] {A B : Set Z}
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B) (e : A ≃ B)
    (he : UniformContinuous e) (he' : UniformContinuous e.symm) :
    ∃ h : closure A ≃ₜ closure B, ∀ a : A, (h ⟨a.1, subset_closure a.2⟩ : Z) = (e a : Z) := by
  have : CompactSpace (closure A) :=
    isCompact_iff_compactSpace.1 (Metric.isCompact_of_isClosed_isBounded isClosed_closure hAb.closure)
  have : CompactSpace (closure B) :=
    isCompact_iff_compactSpace.1 (Metric.isCompact_of_isClosed_isBounded isClosed_closure hBb.closure)
  let A' : Set (closure A) := {x | (x : Z) ∈ A}
  let B' : Set (closure B) := {x | (x : Z) ∈ B}
  have hA' : Dense A' := by
    intro x
    rw [mem_closure_iff_nhds]
    intro t ht
    have hx := x.2
    rw [mem_closure_iff_nhds] at hx
    rcases mem_nhds_subtype _ _ _ |>.1 ht with ⟨u, hu, hut⟩
    obtain ⟨y, hyu, hyA⟩ := hx u hu
    exact ⟨⟨y, subset_closure hyA⟩, hut hyu, hyA⟩
  have hB' : Dense B' := by
    intro x
    rw [mem_closure_iff_nhds]
    intro t ht
    have hx := x.2
    rw [mem_closure_iff_nhds] at hx
    rcases mem_nhds_subtype _ _ _ |>.1 ht with ⟨u, hu, hut⟩
    obtain ⟨y, hyu, hyB⟩ := hx u hu
    exact ⟨⟨y, subset_closure hyB⟩, hut hyu, hyB⟩
  let e' : A' ≃ B' := ((denseSubEquiv A).trans e).trans (denseSubEquiv B).symm
  have h1 : UniformContinuous e' :=
    (denseSubEquiv_symm_isometry B).uniformContinuous.comp
      (he.comp (denseSubEquiv_isometry A).uniformContinuous)
  have h2 : UniformContinuous e'.symm :=
    (denseSubEquiv_symm_isometry A).uniformContinuous.comp
      (he'.comp (denseSubEquiv_isometry B).uniformContinuous)
  obtain ⟨h, hh⟩ := exists_homeo_of_uniformEquiv_dense hA' hB' e' h1 h2
  refine ⟨h, fun a => ?_⟩
  have := hh ⟨⟨a.1, subset_closure a.2⟩, a.2⟩
  have h3 : h ⟨a.1, subset_closure a.2⟩ = ⟨(e a : Z), subset_closure (e a).2⟩ := by
    simpa [e', denseSubEquiv] using this
  exact congrArg Subtype.val h3

end Lightlike.PL.Schoenflies
