import Mathlib

/-!
# Projective limit of compact Hausdorff spaces, and limits of measure families (row G2-008)

Mathlib's `IsProjectiveLimit` is about measures on a product `∀ i, α i` and finite sets of indices.
The Ashtekar–Lewandowski measure lives on the *space* `lim G^{E(α)}` of generalised connections,
a projective limit of compact groups over a directed set of graphs. This file defines that space
for an abstract inverse system over a directed preorder, proves that it is compact Hausdorff, and
defines the projective limit of a family of measures `μ i` on the `X i` (`IsLimitMeasure`).
A family with a limit is cylindrically consistent (`IsConsistent`); a family that is not
consistent has no limit.
-/

noncomputable section

open MeasureTheory Set

universe u v

namespace Lightlike.Rows.G2_008

/-- An **inverse system** of topological spaces `X i` over a preorder `ι`: continuous bonding maps
`f : X j → X i` for `i ≤ j`, with `f` the identity for `i = i` and compatible with composition. -/
structure InvSystem (ι : Type u) [Preorder ι] (X : ι → Type v) [∀ i, TopologicalSpace (X i)] where
  /-- The bonding map `X j → X i` for `i ≤ j`. -/
  f : ∀ {i j : ι}, i ≤ j → X j → X i
  /-- The bonding maps are continuous. -/
  continuous_f : ∀ {i j : ι} (h : i ≤ j), Continuous (f h)
  /-- The bonding map of `i ≤ i` is the identity. -/
  f_self : ∀ (i : ι) (h : i ≤ i) (x : X i), f h x = x
  /-- Compatibility with composition. -/
  f_comp : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : X k),
    f hij (f hjk x) = f (hij.trans hjk) x

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

namespace InvSystem

/-- The **projective limit** of the inverse system: the compatible families `x i ∈ X i`
(a subspace of the product). -/
def Limit (_S : InvSystem ι X) : Type (max u v) :=
  {x : ∀ i, X i // ∀ (i j : ι) (h : i ≤ j), _S.f h (x j) = x i}

variable (S : InvSystem ι X)

instance : TopologicalSpace S.Limit := instTopologicalSpaceSubtype

/-- The projection `lim X → X i`. -/
def proj (i : ι) : S.Limit → X i := fun x => x.1 i

/-- The projections are continuous. -/
lemma continuous_proj (i : ι) : Continuous (S.proj i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- The projections are compatible with the bonding maps. -/
lemma f_proj {i j : ι} (h : i ≤ j) (x : S.Limit) : S.f h (S.proj j x) = S.proj i x :=
  x.2 i j h

/-- The projective limit of compact Hausdorff spaces is closed in the product. -/
lemma isClosed_limit [∀ i, T2Space (X i)] :
    IsClosed {x : ∀ i, X i | ∀ (i j : ι) (h : i ≤ j), S.f h (x j) = x i} := by
  have : {x : ∀ i, X i | ∀ (i j : ι) (h : i ≤ j), S.f h (x j) = x i} =
      ⋂ i, ⋂ j, ⋂ h : i ≤ j, {x : ∀ i, X i | S.f h (x j) = x i} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h => ?_
  exact isClosed_eq ((S.continuous_f h).comp (continuous_apply j)) (continuous_apply i)

instance [∀ i, T2Space (X i)] : T2Space S.Limit := instT2SpaceSubtype

/-- **The projective limit of compact Hausdorff spaces is compact.** -/
instance [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] : CompactSpace S.Limit :=
  isCompact_iff_compactSpace.mp (S.isClosed_limit.isCompact)

/-- The Borel σ-algebra on the limit. -/
instance : MeasurableSpace S.Limit := borel _

instance : BorelSpace S.Limit := ⟨rfl⟩

section Measures

variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]

/-- The family `μ i` is **cylindrically consistent**: the bonding maps push `μ j` to `μ i`. -/
def IsConsistent (μ : ∀ i, Measure (X i)) : Prop :=
  ∀ (i j : ι) (h : i ≤ j), (μ j).map (S.f h) = μ i

/-- `ν` is a **projective limit** of the family `μ i`: it pushes forward to `μ i` under
every projection. -/
def IsLimitMeasure (μ : ∀ i, Measure (X i)) (ν : Measure S.Limit) : Prop :=
  ∀ i, ν.map (S.proj i) = μ i

lemma measurable_f {i j : ι} (h : i ≤ j) : Measurable (S.f h) :=
  (S.continuous_f h).measurable

lemma measurable_proj (i : ι) : Measurable (S.proj i) :=
  (S.continuous_proj i).measurable

/-- A family of measures with a projective limit is cylindrically consistent. -/
theorem IsLimitMeasure.isConsistent {μ : ∀ i, Measure (X i)} {ν : Measure S.Limit}
    (hν : S.IsLimitMeasure μ ν) : S.IsConsistent μ := by
  intro i j h
  rw [← hν j, ← hν i, Measure.map_map (S.measurable_f h) (S.measurable_proj j)]
  congr 1
  funext x
  exact S.f_proj h x

/-- **A family of measures that is not cylindrically consistent has no projective limit.** -/
theorem not_exists_isLimitMeasure {μ : ∀ i, Measure (X i)} (hμ : ¬ S.IsConsistent μ) :
    ¬ ∃ ν : Measure S.Limit, S.IsLimitMeasure μ ν :=
  fun ⟨_, hν⟩ => hμ hν.isConsistent

end Measures

end InvSystem

end Lightlike.Rows.G2_008
