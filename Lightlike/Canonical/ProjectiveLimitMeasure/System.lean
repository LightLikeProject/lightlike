import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Projective systems of spaces and their limit measures (row G2-009, CA2)

The setting of the Ashtekar–Lewandowski measure (`ashtekar-lewandowski-1995`, §3.3): a directed
family of compact spaces `X i` (the configuration spaces `G^E` of graphs), continuous bonding maps
`f : X j → X i` for `i ≤ j`, the projective limit space `Lim f`, and a family of Borel measures
`μ i` on the `X i`.  The family is *cylindrically consistent* if each `f` pushes `μ j` to `μ i`.
A *limit* is a Borel measure `ν` on `Lim f` pushing forward to each `μ i`.

This file records the easy direction: a family with a limit is consistent, so a family that is not
consistent (even in total mass) has no limit.  Mathlib has no Kolmogorov extension theorem for
compact spaces; the existence direction is in later files of this folder.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]

/-- Bonding maps `f h : X j → X i` (for `h : i ≤ j`) of a projective system: continuous, the
identity on `i ≤ i`, and compatible with composition. -/
structure IsProjSystem (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) : Prop where
  /-- each bonding map is continuous -/
  cont : ∀ i j (h : i ≤ j), Continuous (f h)
  /-- the bonding map of `i ≤ i` is the identity -/
  id : ∀ i (h : i ≤ i) x, f h x = x
  /-- bonding maps compose -/
  comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x, f hij (f hjk x) = f (hij.trans hjk) x

/-- The projective limit space: the compatible families `x i ∈ X i`. -/
def Lim (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i) : Type (max u v) :=
  {x : ∀ i, X i // ∀ i j (h : i ≤ j), f h (x j) = x i}

variable (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i)

instance : TopologicalSpace (Lim f) := instTopologicalSpaceSubtype

/-- The Borel σ-algebra on the projective limit (not the product σ-algebra). -/
instance : MeasurableSpace (Lim f) := borel (Lim f)

instance : BorelSpace (Lim f) := ⟨rfl⟩

/-- The canonical projection `Lim f → X i`. -/
def proj (i : ι) : Lim f → X i := fun x => x.1 i

lemma continuous_proj (i : ι) : Continuous (proj f i) :=
  (continuous_apply i).comp continuous_subtype_val

omit [(i : ι) → TopologicalSpace (X i)] in
lemma proj_comp {i j : ι} (h : i ≤ j) (x : Lim f) : f h (proj f j x) = proj f i x := x.2 i j h

variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]

/-- A family of measures is *cylindrically consistent* if the bonding maps push `μ j` to `μ i`. -/
def Consistent (μ : ∀ i, Measure (X i)) : Prop :=
  ∀ i j (h : i ≤ j), (μ j).map (f h) = μ i

/-- `ν` is a *projective limit* of the family `μ` if it pushes forward to each `μ i`. -/
def IsLimit (ν : Measure (Lim f)) (μ : ∀ i, Measure (X i)) : Prop :=
  ∀ i, ν.map (proj f i) = μ i

variable {f}

/-- A family of measures with a projective limit is cylindrically consistent. -/
theorem IsLimit.consistent (hf : IsProjSystem f) {ν : Measure (Lim f)} {μ : ∀ i, Measure (X i)}
    (h : IsLimit f ν μ) : Consistent f μ := by
  intro i j hij
  rw [← h j, ← h i, Measure.map_map (hf.cont i j hij).measurable
    (continuous_proj f j).measurable]
  congr 1
  funext x
  exact proj_comp f hij x

/-- A family that is not cylindrically consistent has no projective limit. -/
theorem not_exists_isLimit_of_not_consistent (hf : IsProjSystem f) {μ : ∀ i, Measure (X i)}
    (h : ¬ Consistent f μ) : ¬ ∃ ν : Measure (Lim f), IsLimit f ν μ :=
  fun ⟨_, hν⟩ => h (hν.consistent hf)

/-- A projective limit has the total mass of every member of the family. -/
theorem IsLimit.measure_univ {ν : Measure (Lim f)} {μ : ∀ i, Measure (X i)} (h : IsLimit f ν μ)
    (i : ι) : μ i Set.univ = ν Set.univ := by
  rw [← h i, Measure.map_apply (continuous_proj f i).measurable MeasurableSet.univ,
    Set.preimage_univ]

/-- Members of different total mass admit no projective limit. -/
theorem not_exists_isLimit_of_measure_univ_ne {μ : ∀ i, Measure (X i)} {i j : ι}
    (h : μ i Set.univ ≠ μ j Set.univ) : ¬ ∃ ν : Measure (Lim f), IsLimit f ν μ :=
  fun ⟨_, hν⟩ => h ((hν.measure_univ i).trans (hν.measure_univ j).symm)

end Lightlike.Rows.G2_009
