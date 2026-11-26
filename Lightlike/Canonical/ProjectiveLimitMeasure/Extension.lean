import Lightlike.Canonical.ProjectiveLimitMeasure.Functional
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The linear functional on cylinder functions (row G2-009, CA2)

For a consistent family `μ` of finite Borel measures on a directed system of nonempty compact
Hausdorff spaces with surjective bonding maps, `cylInt` is the value `∫ g dμ i` of a cylinder
function `g ∘ proj i`.  It is a bounded linear functional (`cylFunctional`) on the subalgebra of
cylinder functions, with `|Λ φ| ≤ M ‖φ‖` where `M` is the common total mass of the `μ i`.
This is the step that precedes the extension to `C(Lim f, ℝ)` and the Riesz–Markov theorem
(`ashtekar-lewandowski-1995`, §3.3).
-/

open MeasureTheory

namespace Lightlike.Canonical.ProjectiveLimitMeasure

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  [IsDirected ι (· ≤ ·)] [Nonempty ι] [∀ i, CompactSpace (X i)]
  [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]

/-- A continuous function on a compact space is integrable for a finite measure. -/
lemma integrable_of_continuous {Y : Type v} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν] (g : C(Y, ℝ)) : Integrable g ν :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- The integral of a cylinder function, computed in a chosen representation. -/
noncomputable def cylInt (μ : ∀ i, Measure (X i)) (hf : IsProjSystem f)
    (φ : cylAlgebra f hf) : ℝ :=
  ∫ y, (Classical.choose (Classical.choose_spec φ.2)) y ∂μ (Classical.choose φ.2)

variable {μ : ∀ i, Measure (X i)}

/-- `cylInt` is computed by any representation. -/
lemma cylInt_eq (hf : IsProjSystem f) (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h))
    (hμ : Consistent f μ) (φ : cylAlgebra f hf) {i : ι} {g : C(X i, ℝ)}
    (h : φ.1 = cyl f i g) : cylInt μ hf φ = ∫ y, g y ∂μ i :=
  integral_eq_of_cyl_eq hf hs hμ
    ((Classical.choose_spec (Classical.choose_spec φ.2)).symm.trans h)

omit [Nonempty ι] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] in
/-- All members of a consistent family have the same total mass. -/
lemma Consistent.measure_univ_eq (hf : IsProjSystem f) (hμ : Consistent f μ) (i j : ι) :
    μ i Set.univ = μ j Set.univ := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h1 : μ i Set.univ = μ k Set.univ := by
    rw [← hμ i k hik, Measure.map_apply (hf.cont i k hik).measurable MeasurableSet.univ,
      Set.preimage_univ]
  have h2 : μ j Set.univ = μ k Set.univ := by
    rw [← hμ j k hjk, Measure.map_apply (hf.cont j k hjk).measurable MeasurableSet.univ,
      Set.preimage_univ]
  rw [h1, h2]

omit [∀ i, BorelSpace (X i)] [∀ i, MeasurableSpace (X i)] in
/-- The sup norm of a cylinder function dominates the sup norm of its profile. -/
lemma norm_le_norm_cyl [CompactSpace (Lim f)] (hf : IsProjSystem f) (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h))
    (i : ι) (g : C(X i, ℝ)) : ‖g‖ ≤ ‖cyl f i g‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y => ?_
  obtain ⟨x, rfl⟩ := surjective_proj f hf hs i y
  exact (cyl f i g).norm_coe_le_norm x

variable [∀ i, IsFiniteMeasure (μ i)]

/-- **The functional on cylinder functions**: `g ∘ proj i ↦ ∫ g dμ i`, a linear map on the
subalgebra of cylinder functions. -/
noncomputable def cylFunctional (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) :
    cylAlgebra f hf →ₗ[ℝ] ℝ where
  toFun := cylInt μ hf
  map_add' φ ψ := by
    obtain ⟨i, g, hg⟩ := φ.2
    obtain ⟨j, g', hg'⟩ := ψ.2
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hsum : (φ + ψ).1 = cyl f k ((g.comp ⟨f hik, hf.cont i k hik⟩) +
        (g'.comp ⟨f hjk, hf.cont j k hjk⟩)) := by
      show φ.1 + ψ.1 = _
      rw [hg, hg', cyl_eq_cyl_comp f hf hik g, cyl_eq_cyl_comp f hf hjk g']
      ext x
      simp [cyl_apply]
    rw [cylInt_eq hf hs hμ _ hsum, cylInt_eq hf hs hμ _ hg, cylInt_eq hf hs hμ _ hg']
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_of_continuous (μ k) (g.comp ⟨f hik, hf.cont i k hik⟩))
      (integrable_of_continuous (μ k) (g'.comp ⟨f hjk, hf.cont j k hjk⟩))]
    rw [← integral_comp_bonding hf hμ hik g, ← integral_comp_bonding hf hμ hjk g']
    rfl
  map_smul' c φ := by
    obtain ⟨i, g, hg⟩ := φ.2
    have hc : (c • φ).1 = cyl f i (c • g) := by
      show c • φ.1 = _
      rw [hg]
      ext x
      simp [cyl_apply]
    rw [RingHom.id_apply, cylInt_eq hf hs hμ _ hc, cylInt_eq hf hs hμ _ hg]
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact integral_const_mul c _

lemma cylFunctional_cyl (hf : IsProjSystem f) (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h))
    (hμ : Consistent f μ) (i : ι) (g : C(X i, ℝ)) :
    cylFunctional hf hs hμ ⟨cyl f i g, mem_cylAlgebra f hf i g⟩ = ∫ y, g y ∂μ i :=
  cylInt_eq hf hs hμ _ rfl

/-- **Boundedness**: `|Λ φ| ≤ M ‖φ‖`, where `M` is the total mass (the same for all `i`). -/
theorem abs_cylFunctional_le [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ)
    (φ : cylAlgebra f hf) :
    ‖cylFunctional hf hs hμ φ‖ ≤ (μ (Classical.arbitrary ι)).real Set.univ * ‖φ.1‖ := by
  obtain ⟨i, g, hg⟩ := φ.2
  have h1 : cylFunctional hf hs hμ φ = ∫ y, g y ∂μ i := cylInt_eq hf hs hμ _ hg
  have h2 : ‖∫ y, g y ∂μ i‖ ≤ ‖g‖ * (μ i).real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => g.norm_coe_le_norm y)
  have h3 : (μ i).real Set.univ = (μ (Classical.arbitrary ι)).real Set.univ := by
    simp only [Measure.real, hμ.measure_univ_eq hf i (Classical.arbitrary ι)]
  have h4 : ‖g‖ ≤ ‖φ.1‖ := by
    rw [hg]
    exact norm_le_norm_cyl hf hs i g
  rw [h1]
  refine h2.trans ?_
  rw [h3, mul_comm]
  exact mul_le_mul_of_nonneg_left h4 ENNReal.toReal_nonneg

end Lightlike.Canonical.ProjectiveLimitMeasure

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.Consistent.measure_univ_eq := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.Consistent.measure_univ_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.abs_cylFunctional_le := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.abs_cylFunctional_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylFunctional := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylFunctional
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylFunctional_cyl := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylFunctional_cyl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylInt := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylInt
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylInt_eq := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylInt_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.integrable_of_continuous := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.integrable_of_continuous
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.norm_le_norm_cyl := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.norm_le_norm_cyl
