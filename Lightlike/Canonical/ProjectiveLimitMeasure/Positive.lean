import Lightlike.Canonical.ProjectiveLimitMeasure.Closure

/-!
# Positivity of the extended functional (row G2-009, CA2)

The extension `cylExt` of the cylinder functional to `C(Lim f, ℝ)` is a positive functional: a
nonnegative continuous function is a uniform limit of cylinder functions that are almost
nonnegative, and `∫ g dμ i ≥ -ε μ(1)` for a cylinder profile `g ≥ -ε`
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
  {μ : ∀ i, Measure (X i)} [∀ i, IsFiniteMeasure (μ i)]

/-- A cylinder function close to a nonnegative function has an integral that is almost
nonnegative: `∫ g dμ i ≥ -ε · μ i (univ)`. -/
lemma neg_mul_le_integral_of_dist_lt [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) {φ : C(Lim f, ℝ)} (hφ : 0 ≤ φ)
    (i : ι) (g : C(X i, ℝ)) {ε : ℝ} (h : dist (cyl f i g) φ < ε) :
    -(ε * (μ i).real Set.univ) ≤ ∫ y, g y ∂μ i := by
  have hg : ∀ y, -ε ≤ g y := by
    intro y
    obtain ⟨x, rfl⟩ := surjective_proj f hf hs i y
    have h1 := (ContinuousMap.dist_apply_le_dist x).trans_lt h
    have h2 := (abs_lt.1 (by simpa [Real.dist_eq] using h1)).1
    have h3 : 0 ≤ φ x := hφ x
    have : g (proj f i x) = cyl f i g x := rfl
    linarith
  have h4 : ∫ _ : X i, -ε ∂μ i ≤ ∫ y, g y ∂μ i :=
    integral_mono (integrable_const _) (integrable_of_continuous (μ i) g) hg
  rw [integral_const, smul_eq_mul] at h4
  linarith

/-- **Positivity**: the extension of the cylinder functional is nonnegative on nonnegative
functions. -/
theorem cylExt_nonneg [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ)
    {φ : C(Lim f, ℝ)} (hφ : 0 ≤ φ) : 0 ≤ cylExt hf hs hμ φ := by
  by_contra hneg
  rw [not_le] at hneg
  set c := -cylExt hf hs hμ φ with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  set M := (μ (Classical.arbitrary ι)).real Set.univ with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1
    (cylExt hf hs hμ).continuous.continuousAt (c / 2) (by linarith)
  set ε := min δ (c / (2 * (M + 1))) with hε
  have hεpos : 0 < ε := lt_min hδ (by positivity)
  obtain ⟨ψ, hψ, hdist⟩ := (dense_cylAlgebra hf).exists_dist_lt φ hεpos
  obtain ⟨i, g, rfl⟩ := hψ
  have hd : dist (cyl f i g) φ < ε := by rwa [dist_comm]
  have h1 := neg_mul_le_integral_of_dist_lt (μ := μ) hf hs hφ i g hd
  have hMi : (μ i).real Set.univ = M := by
    rw [hM]
    simp only [Measure.real]
    rw [hμ.measure_univ_eq hf i (Classical.arbitrary ι)]
  rw [hMi, ← cylExt_cyl hf hs hμ i g] at h1
  have h2 := hδ' (x := cyl f i g) (lt_of_lt_of_le hd (min_le_left _ _))
  rw [Real.dist_eq] at h2
  have h3 := (abs_lt.1 h2).2
  have h4 : ε ≤ c / (2 * (M + 1)) := min_le_right _ _
  have h5 : ε * (M + 1) ≤ c / 2 := by
    calc ε * (M + 1) ≤ c / (2 * (M + 1)) * (M + 1) :=
          mul_le_mul_of_nonneg_right h4 (by linarith)
      _ = c / 2 := by field_simp
  have h6 : ε * M < c / 2 := by nlinarith
  linarith

end Lightlike.Canonical.ProjectiveLimitMeasure

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylExt_nonneg := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylExt_nonneg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.neg_mul_le_integral_of_dist_lt := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.neg_mul_le_integral_of_dist_lt
