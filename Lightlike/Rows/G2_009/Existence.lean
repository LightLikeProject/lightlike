import Lightlike.Rows.G2_009.Positive
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Existence of the projective limit measure (row G2-009, CA2)

A cylindrically consistent family `μ` of finite Borel measures on a directed system of nonempty
compact Hausdorff spaces with surjective bonding maps has a projective limit: the Riesz–Markov
measure of the positive functional `cylExt` on `C(Lim f, ℝ)` pushes forward to each `μ i`
(`ashtekar-lewandowski-1995`, §3.3, `baez-1996`, Lemma 3).  Uniqueness of the pushforward in each
`X i` uses that finite Borel measures on `X i` are determined by their integrals of bounded
continuous functions (`HasOuterApproxClosed`, true for metrizable `X i`, such as `G^n`).
-/

open MeasureTheory
open scoped CompactlySupported

namespace Lightlike.Rows.G2_009

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  [IsDirected ι (· ≤ ·)] [Nonempty ι] [∀ i, CompactSpace (X i)]
  [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsFiniteMeasure (μ i)]

/-- The extension `cylExt` as a positive linear functional on `C_c(Lim f, ℝ)`. -/
noncomputable def cylPositive [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) :
    C_c(Lim f, ℝ) →ₚ[ℝ] ℝ where
  toFun g := cylExt hf hs hμ ⟨g, g.continuous⟩
  map_add' g g' := by
    rw [← map_add]
    rfl
  map_smul' c g := by
    rw [RingHom.id_apply, ← map_smul]
    rfl
  monotone' g g' h := by
    have h0 : 0 ≤ (⟨g', g'.continuous⟩ : C(Lim f, ℝ)) - ⟨g, g.continuous⟩ :=
      fun x => sub_nonneg.2 (h x)
    have h1 := cylExt_nonneg hf hs hμ h0
    rw [map_sub] at h1
    exact sub_nonneg.1 h1

/-- **Existence of the projective limit** (Kolmogorov extension for compact spaces): a
cylindrically consistent family of finite Borel measures has a Borel measure on `Lim f` pushing
forward to each member. -/
theorem exists_isLimit [∀ i, HasOuterApproxClosed (X i)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) :
    ∃ ν : Measure (Lim f), IsLimit f ν μ := by
  have := compactSpace_lim f hf
  refine ⟨RealRMK.rieszMeasure (cylPositive hf hs hμ), fun i => ?_⟩
  set ν := RealRMK.rieszMeasure (cylPositive hf hs hμ) with hν
  have hint : ∀ φ : C(Lim f, ℝ), ∫ x, φ x ∂ν = cylExt hf hs hμ φ := fun φ =>
    RealRMK.integral_rieszMeasure (cylPositive hf hs hμ) ⟨φ, HasCompactSupport.of_compactSpace φ⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map (continuous_proj f i).aemeasurable g.continuous.aestronglyMeasurable]
  have := hint (cyl f i ⟨g, g.continuous⟩)
  rw [cylExt_cyl hf hs hμ] at this
  exact this

end Lightlike.Rows.G2_009
