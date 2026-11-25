import Lightlike.Canonical.ProjectiveLimitIntegral.Cylindrical
import Lightlike.Canonical.ProjectiveLimitIntegral.Surjective

/-!
# The integral functional on cylindrical functions (row G2-008)

For a cylindrically consistent family `μ i` of measures on an inverse system of compact Hausdorff
spaces with surjective bonding maps, the assignment `φ ∘ proj i ↦ ∫ φ dμ i` is well defined on the
cylindrical functions (`integral_eq_of_cyl_eq`).  This is the first step in the construction of the
projective-limit measure via the Riesz–Markov theorem.
-/

noncomputable section

open MeasureTheory Set

namespace Lightlike.Canonical.ProjectiveLimitIntegral

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)

/-- A cylindrical function is determined by its base function once the projection is surjective. -/
lemma cyl_injective {k : ι} (hk : Function.Surjective (S.proj k)) :
    Function.Injective (S.cyl k) := by
  intro φ ψ h
  ext a
  obtain ⟨x, rfl⟩ := hk a
  simpa using congrArg (fun F : C(S.Limit, ℝ) => F x) h

section Measures

variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]

/-- Integrating the pull-back of `φ` along a bonding map against `μ k` gives `∫ φ dμ i`. -/
lemma integral_comp_f {μ : ∀ i, Measure (X i)} (hμ : S.IsConsistent μ) {i k : ι} (h : i ≤ k)
    (φ : C(X i, ℝ)) :
    ∫ x, (φ.comp ⟨S.f h, S.continuous_f h⟩) x ∂(μ k) = ∫ y, φ y ∂(μ i) := by
  rw [← hμ i k h]
  exact (integral_map (S.measurable_f h).aemeasurable
    φ.continuous.aestronglyMeasurable).symm

/-- **Well-definedness**: two base functions with the same cylindrical function have the same
integral. -/
theorem integral_eq_of_cyl_eq [IsDirectedOrder ι] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    (hS : ∀ {i j : ι} (h : i ≤ j), Function.Surjective (S.f h))
    {μ : ∀ i, Measure (X i)} (hμ : S.IsConsistent μ) {i j : ι} {φ : C(X i, ℝ)} {ψ : C(X j, ℝ)}
    (h : S.cyl i φ = S.cyl j ψ) : ∫ x, φ x ∂(μ i) = ∫ y, ψ y ∂(μ j) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h1 : S.cyl k (φ.comp ⟨S.f hik, S.continuous_f hik⟩) =
      S.cyl k (ψ.comp ⟨S.f hjk, S.continuous_f hjk⟩) := by
    rw [← S.cyl_eq_of_le hik φ, ← S.cyl_eq_of_le hjk ψ]; exact h
  have h2 := S.cyl_injective (S.proj_surjective hS k) h1
  rw [← S.integral_comp_f hμ hik φ, ← S.integral_comp_f hμ hjk ψ, h2]

end Measures

end InvSystem

end Lightlike.Canonical.ProjectiveLimitIntegral

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.cyl_injective := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.cyl_injective
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.integral_comp_f := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.integral_comp_f
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_008.InvSystem.integral_eq_of_cyl_eq := _root_.Lightlike.Canonical.ProjectiveLimitIntegral.InvSystem.integral_eq_of_cyl_eq
