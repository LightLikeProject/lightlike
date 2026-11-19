import Lightlike.Spacetime.EHManifold.DefiningFunction

/-!
# Tests for the divergence theorem with defining functions

* `obliqueHalfSpace_regular`: for a nonzero continuous linear functional `ℓ` on `ℝⁿ⁺¹`, the half-space
  `{ℓ ≥ 0}` satisfies the hypothesis of `exists_graph_atlas_integral_divergence_of_defining_function`, with
  the defining function `ℓ`. The half-space need not be bounded by a coordinate hyperplane: the graph charts
  come from the implicit function theorem.
* `exists_graph_atlas_integral_divergence_obliqueHalfSpace`: the divergence theorem on such a half-space.

No catalogue entry.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- An oblique half-space has a regular boundary, with the linear functional as defining function. -/
theorem obliqueHalfSpace_regular (ℓ : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ∀ x ∈ closure {x : Fin (n + 1) → ℝ | 0 ≤ ℓ x}, ∃ u : (Fin (n + 1) → ℝ) → ℝ,
      ContDiffAt ℝ 2 u x ∧ (u x = 0 → fderiv ℝ u x ≠ 0) ∧
        ∀ᶠ y in 𝓝 x, (y ∈ {x : Fin (n + 1) → ℝ | 0 ≤ ℓ x} ↔ 0 ≤ u y) := by
  intro x _
  refine ⟨fun y => ℓ y, ℓ.contDiff.contDiffAt, fun _ => ?_, Filter.Eventually.of_forall fun y => Iff.rfl⟩
  have h : fderiv ℝ (fun y => ℓ y) x = ℓ := ℓ.hasFDerivAt.fderiv
  rw [h]
  exact hℓ

/-- The divergence theorem on an oblique half-space. -/
theorem exists_graph_atlas_integral_divergence_obliqueHalfSpace (ℓ : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) →
        (x ∈ {x : Fin (n + 1) → ℝ | 0 ≤ ℓ x} ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure {x : Fin (n + 1) → ℝ | 0 ≤ ℓ x}, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in {x : Fin (n + 1) → ℝ | 0 ≤ ℓ x}, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) :=
  exists_graph_atlas_integral_divergence_of_defining_function _
    (measurableSet_le measurable_const ℓ.continuous.measurable) F hF hc
    (obliqueHalfSpace_regular ℓ hℓ)

end Lightlike
