import Mathlib
import Lightlike.Canonical.Hypersurface

/-!
# The one-chart bridge for the constraints on a hypersurface

On `M = ℝᵈ` (the model space, whose atlas is its identity chart) the sum over the atlas pieces of the chart integrals is
the integral over `ℝᵈ`: `chartSum_modelSpace`. The constraints `momentumConstraintM` and `hamiltonianConstraintM` of constant
chart families are the chart constraints `momentumConstraint` and `hamiltonianConstraint` of `Lightlike/Canonical/ADM.lean`.
-/

open MeasureTheory Set Manifold

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- On the model space every chart is the identity. -/
lemma extChartAt_modelSpace (x : Fin d → ℝ) :
    extChartAt 𝓘(ℝ, Fin d → ℝ) x = PartialEquiv.refl (Fin d → ℝ) := by
  rw [extChartAt_model_space_eq_id]

/-- **The chart sum on the model space is the integral over the model space** for a chart family that does not depend on
the base point. -/
lemma chartSum_modelSpace (f : (Fin d → ℝ) → ℝ) :
    chartSum (M := Fin d → ℝ) (fun _ y => f y) = ∫ y, f y := by
  classical
  have hne : Nonempty (AtlasIdx (n := d) (Fin d → ℝ)) := by
    have hc := atlasPts_cover (n := d) (M := Fin d → ℝ)
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have : (atlasPts (n := d) (Fin d → ℝ)) = ∅ := by
      ext x; constructor
      · intro hx; exact (hcon.false ⟨x, hx⟩).elim
      · intro hx; exact hx.elim
    rw [this] at hc
    simp at hc
    exact Set.empty_ne_univ hc
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : AtlasIdx (n := d) (Fin d → ℝ), ∀ j, Encodable.encode i₀ ≤ Encodable.encode j := by
    obtain ⟨i⟩ := hne
    have hex : ∃ n, ∃ j : AtlasIdx (n := d) (Fin d → ℝ), Encodable.encode j = n := ⟨_, i, rfl⟩
    obtain ⟨j, hj⟩ := Nat.find_spec hex
    exact ⟨j, fun k => by rw [hj]; exact Nat.find_min' hex ⟨k, rfl⟩⟩
  have hsrc : ∀ x : Fin d → ℝ, (chartAt (Fin d → ℝ) x).source = univ := fun x => by
    simp [chartAt]
  have hpiece : ∀ i : AtlasIdx (n := d) (Fin d → ℝ), atlasPiece i = if Encodable.encode i₀ < Encodable.encode i then ∅ else univ := by
    intro i
    unfold atlasPiece
    simp only [hsrc]
    by_cases h : Encodable.encode i₀ < Encodable.encode i
    · simp only [h, ↓reduceIte]
      have : (⋃ j ∈ {j : AtlasIdx (n := d) (Fin d → ℝ) | Encodable.encode j < Encodable.encode i}, (univ : Set (Fin d → ℝ))) = univ := by
        ext x; simp only [mem_iUnion, mem_univ, iff_true]
        exact ⟨i₀, h, trivial⟩
      rw [this]; simp
    · simp only [h, ↓reduceIte]
      have : (⋃ j ∈ {j : AtlasIdx (n := d) (Fin d → ℝ) | Encodable.encode j < Encodable.encode i}, (univ : Set (Fin d → ℝ))) = ∅ := by
        ext x; simp only [mem_iUnion, mem_univ, exists_prop, mem_empty_iff_false, iff_false, not_exists, mem_ofPred_eq]
        intro j hj
        exact h (lt_of_le_of_lt (hi₀ j) hj.1)
      rw [this]; simp
  unfold chartSum
  rw [tsum_eq_single i₀]
  · rw [pieceImage, hpiece, extChartAt_modelSpace]
    simp
  · intro i hi
    have hne' : Encodable.encode i₀ < Encodable.encode i :=
      lt_of_le_of_ne (hi₀ i) (fun h => hi (Encodable.encode_injective h).symm)
    rw [pieceImage, hpiece]
    simp [hne']

/-- On the model space the function `N` in any chart is `N`. -/
lemma chartScalar_modelSpace (N : (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ) : chartScalar N x₀ = N := by
  funext y
  simp [chartScalar]

/-- **The one-chart bridge** (library form of `T-CA1-P7`): on `ℝᵈ`, the constraints on a hypersurface of constant chart
families are the chart constraints. -/
theorem constraintM_bridge_global (ξ : VectorField d) (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) :
    momentumConstraintM (M := Fin d → ℝ) (fun _ => ξ) (fun _ => h) (fun _ => π) = momentumConstraint ξ h π ∧
      hamiltonianConstraintM (M := Fin d → ℝ) N (fun _ => h) (fun _ => π) = hamiltonianConstraint N h π := by
  constructor
  · exact chartSum_modelSpace (fun y => momentumDensity ξ h π y)
  · unfold hamiltonianConstraintM
    have e : (fun (x₀ : Fin d → ℝ) (y : Fin d → ℝ) => chartScalar N x₀ y * hamiltonianDensity h π y) =
        fun _ y => N y * hamiltonianDensity h π y := by
      funext x₀ y; rw [chartScalar_modelSpace]
    rw [e]
    exact chartSum_modelSpace (fun y => N y * hamiltonianDensity h π y)

end Lightlike.Canonical

end
