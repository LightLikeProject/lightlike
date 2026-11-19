import Lightlike.Spacetime.EHManifold.RegularDomainDivergence

/-!
# Tests for the divergence theorem on domains with regular boundary

* `graphFlux_zero`: for the graph of the zero function the flux is the integral of the normal component over
  the hyperplane;
* `integral_divergence_halfSpace_of_graphRegion`: the graph-region theorem gives back the half-space case;
* `slab_locally_graph`: the slab `0 ≤ x_i ≤ 1` satisfies the hypothesis of
  `exists_graph_atlas_integral_divergence` (two graph charts of opposite orientation), so that theorem is
  not vacuous;
* `exists_graph_atlas_integral_divergence_slab`: the theorem on the slab.

No catalogue entry.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The flux through the graph of the zero function. -/
theorem graphFlux_zero (i : Fin (n + 1)) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) :
    graphFlux (fun _ => 0) i F = ∫ y : Fin n → ℝ, F i (Fin.insertNth (α := fun _ => ℝ) i 0 y) := by
  unfold graphFlux
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : ∀ k : Fin n, pd k (fun _ : Fin n → ℝ => (0 : ℝ)) y = 0 := fun k => by simp [pd]
  simp [h0]

/-- The graph-region theorem gives back the half-space case. -/
theorem integral_divergence_halfSpace_of_graphRegion (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x in {x : Fin (n + 1) → ℝ | 0 ≤ x i}, ∑ j, pd j (F j) x =
      -∫ y : Fin n → ℝ, F i (Fin.insertNth (α := fun _ => ℝ) i 0 y) := by
  have h := integral_divergence_graphRegion SignType.pos (fun _ : Fin n → ℝ => (0 : ℝ)) contDiff_const
    i F hF hc
  rw [graphFlux_zero] at h
  simpa [graphRegion] using h

/-- The slab `0 ≤ x_i ≤ 1` is locally the region above or below a graph. -/
theorem slab_locally_graph (i : Fin (n + 1)) :
    ∀ x ∈ closure {x : Fin (n + 1) → ℝ | 0 ≤ x i ∧ x i ≤ 1}, ∃ U ∈ 𝓝 x,
      ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i' : Fin (n + 1)), ContDiff ℝ 2 γ ∧
        ∀ y ∈ U, (y ∈ {x : Fin (n + 1) → ℝ | 0 ≤ x i ∧ x i ≤ 1} ↔ y ∈ graphRegion σ γ i') := by
  intro x _
  by_cases hx : x i < 1
  · refine ⟨{y | y i < 1}, (isOpen_lt (continuous_apply i) continuous_const).mem_nhds hx,
      SignType.pos, fun _ => 0, i, contDiff_const, fun y hy => ?_⟩
    show (0 ≤ y i ∧ y i ≤ 1) ↔ (0 : ℝ) ≤ y i
    exact ⟨fun h => h.1, fun h => ⟨h, le_of_lt hy⟩⟩
  · have hx' : 0 < x i := by linarith [not_lt.1 hx]
    refine ⟨{y | 0 < y i}, (isOpen_lt continuous_const (continuous_apply i)).mem_nhds hx',
      SignType.neg, fun _ => 1, i, contDiff_const, fun y hy => ?_⟩
    show (0 ≤ y i ∧ y i ≤ 1) ↔ y i ≤ (1 : ℝ)
    exact ⟨fun h => h.2, fun h => ⟨le_of_lt hy, h⟩⟩

/-- The divergence theorem on the slab `0 ≤ x_i ≤ 1`, from the theorem for domains with regular
boundary. -/
theorem exists_graph_atlas_integral_divergence_slab (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i' : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) →
        (x ∈ {x : Fin (n + 1) → ℝ | 0 ≤ x i ∧ x i ≤ 1} ↔ x ∈ graphRegion (σ a) (γ a) (i' a))) ∧
      (∀ y ∈ closure {x : Fin (n + 1) → ℝ | 0 ≤ x i ∧ x i ≤ 1},
        (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in {x : Fin (n + 1) → ℝ | 0 ≤ x i ∧ x i ≤ 1}, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i' a) (fun j y => ρ a y * F j y) :=
  exists_graph_atlas_integral_divergence _
    ((measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_le (measurable_pi_apply i) measurable_const)) F hF hc (slab_locally_graph i)

end Lightlike
