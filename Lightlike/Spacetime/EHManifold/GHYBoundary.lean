import Lightlike.Spacetime.EHManifold.GHYLocal
import Lightlike.Spacetime.EHManifold.DomainDivergence
import Lightlike.Spacetime.LeviCivita

/-!
# The boundary of a region in a graph chart (M16, step 3b)

`pd_of_eventually_vanishing_on_graph_at`: a function vanishing on the graph of `γ` near `y` and differentiable at
the graph point has only a normal derivative there, `∂_τ H = ν_τ ∂_i H` with the graph conormal `ν`
(the hypothesis of `pd_of_eventually_vanishing_on_graph` only at the point).
-/

open MeasureTheory Set Filter Topology Matrix Metric
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **A function vanishing on the graph near a point and differentiable there has only a normal derivative there.** -/
theorem pd_of_eventually_vanishing_on_graph_at (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ)
    (i : Fin (n + 1)) (H : (Fin (n + 1) → ℝ) → ℝ) (y : Fin n → ℝ) (hH : DifferentiableAt ℝ H (graphPt γ i y))
    (hz : ∀ᶠ y' in 𝓝 y, H (graphPt γ i y') = 0) (τ : Fin (n + 1)) :
    pd τ H (graphPt γ i y) = graphConormal γ i y τ * pd i H (graphPt γ i y) := by
  rcases Fin.eq_self_or_eq_succAbove i τ with h | ⟨k, h⟩
  · rw [h]
    simp only [graphConormal, Fin.insertNth_apply_same, one_mul]
  · rw [h]
    obtain ⟨z, hzdef⟩ : ∃ z : Fin (n + 1) → ℝ, z = Fin.insertNth (α := fun _ => ℝ) i 0 y := ⟨_, rfl⟩
    have hrem : i.removeNth z = y := by
      rw [hzdef]
      simp
    have hzi : z i = 0 := by
      rw [hzdef]
      simp
    have hz0 : shearFwd γ i z = graphPt γ i y := by
      unfold shearFwd graphPt
      rw [hrem, hzi, zero_add]
    have hΨ : Differentiable ℝ (shearFwd γ i) := (contDiff_shearFwd γ hγ i).differentiable (by simp)
    have hH' : DifferentiableAt ℝ H (shearFwd γ i z) := by rw [hz0]; exact hH
    have hc := pd_comp_shearFwd_succAbove γ i k H z
      ((hγ.differentiable (by simp)).differentiableAt) hH'
    have htend : Tendsto (fun w : Fin (n + 1) → ℝ => i.removeNth w) (𝓝 z) (𝓝 y) := by
      have h1 := (removeNthL i).continuous.tendsto z
      rw [removeNthL_apply, hrem] at h1
      exact h1
    have h0 : pd (i.succAbove k) (fun w => H (shearFwd γ i w)) z = 0 :=
      pd_eq_zero_of_eventually_vanishing_on_hyperplane (hH'.comp z (hΨ z)) i (i.succAbove k)
        (Fin.succAbove_ne i k) ((htend.eventually hz).mono fun w hw hwi => by
          have e : shearFwd γ i w = graphPt γ i (i.removeNth w) := by
            unfold shearFwd graphPt
            rw [hwi, hzi, zero_add]
          show H (shearFwd γ i w) = 0
          rw [e]
          exact hw)
    rw [h0, hrem, hz0] at hc
    simp only [graphConormal, Fin.insertNth_apply_succAbove]
    linarith

/-- Frontier membership depends only on the germ of the set: if `S` and `R` agree near `x`, `x` is in the frontier of
both or of neither. -/
theorem mem_frontier_congr {X : Type*} [TopologicalSpace X] {S R : Set X} {x : X}
    (h : ∀ᶠ z in 𝓝 x, (z ∈ S ↔ z ∈ R)) : x ∈ frontier S ↔ x ∈ frontier R := by
  have h1 : (∃ᶠ z in 𝓝 x, z ∈ S) ↔ ∃ᶠ z in 𝓝 x, z ∈ R := Filter.frequently_congr h
  have h2 : (∃ᶠ z in 𝓝 x, z ∈ Sᶜ) ↔ ∃ᶠ z in 𝓝 x, z ∈ Rᶜ :=
    Filter.frequently_congr (h.mono fun z hz => by rw [mem_compl_iff, mem_compl_iff, hz])
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure, mem_inter_iff, mem_inter_iff,
    mem_closure_iff_frequently, mem_closure_iff_frequently, mem_closure_iff_frequently,
    mem_closure_iff_frequently, h1, h2]

/-- **The graph is the frontier of the region above or below it.** -/
theorem graphPt_mem_frontier (σ : SignType) (hσ : σ ≠ 0) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1))
    (y : Fin n → ℝ) : graphPt γ i y ∈ frontier (graphRegion σ γ i) := by
  have hrem : ∀ c : ℝ, i.removeNth (Fin.insertNth (α := fun _ => ℝ) i c y) = y := fun c => by simp
  have happ : ∀ c : ℝ, Fin.insertNth (α := fun _ => ℝ) i c y i = c := fun c => by simp
  have hc : Continuous (fun c : ℝ => Fin.insertNth (α := fun _ => ℝ) i c y) :=
    Continuous.finInsertNth i continuous_id continuous_const
  have hlim : Tendsto (fun c : ℝ => Fin.insertNth (α := fun _ => ℝ) i c y) (𝓝 (γ y)) (𝓝 (graphPt γ i y)) :=
    hc.tendsto (γ y)
  rw [frontier_eq_closure_inter_closure]
  rcases σ with _ | _ | _
  · exact absurd rfl hσ
  · -- below the graph
    have ht : Tendsto (fun ε : ℝ => Fin.insertNth (α := fun _ => ℝ) i (γ y + ε) y) (𝓝[>] 0)
        (𝓝 (graphPt γ i y)) :=
      (hlim.comp ((continuous_const.add continuous_id).tendsto' 0 (γ y) (add_zero _))).mono_left nhdsWithin_le_nhds
    refine ⟨subset_closure ?_, mem_closure_of_tendsto ht ?_⟩
    · show graphPt γ i y i ≤ γ (i.removeNth (graphPt γ i y))
      simp [graphPt]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show ¬ (Fin.insertNth (α := fun _ => ℝ) i (γ y + ε) y i ≤ γ (i.removeNth (Fin.insertNth (α := fun _ => ℝ) i (γ y + ε) y)))
      rw [happ, hrem]
      simp only [not_le]
      exact lt_add_of_pos_right _ hε
  · -- above the graph
    have ht : Tendsto (fun ε : ℝ => Fin.insertNth (α := fun _ => ℝ) i (γ y - ε) y) (𝓝[>] 0)
        (𝓝 (graphPt γ i y)) :=
      (hlim.comp ((continuous_const.sub continuous_id).tendsto' 0 (γ y) (sub_zero _))).mono_left nhdsWithin_le_nhds
    refine ⟨subset_closure ?_, mem_closure_of_tendsto ht ?_⟩
    · show γ (i.removeNth (graphPt γ i y)) ≤ graphPt γ i y i
      simp [graphPt]
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      show ¬ (γ (i.removeNth (Fin.insertNth (α := fun _ => ℝ) i (γ y - ε) y)) ≤ Fin.insertNth (α := fun _ => ℝ) i (γ y - ε) y i)
      rw [happ, hrem]
      simp only [not_le]
      exact sub_lt_self _ hε

/-- A defining function of `D` near `q` (`D = {u ≥ 0}` near `q`), continuous at `q`, vanishes at a frontier point `q`. -/
theorem eq_zero_of_mem_frontier {X : Type*} [TopologicalSpace X] {D : Set X} {u : X → ℝ} {q : X}
    (hDq : ∀ᶠ z in 𝓝 q, (z ∈ D ↔ 0 ≤ u z)) (huq : ContinuousAt u q) (hq : q ∈ frontier D) : u q = 0 := by
  rw [mem_frontier_congr (S := D) (R := {z | 0 ≤ u z}) hDq, frontier_eq_closure_inter_closure] at hq
  obtain ⟨h1, h2⟩ := hq
  have a1 : u q ∈ closure (Ici (0 : ℝ)) := closure_mono (by rintro _ ⟨z, hz, rfl⟩; exact hz) (mem_closure_image huq h1)
  have a2 : u q ∈ closure (Iic (0 : ℝ)) := closure_mono (by
    rintro _ ⟨z, hz, rfl⟩
    exact (not_le.1 (show ¬ (0 ≤ u z) from hz)).le) (mem_closure_image huq h2)
  rw [closure_Ici] at a1
  rw [closure_Iic] at a2
  exact le_antisymm a2 a1

/-- **A graph on which a non-null defining function vanishes is not null**: if `ũ` vanishes on the graph near `y`
and `∇ũ G⁻¹ ∇ũ ≠ 0` at the graph point, then `ν G⁻¹ ν ≠ 0` for the graph conormal `ν` (since `∇ũ = (∂ᵢũ) ν`). -/
theorem conormal_nonnull_of_defining (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (γ : (Fin n → ℝ) → ℝ)
    (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1)) (y : Fin n → ℝ) (u : (Fin (n + 1) → ℝ) → ℝ)
    (hu : DifferentiableAt ℝ u (graphPt γ i y)) (hz : ∀ᶠ y' in 𝓝 y, u (graphPt γ i y') = 0)
    (hnn : ∑ a, ∑ b, pd a u (graphPt γ i y) * G⁻¹ a b * pd b u (graphPt γ i y) ≠ 0) :
    (∑ a, graphConormal γ i y a * ∑ b, G⁻¹ a b * graphConormal γ i y b) ≠ 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = pd i u (graphPt γ i y) := ⟨_, rfl⟩
  have hpd : ∀ τ, pd τ u (graphPt γ i y) = graphConormal γ i y τ * c := fun τ => by
    rw [hc]; exact pd_of_eventually_vanishing_on_graph_at γ hγ i u y hu hz τ
  intro h0
  apply hnn
  simp only [hpd]
  calc ∑ a, ∑ b, graphConormal γ i y a * c * G⁻¹ a b * (graphConormal γ i y b * c)
      = c * c *
          ∑ a, graphConormal γ i y a * ∑ b, G⁻¹ a b * graphConormal γ i y b := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = 0 := by rw [h0, mul_zero]

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- The chart preimage of a frontier point of the chart image of `D` is a frontier point of `D`. -/
theorem symm_mem_frontier_of_mem_frontier_image (x₀ : M) {D : Set M} {x : Fin n → ℝ}
    (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hf : x ∈ frontier (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' (D ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source))) :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm x ∈ frontier D := by
  have hc : ContinuousAt (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm x := continuousAt_extChartAt_symm'' hx
  rw [frontier_eq_closure_inter_closure] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  constructor
  · refine closure_mono ?_ (mem_closure_image hc h1)
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp.2]
    exact hp.1
  · have h2' := (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).inter_closure ⟨hx, h2⟩
    refine closure_mono ?_ (mem_closure_image hc h2')
    rintro _ ⟨z, ⟨hzt, hzS⟩, rfl⟩ hzD
    exact hzS ⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm z, ⟨hzD, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hzt⟩,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hzt⟩

variable [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- **`du(♯du)` in a chart**: `Σ ∂ₐũ (G⁻¹)ₐ_b ∂_bũ` for `ũ = u ∘ φ⁻¹` and the coordinate metric `G`. -/
theorem mvfderiv_sharp_chart (x₀ : M) {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {u : M → ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) u p) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) u p (sharp g p (mvfderiv 𝓘(ℝ, Fin n → ℝ) u p)) =
      ∑ a, ∑ b, pd a (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) *
        (g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p))⁻¹ a b *
        pd b (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  set y := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p with hy
  set ũ := u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm with hũ
  set G := g.coordMetric x₀ y with hG
  set L := mvfderiv 𝓘(ℝ, Fin n → ℝ) u p with hLdef
  have hpb := mem_baseSet_of_mem_source x₀ hp
  have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp
  have hL : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p, L v = ∑ k, hv x₀ p v k * pd k ũ y := fun v => by
    rw [hLdef, mvfderiv_eq_chart₀ x₀ u hp hu v, mfderiv_extChartAt_apply' x₀ hp v]
    conv_lhs => rw [vec_expand (hv x₀ p v)]
    simp only [map_sum, map_smul, smul_eq_mul, pd]
    rfl
  set w := sharp g p L with hw
  have hGs : Gᵀ = G := g.coordMetric_transpose x₀ y
  have hGw : G *ᵥ hv x₀ p w = fun k => pd k ũ y := by
    funext k
    have h1 := g_sharp g p L (coordField x₀ k p)
    rw [g_hv' x₀ g hp, hv_coordField x₀ hpb k, hL, hv_coordField x₀ hpb k] at h1
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    rw [← h1]
    conv_lhs => rw [← hGs]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hdet : IsUnit G.det := g.coordMetric_isUnit_det x₀ hyt
  have hwv : hv x₀ p w = G⁻¹ *ᵥ fun k => pd k ũ y := by
    rw [← hGw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [hL, hwv]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Manifold

end Lightlike
