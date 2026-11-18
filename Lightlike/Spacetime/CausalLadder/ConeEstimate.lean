import Lightlike.Spacetime.Causal.SmoothOrientation
import Lightlike.Spacetime.CausalLadder.UniformCone
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# Chart cone estimate for future causal vectors

Around a point `p`, in the coordinates of the tangent-bundle trivialization at `p`, every future
causal vector is controlled by one fixed linear functional: `‖w‖ ≤ C · ℓ(w)`. This is the local
cone estimate behind the limit-curve theorem for causal curves.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Local cone estimate.** Around `p` there are a neighbourhood `W`, a linear functional `ℓ` on
the model space and a constant `C` such that every future-directed causal vector at a point `q ∈ W`
has coordinates `w` in the trivialization of the tangent bundle at `p` with `‖w‖ ≤ C · ℓ w`. -/
theorem exists_cone_estimate (p : M) :
    ∃ W ∈ 𝓝 p, W ⊆ (tTriv I M p).baseSet ∧ ∃ (ℓ : E →L[ℝ] ℝ) (C : ℝ), 0 < C ∧
      ∀ q ∈ W, ∀ v : TangentSpace I q, T.IsFutureCausal v →
        ‖(tTriv I M p ⟨q, v⟩).2‖ ≤ C * ℓ (tTriv I M p ⟨q, v⟩).2 := by
  have hp : p ∈ (tTriv I M p).baseSet := mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  obtain ⟨e, he⟩ := g.lorentzian p
  let L : ∀ q ∈ (tTriv I M p).baseSet, TangentSpace I q ≃ₗ[ℝ] E :=
    fun q hq => (tTriv I M p).linearEquivAt ℝ q hq
  let ξ : Module.Basis (Fin n) ℝ E := e.map (L p hp)
  -- the frame fields, constant in the trivialization at `p`
  let Y : Fin n → ∀ q : M, TangentSpace I q := fun i q => localField (I := I) p (ξ i) q
  have hYsymm : ∀ i q (hq : q ∈ (tTriv I M p).baseSet), Y i q = (L q hq).symm (ξ i) := by
    intro i q hq
    exact ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq (ξ i)).symm
  have hYp : ∀ i, Y i p = e i := by
    intro i
    rw [hYsymm i p hp]
    simp only [ξ, L, Module.Basis.map_apply]
    rw [Trivialization.linearEquivAt_symm_apply (R := ℝ), Trivialization.linearEquivAt_apply]
    exact (tTriv I M p).symm_apply_apply_mk hp (e i)
  have hbase : (tTriv I M p).baseSet ∈ 𝓝 p := (tTriv I M p).open_baseSet.mem_nhds hp
  have hYsm : ∀ i, ∀ q ∈ (tTriv I M p).baseSet,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
        (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (Y i q)) q := by
    intro i q hq
    exact (((localField_contMDiffOn (I := I) p (ξ i)).contMDiffAt
      ((tTriv I M p).open_baseSet.mem_nhds hq)).of_le (by norm_num))
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (T.X q)) p := T.contMDiff p
  let a : M → Fin n → Fin n → ℝ := fun q i j => g.g q (Y i q) (Y j q)
  let b : M → Fin n → ℝ := fun q i => g.g q (Y i q) (T.X q)
  have ha : ContinuousAt a p :=
    continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
      continuousAt_metric_apply (hYsm i p hp) (hYsm j p hp)
  have hb : ContinuousAt b p :=
    continuousAt_pi.2 fun i => continuousAt_metric_apply (hYsm i p hp) hX
  -- expansion of the metric on combinations of the frame
  have hquad : ∀ (q : M) (c : Fin n → ℝ),
      g.g q (∑ i, c i • Y i q) (∑ j, c j • Y j q) = quadForm (a q) c := by
    intro q c
    simp only [quadForm, map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [g.symm q (Y j q) (Y i q)]; ring
  have hlin : ∀ (q : M) (c : Fin n → ℝ),
      g.g q (∑ i, c i • Y i q) (T.X q) = linForm (b q) c := by
    intro q c
    simp only [linForm, map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul, b]
  have h0 : ∀ c : Fin n → ℝ, c ≠ 0 → quadForm (a p) c ≤ 0 → linForm (b p) c ≠ 0 := by
    intro c hc hq hl
    have hw : ∑ i, c i • e i = 0 := by
      refine (g.lorentzian p).eq_zero_of_orthogonal_timelike (X := T.X p) (T.timelike p) ?_ ?_
      · have := hlin p c
        simp only [hYp] at this
        rw [this, hl]
      · have := hquad p c
        simp only [hYp] at this
        rw [this]; exact hq
    exact hc (Fintype.linearIndependent_iff.1 e.linearIndependent c hw |> funext)
  obtain ⟨W0, hW0, c0, hc0, hcone⟩ := uniform_cone_bound ha hb h0
  set K : ℝ := ∑ i, ‖ξ i‖ + 1 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ ∑ i, ‖ξ i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    linarith
  have : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  let ℓl : E →ₗ[ℝ] ℝ := -(∑ i, b p i • ξ.coord i)
  let ℓ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ℓl
  have hℓ : ∀ w, ℓ w = -(linForm (b p) (fun i => ξ.repr w i)) := by
    intro w
    simp [ℓ, ℓl, linForm, Module.Basis.coord_apply, mul_comm]
  refine ⟨W0 ∩ (tTriv I M p).baseSet, Filter.inter_mem hW0 hbase, inter_subset_right, ℓ, K * c0,
    mul_pos hKpos hc0, ?_⟩
  rintro q ⟨hq0, hqb⟩ v ⟨hv0, hvv, hvX⟩
  have hw : (tTriv I M p ⟨q, v⟩).2 = L q hqb v :=
    ((tTriv I M p).linearEquivAt_apply (R := ℝ) q hqb v).symm
  rw [hw]
  set w : E := L q hqb v with hwdef
  set c : Fin n → ℝ := fun i => ξ.repr w i with hc
  have hwc : w = ∑ i, c i • ξ i := by
    have := (ξ.sum_repr w).symm
    simp [hc]
  have hvc : v = ∑ i, c i • Y i q := by
    have : v = (L q hqb).symm w := ((L q hqb).symm_apply_apply v).symm
    rw [this, hwc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hYsymm i q hqb]
  have hQ : quadForm (a q) c ≤ 0 := by
    rw [← hquad q c, ← hvc]; exact hvv
  have hL : linForm (b q) c < 0 := by
    rw [← hlin q c, ← hvc]; exact hvX
  have h1 := hcone q hq0 c hQ hL
  rw [hℓ]
  have h2 : ‖w‖ ≤ K * ‖c‖ := by
    calc ‖w‖ = ‖∑ i, c i • ξ i‖ := by rw [← hwc]
      _ ≤ ∑ i, ‖c i • ξ i‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖ξ i‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖c‖ * ‖ξ i‖ := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _)
      _ = ‖c‖ * ∑ i, ‖ξ i‖ := by rw [Finset.mul_sum]
      _ ≤ K * ‖c‖ := by rw [hK]; nlinarith [norm_nonneg c]
  calc ‖w‖ ≤ K * ‖c‖ := h2
    _ ≤ K * (c0 * (-(linForm (b p) c))) := mul_le_mul_of_nonneg_left h1 hKpos.le
    _ = K * c0 * -linForm (b p) (fun i => ξ.repr w i) := by rw [hc]; ring

end Lightlike.Causal
