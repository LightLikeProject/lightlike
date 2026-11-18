import Lightlike.Spacetime.CausalLadder.ConeEstimate
import Lightlike.Spacetime.CausalLadder.ConeTransfer

/-!
# Coordinates of the metric and of the time orientation in a frame, around a point

Around `p`, fix a Lorentz frame `ξ` of the model space, transported by the trivialization of the
tangent bundle at `p`. The Gram matrix `a q` of the metric in the transported frame and the pairing
`b q` of the frame with the time orientation are continuous at `p`, and for every tangent vector `v` at
`q` in the base set of the trivialization, with coordinates `c` in the frame, `g(v, v)` is the quadratic
form of `a q` at `c` and `g(v, X)` the linear form of `b q`. Moreover no nonzero `c` with `a p`-norm `≤ 0`
is orthogonal to `b p`. This turns the cone conditions on tangent vectors into the real-analysis
statements of `UniformCone` and `ConeTransfer`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **The metric and the time orientation in a frame around `p`.** See the module docstring. -/
theorem exists_chart_model (p : M) :
    ∃ (ξ : Module.Basis (Fin n) ℝ E) (a : M → Fin n → Fin n → ℝ) (b : M → Fin n → ℝ),
      ContinuousAt a p ∧ ContinuousAt b p ∧
      (∀ c : Fin n → ℝ, c ≠ 0 → quadForm (a p) c ≤ 0 → linForm (b p) c ≠ 0) ∧
      ∀ (q : M) (hq : q ∈ (tTriv I M p).baseSet) (v : TangentSpace I q),
        g.g q v v = quadForm (a q) (fun i => ξ.repr (tTriv I M p ⟨q, v⟩).2 i) ∧
        g.g q v (T.X q) = linForm (b q) (fun i => ξ.repr (tTriv I M p ⟨q, v⟩).2 i) := by
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
  refine ⟨ξ, a, b, ha, hb, h0, ?_⟩
  intro q hqb v
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
  exact ⟨by rw [← hquad q c, ← hvc], by rw [← hlin q c, ← hvc]⟩

end Lightlike.Causal
