import Lightlike.Spacetime.Causal.SmoothOrientation
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# A frozen functional bounds the future causal cone from one side

Fix a point `x₀` in the base set of the tangent-bundle trivialization at `p` and a vector `V` of the
model space that is future timelike at `x₀` when transported by the trivialization (the vector
`localField p V`). Let `Φ w = g_{x₀}(V, w)` in the coordinates of the trivialization. Near `x₀`, the
transported `V` is future timelike, so by `IsLorentzianForm.nonpos_of_futureCausal` it has
nonpositive product with every future causal vector; since the metric is continuous, `Φ w ≤ ε ‖w‖`
for every future causal vector with coordinates `w` at a point near `x₀`.

This is the one-sided estimate used to show that a uniform limit of causal curves has an
almost-everywhere derivative in the closed future cone.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Frozen functional estimate.** See the module docstring. -/
theorem exists_functional_estimate (p x₀ : M) (hx₀ : x₀ ∈ (tTriv I M p).baseSet) (V : E)
    (hV1 : g.g x₀ (localField (I := I) p V x₀) (localField (I := I) p V x₀) < 0)
    (hV2 : g.g x₀ (localField (I := I) p V x₀) (T.X x₀) < 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : E →L[ℝ] ℝ, (∀ u : TangentSpace I x₀, Φ (tTriv I M p ⟨x₀, u⟩).2 =
        g.g x₀ (localField (I := I) p V x₀) u) ∧
      ∃ N ∈ 𝓝 x₀, N ⊆ (tTriv I M p).baseSet ∧ ∀ q ∈ N, ∀ v : TangentSpace I q, T.IsFutureCausal v →
        Φ (tTriv I M p ⟨q, v⟩).2 ≤ ε * ‖(tTriv I M p ⟨q, v⟩).2‖ := by
  have hp : p ∈ (tTriv I M p).baseSet :=
    mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  obtain ⟨e, -⟩ := g.lorentzian p
  let L : ∀ q ∈ (tTriv I M p).baseSet, TangentSpace I q ≃ₗ[ℝ] E :=
    fun q hq => (tTriv I M p).linearEquivAt ℝ q hq
  let ξ : Module.Basis (Fin n) ℝ E := e.map (L p hp)
  have : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  let Y : Fin n → ∀ q : M, TangentSpace I q := fun i q => localField (I := I) p (ξ i) q
  let U : ∀ q : M, TangentSpace I q := localField (I := I) p V
  have hYsymm : ∀ i q (hq : q ∈ (tTriv I M p).baseSet), Y i q = (L q hq).symm (ξ i) := by
    intro i q hq
    exact ((tTriv I M p).linearEquivAt_symm_apply (R := ℝ) q hq (ξ i)).symm
  have hsm : ∀ w : E, ∀ q ∈ (tTriv I M p).baseSet,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
        (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q
          (localField (I := I) p w q)) q := by
    intro w q hq
    exact (((localField_contMDiffOn (I := I) p w).contMDiffAt
      ((tTriv I M p).open_baseSet.mem_nhds hq)).of_le (by norm_num))
  have hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 0
      (fun q ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) q (T.X q)) x₀ :=
    T.contMDiff x₀
  have hbase : (tTriv I M p).baseSet ∈ 𝓝 x₀ := (tTriv I M p).open_baseSet.mem_nhds hx₀
  -- the coefficient functions
  let r : M → Fin n → ℝ := fun q j => g.g q (U q) (Y j q)
  have hr : ContinuousAt r x₀ :=
    continuousAt_pi.2 fun j => continuousAt_metric_apply (hsm V x₀ hx₀) (hsm (ξ j) x₀ hx₀)
  -- expansion of a transported vector
  have hexp : ∀ q (hq : q ∈ (tTriv I M p).baseSet) (w : E),
      g.g q (U q) ((L q hq).symm w) = ∑ j, ξ.repr w j * r q j := by
    intro q hq w
    conv_lhs => rw [← ξ.sum_repr w]
    simp only [map_sum, map_smul, smul_eq_mul, r, hYsymm _ q hq]
  -- the functional
  let Φl : E →ₗ[ℝ] ℝ := ∑ j, r x₀ j • ξ.coord j
  let Φ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap Φl
  have hΦ : ∀ w, Φ w = ∑ j, ξ.repr w j * r x₀ j := by
    intro w; simp [Φ, Φl, mul_comm]
  -- bound on the coordinates
  let Λ : E →L[ℝ] (Fin n → ℝ) := (ξ.equivFun.toContinuousLinearEquiv : E →L[ℝ] (Fin n → ℝ))
  have hΛ : ∀ w, ‖fun j => ξ.repr w j‖ ≤ ‖Λ‖ * ‖w‖ := fun w => Λ.le_opNorm w
  refine ⟨Φ, ?_, ?_⟩
  · intro u
    have hu : (L x₀ hx₀).symm ((tTriv I M p ⟨x₀, u⟩).2) = u := by
      have := (L x₀ hx₀).symm_apply_apply u
      simpa [L, Trivialization.linearEquivAt_apply] using this
    have h := hexp x₀ hx₀ (tTriv I M p ⟨x₀, u⟩).2
    rw [hu] at h
    rw [hΦ]
    exact h.symm
  · set δ : ℝ := ε / (((n : ℝ) + 1) * (‖Λ‖ + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have E2 : ∀ᶠ q in 𝓝 x₀, ∀ j, |r q j - r x₀ j| ≤ δ := by
      refine Filter.eventually_all.2 fun j => ?_
      have : ContinuousAt (fun q => r q j) x₀ := continuousAt_pi.1 hr j
      filter_upwards [this.eventually (Metric.closedBall_mem_nhds (r x₀ j) hδpos)] with q hq
      simpa [Real.dist_eq] using hq
    have E3 : ∀ᶠ q in 𝓝 x₀, g.g q (U q) (U q) < 0 :=
      (continuousAt_metric_apply (hsm V x₀ hx₀) (hsm V x₀ hx₀)).eventually (gt_mem_nhds hV1)
    have E4 : ∀ᶠ q in 𝓝 x₀, g.g q (U q) (T.X q) < 0 :=
      (continuousAt_metric_apply (hsm V x₀ hx₀) hX).eventually (gt_mem_nhds hV2)
    refine ⟨{q | q ∈ (tTriv I M p).baseSet ∧ (∀ j, |r q j - r x₀ j| ≤ δ) ∧
      g.g q (U q) (U q) < 0 ∧ g.g q (U q) (T.X q) < 0}, (show ∀ᶠ q in 𝓝 x₀, q ∈ (tTriv I M p).baseSet from hbase).and (E2.and (E3.and E4)),
      fun q hq => hq.1, ?_⟩
    rintro q ⟨hqb, hq2, hq3, hq4⟩ v ⟨hv0, hvv, hvX⟩
    set w : E := (tTriv I M p ⟨q, v⟩).2 with hw
    have hvw : (L q hqb).symm w = v := by
      have := (L q hqb).symm_apply_apply v
      simpa [L, Trivialization.linearEquivAt_apply, hw] using this
    -- the product of `v` with the transported `V` is nonpositive
    have hprod : ∑ j, ξ.repr w j * r q j ≤ 0 := by
      rw [← hexp q hqb w, hvw]
      have := (g.lorentzian q).nonpos_of_futureCausal (X := T.X q) (T.timelike q) hvv hq3.le hvX hq4
      rwa [g.symm q] at this
    have hbound : ∑ j, ξ.repr w j * (r x₀ j - r q j) ≤ ε * ‖w‖ := by
      calc ∑ j, ξ.repr w j * (r x₀ j - r q j) ≤ ∑ _j : Fin n, (‖Λ‖ * ‖w‖) * δ := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 : |ξ.repr w j| ≤ ‖Λ‖ * ‖w‖ := by
              have := norm_le_pi_norm (fun j => ξ.repr w j) j
              simpa using this.trans (hΛ w)
            have h2 : |r x₀ j - r q j| ≤ δ := by rw [abs_sub_comm]; exact hq2 j
            calc ξ.repr w j * (r x₀ j - r q j) ≤ |ξ.repr w j * (r x₀ j - r q j)| := le_abs_self _
              _ = |ξ.repr w j| * |r x₀ j - r q j| := abs_mul _ _
              _ ≤ (‖Λ‖ * ‖w‖) * δ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = n * (‖Λ‖ * ‖w‖ * δ) := by simp
        _ ≤ ε * ‖w‖ := by
            rw [hδ]
            have hpos : 0 < ((n : ℝ) + 1) * (‖Λ‖ + 1) := by positivity
            have : (n : ℝ) * ‖Λ‖ ≤ ((n : ℝ) + 1) * (‖Λ‖ + 1) := by
              nlinarith [norm_nonneg Λ, Nat.cast_nonneg (α := ℝ) n]
            calc (n : ℝ) * (‖Λ‖ * ‖w‖ * (ε / (((n : ℝ) + 1) * (‖Λ‖ + 1))))
                = ((n : ℝ) * ‖Λ‖) / (((n : ℝ) + 1) * (‖Λ‖ + 1)) * (ε * ‖w‖) := by
                  field_simp
              _ ≤ 1 * (ε * ‖w‖) := by
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  rw [div_le_one hpos]; exact this
              _ = ε * ‖w‖ := one_mul _
    rw [hΦ]
    have : ∑ j, ξ.repr w j * r x₀ j =
        ∑ j, ξ.repr w j * r q j + ∑ j, ξ.repr w j * (r x₀ j - r q j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith

end Lightlike.Causal
