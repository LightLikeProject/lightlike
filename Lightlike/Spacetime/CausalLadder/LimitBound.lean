import Lightlike.Spacetime.CausalLadder.ReparamCurve
import Lightlike.Spacetime.CausalLadder.FunctionalEstimate

/-!
# The frozen functional bound for reparametrised causal curves

Combine `exists_functional_estimate` (a one-sided bound of the future causal cone by the metric
frozen at `x₀`) with `sub_le_sub_reparam` (monotonicity along a causal curve in the reparametrised
variable): near `x₀` every reparametrised causal curve satisfies
`Φ (f σ₂ - f σ₁) ≤ ε (σ₂ - σ₁)`, as long as it stays within a fixed radius of the chart image of
`x₀` on `[σ₁, σ₂]`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Frozen functional bound along reparametrised causal curves.** Let `ℓ`, `C` satisfy the cone
estimate `‖w‖ ≤ C ℓ w` on a neighbourhood `W` of `x₀`. For a vector `V` that is future timelike at
`x₀` and `ε > 0` there are a functional `Φ`, with `Φ w = g_{x₀}(V, w)` in the coordinates of the
trivialization at `p`, and a radius `r > 0` such that the following holds for every future causal
curve `γ` on `[a, b]` with values in `W`, every reparametrisation `f` of its chart image through
`ℓ`, and all `ℓ`-values `σ₁ ≤ σ₂` of the curve: if `‖f σ - extChartAt p x₀‖ < r` for
`σ ∈ [σ₁, σ₂]` then `Φ (f σ₂) - Φ (f σ₁) ≤ ε (σ₂ - σ₁)`. -/
theorem exists_reparam_bound (p x₀ : M) (hx₀ : x₀ ∈ (tTriv I M p).baseSet) (V : E)
    (hV1 : g.g x₀ (localField (I := I) p V x₀) (localField (I := I) p V x₀) < 0)
    (hV2 : g.g x₀ (localField (I := I) p V x₀) (T.X x₀) < 0) {ε : ℝ} (hε : 0 < ε)
    {W : Set M} (hWb : W ⊆ (tTriv I M p).baseSet) {ℓ : E →L[ℝ] ℝ} {C : ℝ} (hC : 0 < C)
    (hcone : ∀ q ∈ W, ∀ v : TangentSpace I q, T.IsFutureCausal v →
      ‖(tTriv I M p ⟨q, v⟩).2‖ ≤ C * ℓ (tTriv I M p ⟨q, v⟩).2) (hW : W ∈ 𝓝 x₀) :
    ∃ Φ : E →L[ℝ] ℝ, (∀ u : TangentSpace I x₀, Φ (tTriv I M p ⟨x₀, u⟩).2 =
        g.g x₀ (localField (I := I) p V x₀) u) ∧
      ∃ r > 0, ∀ {γ : ℝ → M} {a b : ℝ} (_ : IsFutureCausalCurve T γ (Icc a b)),
        (∀ t ∈ Icc a b, γ t ∈ W) →
        (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
          ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t))) →
        ∀ {f : ℝ → E}, (∀ t ∈ Icc a b, f (ℓ (extChartAt I p (γ t))) = extChartAt I p (γ t)) →
        ∀ {σ₁ σ₂ : ℝ}, σ₁ ≤ σ₂ → (∃ t ∈ Icc a b, ℓ (extChartAt I p (γ t)) = σ₁) →
        (∃ t ∈ Icc a b, ℓ (extChartAt I p (γ t)) = σ₂) →
        (∀ t ∈ Icc a b, σ₁ ≤ ℓ (extChartAt I p (γ t)) → ℓ (extChartAt I p (γ t)) ≤ σ₂ →
          ‖extChartAt I p (γ t) - extChartAt I p x₀‖ < r) →
        Φ (f σ₂) - Φ (f σ₁) ≤ ε * (σ₂ - σ₁) := by
  obtain ⟨Φ, hΦ, N, hN, hNb, hbound⟩ :=
    exists_functional_estimate T p x₀ hx₀ V hV1 hV2 (ε := ε / C) (by positivity)
  refine ⟨Φ, hΦ, ?_⟩
  -- a radius in the chart such that chart points in the target within `r` come from `N ∩ W`
  have hNW : N ∩ W ∈ 𝓝 x₀ := inter_mem hN hW
  have hpre : (extChartAt I p).symm ⁻¹' (N ∩ W) ∈ 𝓝[(extChartAt I p).target] (extChartAt I p x₀) := by
    have hx0src : x₀ ∈ (extChartAt I p).source := by rw [extChartAt_source]; exact hx₀
    have hcont := (continuousOn_extChartAt_symm p) (extChartAt I p x₀)
      ((extChartAt I p).map_source hx0src)
    refine hcont.preimage_mem_nhdsWithin ?_
    rw [(extChartAt I p).left_inv hx0src]; exact hNW
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨r, hr, ?_⟩
  intro γ a b hγ hmem hmono f hf σ₁ σ₂ h12 h1 h2 hball
  have hFG : ∀ q ∈ N ∩ W, ∀ v : TangentSpace I q, T.IsFutureCausal v →
      Φ (tTriv I M p ⟨q, v⟩).2 ≤ (ε • ℓ) (tTriv I M p ⟨q, v⟩).2 := by
    intro q hq v hv
    have h1 := hbound q hq.1 v hv
    have h2 := hcone q hq.2 v hv
    simp only [smul_apply, smul_eq_mul]
    calc Φ _ ≤ ε / C * ‖(tTriv I M p ⟨q, v⟩).2‖ := h1
      _ ≤ ε / C * (C * ℓ (tTriv I M p ⟨q, v⟩).2) := by gcongr
      _ = ε * ℓ (tTriv I M p ⟨q, v⟩).2 := by field_simp
  have := sub_le_sub_reparam T p (W := N ∩ W) (fun q hq => hWb hq.2) Φ (ε • ℓ) hFG hγ hmono hf
    h12 h1 h2 (fun t ht hl1 hl2 => by
      have hb := hball t ht hl1 hl2
      have hsrc : γ t ∈ (extChartAt I p).source := by rw [extChartAt_source]; exact hWb (hmem t ht)
      have hmaps : extChartAt I p (γ t) ∈ (extChartAt I p).target :=
        (extChartAt I p).map_source hsrc
      have h3 : (extChartAt I p).symm (extChartAt I p (γ t)) ∈ N ∩ W :=
        hrsub ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hb, hmaps⟩
      rwa [(extChartAt I p).left_inv hsrc] at h3)
  simp only [smul_apply, smul_eq_mul] at this
  have hℓ1 : ℓ (f σ₁) = σ₁ := by
    obtain ⟨t, ht, e⟩ := h1
    rw [← e, hf t ht]
  have hℓ2 : ℓ (f σ₂) = σ₂ := by
    obtain ⟨t, ht, e⟩ := h2
    rw [← e, hf t ht]
  rw [hℓ1, hℓ2] at this
  linarith

end Lightlike.Causal
