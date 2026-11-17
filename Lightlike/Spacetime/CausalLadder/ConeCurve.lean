import Lightlike.Spacetime.CausalLadder.ConeEstimate
import Lightlike.Spacetime.CausalLadder.ChartLipschitz
import Lightlike.Spacetime.CausalLadder.ChartVelocity
import Lightlike.Spacetime.CausalLadder.LipschitzMono

/-!
# Chart cone estimate for future causal curves

Near a point `p`, a future-directed causal curve that stays in a small neighbourhood `W` has chart
coordinates `c = extChartAt I p ∘ γ` for which one fixed linear functional `ℓ` is nondecreasing and
controls the displacement: `‖c t - c s‖ ≤ C (ℓ (c t) - ℓ (c s))` for `s ≤ t`.

The proof combines the local cone estimate (`exists_cone_estimate`), the chart derivative of a
curve (`hasDerivWithinAt_chart_comp`), Lipschitz continuity in the chart at `p`
(`exists_lipschitzOnWith_chart_comp`) and the fundamental theorem of calculus for Lipschitz
functions (`sub_le_sub_of_ae_deriv_le`).

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Chart cone estimate for causal curves.** Around `p` there are a neighbourhood `W`, a
continuous linear functional `ℓ` and a constant `C` such that for every future-directed causal curve
`γ` on `[a, b]` with values in `W` and all `s ≤ t` in `[a, b]`, in the chart at `p`
`ℓ (c s) ≤ ℓ (c t)` and `‖c t - c s‖ ≤ C (ℓ (c t) - ℓ (c s))`, where `c = extChartAt I p ∘ γ`. -/
theorem exists_cone_estimate_curve (p : M) :
    ∃ W ∈ 𝓝 p, ∃ (ℓ : E →L[ℝ] ℝ) (C : ℝ), 0 < C ∧
      ∀ (γ : ℝ → M) (a b : ℝ), IsFutureCausalCurve T γ (Icc a b) → (∀ t ∈ Icc a b, γ t ∈ W) →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
          ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t)) ∧
          ‖extChartAt I p (γ t) - extChartAt I p (γ s)‖ ≤
            C * (ℓ (extChartAt I p (γ t)) - ℓ (extChartAt I p (γ s))) := by
  obtain ⟨W, hW, hWb, ℓ, C, hC, hcone⟩ := exists_cone_estimate T p
  refine ⟨W, hW, ℓ, C, hC, ?_⟩
  intro γ a b hγ hmem s hs t ht hst
  have hsrc : ∀ u ∈ Icc a b, γ u ∈ (extChartAt I p).source := fun u hu => by
    rw [extChartAt_source]; exact hWb (hmem u hu)
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_chart_comp hγ.lipschitz p hsrc
  have hae := hγ.ae_velocity
  rw [ae_restrict_iff' measurableSet_Icc] at hae
  have key : ∀ᵐ u, u ∈ Ioo a b → ∃ w : E, HasDerivAt (extChartAt I p ∘ γ) w u ∧
      ‖w‖ ≤ C * ℓ w := by
    filter_upwards [hae] with u hu hum
    have hmem' : u ∈ Icc a b := Ioo_subset_Icc_self hum
    obtain ⟨hdiff, hP⟩ := hu hmem'
    have hd := hasDerivWithinAt_chart_comp (I := I) p hdiff (hsrc u hmem')
    have hd' : HasDerivAt (extChartAt I p ∘ γ) _ u :=
      hd.hasDerivAt (Icc_mem_nhds hum.1 hum.2)
    refine ⟨_, hd', ?_⟩
    exact hcone (γ u) (hmem u hmem') _ hP
  have mono : ∀ F G : E →L[ℝ] ℝ, (∀ w : E, ‖w‖ ≤ C * ℓ w → F w ≤ G w) →
      F (extChartAt I p (γ t)) - F (extChartAt I p (γ s)) ≤
        G (extChartAt I p (γ t)) - G (extChartAt I p (γ s)) := by
    intro F G hFG
    have hst' : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hlip : ∀ F : E →L[ℝ] ℝ, LipschitzOnWith (‖F‖₊ * K) (F ∘ (extChartAt I p ∘ γ)) (Icc s t) :=
      fun F => (F.lipschitzWith.comp_lipschitzOnWith (hK.mono hst'))
    refine sub_le_sub_of_ae_deriv_le hst (hlip F) (hlip G) ?_
    filter_upwards [key] with u hu hum
    obtain ⟨w, hw, hwC⟩ := hu ⟨lt_of_le_of_lt hs.1 hum.1, lt_of_lt_of_le hum.2 ht.2⟩
    have h1 := F.hasFDerivAt.comp_hasDerivAt u hw
    have h2 := G.hasFDerivAt.comp_hasDerivAt u hw
    exact ⟨h1.differentiableAt, h2.differentiableAt, by rw [h1.deriv, h2.deriv]; exact hFG w hwC⟩
  have hℓ0 : ∀ w : E, ‖w‖ ≤ C * ℓ w → 0 ≤ ℓ w := fun w hw =>
    nonneg_of_mul_nonneg_right (le_trans (norm_nonneg w) hw) hC
  have h1 := mono 0 ℓ (fun w hw => by simpa using hℓ0 w hw)
  simp only [zero_apply, sub_self] at h1
  refine ⟨by linarith, ?_⟩
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ (extChartAt I p (γ t) - extChartAt I p (γ s))
  have h2 := mono φ (C • ℓ) (fun w hw => by
    have : φ w ≤ ‖w‖ := (le_abs_self _).trans ((φ.le_opNorm w).trans (by nlinarith [norm_nonneg w]))
    simpa using this.trans hw)
  rw [map_sub] at hφx
  replace hφx : φ (extChartAt I p (γ t)) - φ (extChartAt I p (γ s)) =
      ‖extChartAt I p (γ t) - extChartAt I p (γ s)‖ := by exact_mod_cast hφx
  simp only [smul_apply, smul_eq_mul] at h2
  rw [mul_sub]
  linarith

end Lightlike.Causal
