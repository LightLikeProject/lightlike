import Lightlike.Spacetime.PenroseSingularity.NullParallel
import Lightlike.Spacetime.PenroseSingularity.FlowFamily
import Lightlike.Spacetime.PenroseSingularity.VariationIntrinsic

/-!
# Lorentzian algebra for the coordinate pairing (G1-012, step D4)

The coordinate pairing `gpairAt (g.coordMetric p₀) (ψ x)` at a point `x` of the chart at `p₀` is the Lorentzian form
`g.g x` read in the trivialization: null vectors orthogonal to a null vector have non-negative norm, and are
multiples of it when null.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- **The coordinate pairing is the Lorentzian form, read on chart components.** -/
theorem gpairAt_eq_g (p₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source)
    (z z' : Fin n → ℝ) :
    gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) z z' =
      g.g x ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ x z) ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ x z') := by
  have hb : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := by
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  have hc : ∀ u : Fin n → ℝ, comp p₀ (x := x) ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ x u) = u := by
    intro u
    unfold comp
    rw [Bundle.Trivialization.symmL_apply _ hb]
    exact congrArg Prod.snd ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).apply_mk_symm hb u)
  rw [g_eq_gpair g p₀ x hx]
  have := hc z
  have := hc z'
  unfold comp at *
  simp only [*]

/-- The components of the vector with components `u` are `u`. -/
theorem comp_symmL (p₀ x : M) (hb : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet) (u : Fin n → ℝ) :
    comp p₀ (x := x) ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ x u) = u := by
  unfold comp
  rw [Bundle.Trivialization.symmL_apply _ hb]
  exact congrArg Prod.snd ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).apply_mk_symm hb u)

/-- **A vector orthogonal to a null vector has non-negative norm** (chart components). -/
theorem chart_null_orth_nonneg (hnm : n = m + 2) (p₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source)
    {w z : Fin n → ℝ} (hww : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) w w = 0)
    (hw0 : w ≠ 0) (hz : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) z w = 0) :
    0 ≤ gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) z z := by
  subst hnm
  have hb : x ∈ (Causal.tTriv 𝓘(ℝ, Fin (m + 2) → ℝ) M p₀).baseSet := by
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  rw [gpairAt_eq_g g p₀ x hx] at hww hz ⊢
  refine null_orth_nonneg (g.lorentzian x) hww ?_ hz
  intro h0
  apply hw0
  have := comp_symmL p₀ x hb w
  rw [h0] at this
  rw [← this]
  have h00 : comp p₀ (x := x) (0 : TangentSpace 𝓘(ℝ, Fin (m + 2) → ℝ) x) = 0 := by
    rw [comp_eq_linearMapAt p₀ hb]
    exact map_zero _
  exact h00

/-- **A null vector orthogonal to a null vector is a multiple of it** (chart components). -/
theorem chart_null_orth_parallel (hnm : n = m + 2) (p₀ x : M) (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source)
    {w z : Fin n → ℝ} (hww : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) w w = 0)
    (hw0 : w ≠ 0) (hz : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) z w = 0)
    (hzz : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x) z z = 0) :
    ∃ c : ℝ, z = c • w := by
  subst hnm
  have hb : x ∈ (Causal.tTriv 𝓘(ℝ, Fin (m + 2) → ℝ) M p₀).baseSet := by
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hx
  rw [gpairAt_eq_g g p₀ x hx] at hww hz hzz
  have hk0 : (Causal.tTriv 𝓘(ℝ, Fin (m + 2) → ℝ) M p₀).symmL ℝ x w ≠ 0 := by
    intro h0
    apply hw0
    have := comp_symmL p₀ x hb w
    rw [h0] at this
    rw [← this]
    rw [comp_eq_linearMapAt p₀ hb]
    exact map_zero _
  obtain ⟨c, hc⟩ := eq_smul_of_null_orth (g.lorentzian x) hww hk0 hz hzz
  refine ⟨c, ?_⟩
  have h1 := congrArg (comp p₀ (x := x)) hc
  rw [comp_symmL p₀ x hb] at h1
  rw [comp_eq_linearMapAt p₀ hb, map_smul, ← comp_eq_linearMapAt p₀ hb, comp_symmL p₀ x hb] at h1
  exact h1

end Lightlike.Penrose
