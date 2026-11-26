import Lightlike.Spacetime.PenroseSingularity.ChartMaster
import Lightlike.Spacetime.PenroseSingularity.FutureCurve

/-!
# The local package at a time `t₀` (G1-012, step D4)

Chart hypotheses on the fields `W`, `Z = φ N + Z⊥` along a null geodesic, at one time `t₀` and in one chart, give the
local future timelike property `LocalFT` of the intrinsic variation.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : Causal.TimeOrientation g)

/-- **`LocalFT` from chart data at `t₀`.** -/
theorem localFT_of_package {p₀ : M} (td : ThetaData g p₀) {γ : ℝ → M}
    {W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t)} {φ : ℝ → ℝ} {N Zp : ℝ → Fin n → ℝ} {I' : Set ℝ}
    {t₀ φ' κ : ℝ} (hI' : IsOpen I') (ht₀ : t₀ ∈ I')
    (hbase : ∀ t ∈ I', γ t ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    (hγs : ContDiffOn ℝ 3 (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) I')
    (hWs : ContDiffOn ℝ 3 (fun t => comp p₀ (W t)) I') (hZs : ContDiffOn ℝ 3 (fun t => comp p₀ (Z t)) I')
    (hD : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀), (0 : Fin n → ℝ)) ∈ td.D)
    (hgeo : HasDerivAt (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)))
      (Lightlike.Geodesic.accel (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀))
        (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t₀)) t₀)
    (hnull : ∀ᶠ t in 𝓝 t₀, gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t))
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t)
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t) = 0)
    (hperp : ∀ᶠ t in 𝓝 t₀, gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t))
      (deriv (fun t => comp p₀ (W t)) t + Lightlike.Geodesic.gammaApply (g.coordMetric p₀)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (comp p₀ (W t))
        (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t))
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t) = 0)
    (hfut : gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀))
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t₀)
      (orientChart T p₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀))) < 0)
    (hN : ∀ᶠ r in 𝓝 t₀, gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ r)) (N r)
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) r) = -1)
    (hZp : ∀ᶠ r in 𝓝 t₀, gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ r)) (Zp r)
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) r) = 0)
    (hZ : ∀ᶠ r in 𝓝 t₀, comp p₀ (Z r) = φ r • N r + Zp r)
    (hφ : HasDerivAt φ φ' t₀) (hκ : 0 < κ)
    (hode : φ' = (1 / 2 : ℝ) * bQ (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀))
      (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t₀) (comp p₀ (W t₀))
      (deriv (fun t => comp p₀ (W t)) t₀ + Lightlike.Geodesic.gammaApply (g.coordMetric p₀)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t₀)) (comp p₀ (W t₀))
        (deriv (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) t₀)) + κ) :
    LocalFT T (varT g γ W Z) t₀ := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set γc : ℝ → Fin n → ℝ := fun t => ψ (γ t) with hγc
  set Wc : ℝ → Fin n → ℝ := fun t => comp p₀ (W t) with hWc
  set Zc : ℝ → Fin n → ℝ := fun t => comp p₀ (Z t) with hZc
  have hgU : Lightlike.IsCoordMetric (g.coordMetric p₀) ψ.target :=
    g.toNondegMetric.isCoordMetric_coordMetric p₀
  obtain ⟨hVo, hA⟩ := varA_smooth td.isOpen td.smooth hI' hγs hWs hZs
  set V := varV td.D I' γc Wc Zc with hV
  have hp : ((0 : ℝ), t₀) ∈ V := by
    refine ⟨ht₀, ?_⟩
    simpa using hD
  have hVD : ∀ q ∈ V, (γc q.2, q.1 • Wc q.2 + q.1 ^ 2 • Zc q.2) ∈ td.D := fun q hq => hq.2
  have hV' : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (ψ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D := fun q hq =>
    ⟨hbase _ hq.1, hq.2⟩
  have hcU : ∀ q ∈ V, varA td.Θ γc Wc Zc q ∈ ψ.target := by
    intro q hq
    have hq' := hVD q hq
    have h1 := td.exp_eq _ hq'
    have h2 := td.exp_mem _ hq'
    unfold varA
    rw [h1]
    exact ψ.map_source h2
  have hneg := chart_neg_master (U := ψ.target) (φ := φ) (N := N) (Zp := Zp) (φ' := φ') (κ := κ) hgU hVo td.isOpen
    td.smooth hA td.zero td.jet1 td.jet2 hVD hcU hp hgeo hnull hperp hN hZp hZ hφ hκ hode
  have hjY : jetY (varA td.Θ γc Wc Zc) (0, t₀) = deriv γc t₀ :=
    (hasDerivAt_curve_of_jetY hVo hA td.zero hVD hp).deriv.symm
  have h0 : varA td.Θ γc Wc Zc (0, t₀) = γc t₀ := by
    have := varA_zero_section (Θ := td.Θ) (γc := γc) (W := Wc) (Z := Zc) (V := V) (D := td.D) td.zero hVD hp
    exact this
  refine localFT_varT T td hgU hVo hV' hA hcU hp hneg ?_
  rw [h0, hjY]
  exact hfut

end Lightlike.Penrose
