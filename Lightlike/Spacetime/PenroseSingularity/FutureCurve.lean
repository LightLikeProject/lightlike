import Lightlike.Spacetime.PenroseSingularity.FutureChart
import Lightlike.Spacetime.PenroseSingularity.UniformCompact

/-!
# The slices of the intrinsic variation are `C¹` curves (G1-012, step D4)

Near a point `q` of the chart domain `V`, `t ↦ varT g γ W Z (q.1, t)` is the inverse chart of a `C³` map, hence a
`C¹` map into `M`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : Causal.TimeOrientation g)
  {p₀ : M} (td : ThetaData g p₀) {γ : ℝ → M} {W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t)}
  {V : Set (ℝ × ℝ)}

/-- **The `t`-slices of the intrinsic variation are `C¹` maps into `M`.** -/
theorem contMDiffAt_varT_slice (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V) {q : ℝ × ℝ} (hq : q ∈ V) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (fun r => varT g γ W Z (q.1, r)) q.2 := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set A := varA td.Θ (fun t => ψ (γ t)) (fun t => comp p₀ (W t)) (fun t => comp p₀ (Z t)) with hAdef
  obtain ⟨-, hsrc, -, hch⟩ := varT_slice g td hVo hV hA hq
  have hAt : A q ∈ ψ.target := by
    have := ψ.map_source hsrc
    rw [hch] at this
    exact this
  have hmem : ∀ᶠ r in 𝓝 q.2, ((q.1, r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hVo.mem_nhds hq)
  have hAq : ContDiffAt ℝ 3 A ((q.1, q.2) : ℝ × ℝ) := hA.contDiffAt (hVo.mem_nhds hq)
  have hc : ContDiffAt ℝ 3 (fun r : ℝ => ((q.1, r) : ℝ × ℝ)) q.2 :=
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ 3 (fun r : ℝ => ((q.1, r) : ℝ × ℝ))).contDiffAt
  have hAd : ContDiffAt ℝ 3 (fun r => A (q.1, r)) q.2 :=
    ContDiffAt.comp (g := A) (f := fun r : ℝ => ((q.1, r) : ℝ × ℝ)) q.2 hAq hc
  have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (fun r => A (q.1, r)) q.2 :=
    (hAd.of_le (by norm_num)).contMDiffAt
  have h2' : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm (A q) :=
    (contMDiffOn_extChartAt_symm p₀).contMDiffAt ((isOpen_extChartAt_target p₀).mem_nhds hAt)
  have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) 1 ψ.symm (A q) :=
    h2'.of_le (by exact_mod_cast le_top)
  have h3 := h2.comp q.2 h1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with r hr using varT_eq_symm g td hV hr

/-- **A `C¹` slice with future timelike velocity is a future timelike curve.** -/
theorem isFutureTimelikeCurve_slice {α : ℝ × ℝ → M} {s a b : ℝ} (hab : a < b)
    (hC : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (fun r => α (s, r)) t)
    (hp : ∀ t ∈ Icc a b, pairT g α (s, t) < 0 ∧ futT T α (s, t) < 0) :
    Causal.IsFutureTimelikeCurve T (fun r => α (s, r)) (Icc a b) := by
  refine Causal.isFutureTimelikeCurve_of_contMDiffOn T hab (fun t ht => (hC t ht).contMDiffWithinAt) ?_
  intro t ht
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (s, r)) t :=
    (hC t ht).mdifferentiableAt one_ne_zero
  have hU : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 (uniqueDiffOn_Icc hab t ht)
  have hv : Causal.velocity 𝓘(ℝ, Fin n → ℝ) (fun r => α (s, r)) (Icc a b) t =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (s, r)) t 1 := by
    unfold Causal.velocity
    rw [mfderivWithin_eq_mfderiv hU hd]
    rfl
  rw [hv]
  exact hp t ht

/-- **The local property at `t₀`:** for small `s ≠ 0` and `t` near `t₀`, the slice `r ↦ α (s, r)` is `C¹` at `t` with
future timelike velocity. -/
def LocalFT (α : ℝ × ℝ → M) (t₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (fun r => α (s, r)) t ∧
      pairT g α (s, t) < 0 ∧ futT T α (s, t) < 0

/-- **`LocalFT` for the intrinsic variation from chart data at `t₀`.** -/
theorem localFT_varT {U : Set (Fin n → ℝ)} (hg : Lightlike.IsCoordMetric (g.coordMetric p₀) U) (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V)
    (hcU : ∀ q ∈ V, varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t)) q ∈ U) {t₀ : ℝ} (ht : ((0 : ℝ), t₀) ∈ V)
    (hneg : ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
      gpairAt (g.coordMetric p₀)
        (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t)) (s, t))
        (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t))
        (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t)) < 0)
    (hfut : gpairAt (g.coordMetric p₀)
        (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t)) (0, t₀))
        (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (0, t₀))
        (orientChart T p₀ (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t)) (0, t₀))) < 0) :
    LocalFT T (varT g γ W Z) t₀ := by
  obtain ⟨δ, hδ, ε, hε, h⟩ := varT_locally_future_timelike T td hg hVo hV hA hcU ht hneg hfut
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hVo.mem_nhds ht)
  refine ⟨min δ ρ, lt_min hδ hρ, min ε ρ, lt_min hε hρ, fun t htt s hs hs0 => ?_⟩
  obtain ⟨a1, a2⟩ : |t - t₀| < ε ∧ |t - t₀| < ρ := by simpa using htt
  obtain ⟨b1, b2⟩ : |s| < δ ∧ |s| < ρ := by simpa using hs
  have hsV : ((s, t) : ℝ × ℝ) ∈ V := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by simpa using b2) (by simpa using a2)
  exact ⟨contMDiffAt_varT_slice td hVo hV hA hsV, h t a1 s b1 hs0⟩

/-- **A compact piece.** If `LocalFT` holds at every point of `[a, b]`, then for all small `s ≠ 0` the slice is a
future timelike curve on `[a, b]`. -/
theorem exists_delta_futureTimelikeCurve {α : ℝ × ℝ → M} {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Icc a b, LocalFT T α t) :
    ∃ δ > 0, ∀ s, |s| < δ → s ≠ 0 →
      Causal.IsFutureTimelikeCurve T (fun r => α (s, r)) (Icc a b) := by
  obtain ⟨δ, hδ, hP⟩ := exists_uniform_delta (P := fun s t =>
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 (fun r => α (s, r)) t ∧
      pairT g α (s, t) < 0 ∧ futT T α (s, t) < 0) (a := a) (b := b) h
  refine ⟨δ, hδ, fun s hs hs0 => isFutureTimelikeCurve_slice T hab
    (fun t ht => (hP t ht s hs hs0).1) (fun t ht => (hP t ht s hs hs0).2)⟩

end Lightlike.Penrose
