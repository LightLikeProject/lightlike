import Lightlike.Spacetime.PenroseSingularity.IntrinsicPairing
import Lightlike.Spacetime.PenroseSingularity.FutureLocal

/-!
# The time orientation in a chart (G1-012, step D4)

`orientChart T p₀ y` is the coordinate expression, in the chart at `p₀`, of the time-orientation field `T.X` at the
point with chart coordinates `y`. It is continuous on the chart target.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : Causal.TimeOrientation g)

/-- The chart expression of the time orientation. -/
def orientChart (p₀ : M) (y : Fin n → ℝ) : Fin n → ℝ :=
  comp p₀ (T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y))

/-- The chart expression of the time orientation is continuous on the chart target. -/
theorem continuousAt_orientChart (p₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target) :
    ContinuousAt (orientChart T p₀) y := by
  have hs : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_target hy
  have hb : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := by
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hs
  have hX : Continuous (fun x : M => (⟨x, T.X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) :=
    T.contMDiff.continuous
  have hsymm : ContinuousAt (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y :=
    continuousAt_extChartAt_symm'' (I := 𝓘(ℝ, Fin n → ℝ)) hy
  have h1 : ContinuousAt (fun y' => (⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y',
      T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y')⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) y :=
    hX.continuousAt.comp hsymm
  have hsrc : (⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y, T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y)⟩ :
      TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).source := by
    rw [(Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).mem_source]; exact hb
  have h2 : ContinuousAt (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀)
      (⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y, T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm y)⟩ :
        TangentBundle 𝓘(ℝ, Fin n → ℝ) M) :=
    ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).continuousOn.continuousAt
      ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).open_source.mem_nhds hsrc))
  exact (continuous_snd.continuousAt).comp (h2.comp_of_eq h1 rfl)

/-- The pairing of the `t`-velocity of `α` with the time-orientation field. -/
def futT (α : ℝ × ℝ → M) (p : ℝ × ℝ) : ℝ :=
  g.g (α p) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (p.1, r)) p.2 1) (T.X (α p))

/-- **The future pairing in a chart.** -/
theorem futT_eq_chart (x₀ : M) {α : ℝ × ℝ → M} {p : ℝ × ℝ}
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (p.1, r)) p.2)
    (hsrc : α p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    futT T α p = gpairAt (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α p))
      (deriv (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α (p.1, r))) p.2)
      (orientChart T x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α p))) := by
  unfold futT orientChart
  rw [g_eq_gpair g x₀ (α p) hsrc, deriv_coord x₀ hα hsrc, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hsrc]
  rfl

section Variation

variable {p₀ : M} (td : ThetaData g p₀) {γ : ℝ → M} {W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t)}
  {V : Set (ℝ × ℝ)}

/-- **The future pairing of the intrinsic variation is the chart pairing of `jetY` with `orientChart`.** -/
theorem futT_varT (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V) {q : ℝ × ℝ} (hq : q ∈ V) :
    futT T (varT g γ W Z) q = gpairAt (g.coordMetric p₀)
      (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t)) q)
      (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t))) q)
      (orientChart T p₀ (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t)) q)) := by
  obtain ⟨hdiff, hsrc, hderiv, hchart⟩ := varT_slice g td hVo hV hA hq
  rw [futT_eq_chart T p₀ hdiff hsrc]
  simp only [hderiv, hchart]

/-- **Local future timelike character of the variation.** Near `(0, t₀)`, for `s ≠ 0` small, the `t`-velocity of the
intrinsic variation is future timelike. -/
theorem varT_locally_future_timelike {U : Set (Fin n → ℝ)} (hg : Lightlike.IsCoordMetric (g.coordMetric p₀) U)
    (hVo : IsOpen V)
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
    ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
      pairT g (varT g γ W Z) (s, t) < 0 ∧ futT T (varT g γ W Z) (s, t) < 0 := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set A := varA td.Θ (fun t => ψ (γ t)) (fun t => comp p₀ (W t)) (fun t => comp p₀ (Z t)) with hAdef
  obtain ⟨δ1, hδ1, ε1, hε1, h1⟩ := hneg
  have hcj := continuousAt_jets hVo hA ht
  have hXc : ContinuousAt (orientChart T p₀) (A (0, t₀)) := by
    refine continuousAt_orientChart T p₀ ?_
    obtain ⟨-, hsrc0, -, hch0⟩ := varT_slice g td hVo hV hA ht
    have := (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_source hsrc0
    rw [hch0] at this
    exact this
  obtain ⟨δ2, hδ2, ε2, hε2, h2⟩ := future_local hg (c := fun s t => A (s, t)) (Y := fun s t => jetY A (s, t))
    (Xc := orientChart T p₀) hcj.1 hcj.2.2.2.1 (hcU _ ht) hXc hfut
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hVo.mem_nhds ht)
  refine ⟨min (min δ1 δ2) ρ, lt_min (lt_min hδ1 hδ2) hρ, min (min ε1 ε2) ρ, lt_min (lt_min hε1 hε2) hρ,
    fun t htt s hs hs0 => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ : (|t - t₀| < ε1 ∧ |t - t₀| < ε2) ∧ |t - t₀| < ρ := by simpa using htt
  obtain ⟨⟨b1, b2⟩, b3⟩ : (|s| < δ1 ∧ |s| < δ2) ∧ |s| < ρ := by simpa using hs
  have hsV : ((s, t) : ℝ × ℝ) ∈ V := by
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by simpa using b3) (by simpa using a3)
  refine ⟨?_, ?_⟩
  · rw [pairT_varT g td hVo hV hA hsV]
    exact h1 t a1 s b1 hs0
  · rw [futT_varT T td hVo hV hA hsV]
    exact h2 t a2 s b2

end Variation

end Lightlike.Penrose
