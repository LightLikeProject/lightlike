import Lightlike.Spacetime.PenroseSingularity.VariationIntrinsic
import Lightlike.Spacetime.PenroseSingularity.FlowFamily

/-!
# The intrinsic pairing of the velocity of a curve (G1-012, step D4)

For a map `α : ℝ × ℝ → M`, `pairT g α (s, t)` is `g (∂ₜ α, ∂ₜ α)` at `α (s, t)`, with `∂ₜ α` the manifold derivative
of `t ↦ α (s, t)`. In the chart at `x₀` it is the pairing `gpairAt` of the chart derivative of the chart expression.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The chart derivative of a differentiable curve is the trivialization component of its manifold derivative. -/
theorem deriv_coord (x₀ : M) {f : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) f t)
    (hsrc : f t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    deriv (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f r)) t =
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨f t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) f t 1⟩).2 := by
  rw [tTriv_snd_eq_mfderiv x₀ _ hsrc]
  have hψ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) (f t) :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ, Fin n → ℝ)) (n := 1)
      (by rw [extChartAt_source] at hsrc; exact hsrc)).mdifferentiableAt one_ne_zero
  have hcomp := mfderiv_comp t hψ hf
  have h3 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f r)) t =
      fderiv ℝ (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f r)) t := mfderiv_eq_fderiv
  have h4 := congrArg (fun L => L 1) hcomp
  simp only [Function.comp] at h4
  rw [← fderiv_apply_one_eq_deriv, ← h3]
  exact h4

/-- The pairing of the `t`-velocity of `α` with itself. -/
def pairT (α : ℝ × ℝ → M) (p : ℝ × ℝ) : ℝ :=
  g.g (α p) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (p.1, r)) p.2 1)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (p.1, r)) p.2 1)

/-- **The pairing in a chart.** -/
theorem pairT_eq_chart (x₀ : M) {α : ℝ × ℝ → M} {p : ℝ × ℝ}
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => α (p.1, r)) p.2)
    (hsrc : α p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    pairT g α p = gpairAt (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α p))
      (deriv (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α (p.1, r))) p.2)
      (deriv (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (α (p.1, r))) p.2) := by
  unfold pairT
  rw [g_eq_gpair g x₀ (α p) hsrc, deriv_coord x₀ hα hsrc]

section Variation

variable {p₀ : M} (td : ThetaData g p₀) {U : Set (Fin n → ℝ)} {γ : ℝ → M} {W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t)}
  {V : Set (ℝ × ℝ)}

/-- On the domain of the chart expression, the variation is the inverse chart of `varA`. -/
theorem varT_eq_symm (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    {q : ℝ × ℝ} (hq : q ∈ V) :
    varT g γ W Z q = (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm
      (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t)) q) := by
  rw [← chart_varT g p₀ td γ W Z (hV q hq).1 (hV q hq).2]
  refine ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).left_inv ?_).symm
  have h := (hV q hq).2
  rw [← comp_add_smul p₀ (hV q hq).1] at h
  have h2 := td.exp_mem _ h
  rw [zetaMap_comp p₀ (hV q hq).1] at h2
  exact h2

/-- **The `t`-slice of the intrinsic variation**: it is differentiable, takes values in the chart, and its chart
derivative is `jetY`. -/
theorem varT_slice (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V) {q : ℝ × ℝ} (hq : q ∈ V) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => varT g γ W Z (q.1, r)) q.2 ∧
      varT g γ W Z q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source ∧
      deriv (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (varT g γ W Z (q.1, r))) q.2 =
        jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) q ∧
      extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (varT g γ W Z q) =
        varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t)) q := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set A := varA td.Θ (fun t => ψ (γ t)) (fun t => comp p₀ (W t)) (fun t => comp p₀ (Z t)) with hAdef
  have hcurve : HasDerivAt (fun r : ℝ => ((q.1, r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hAd : DifferentiableAt ℝ A q := (hA.contDiffAt (hVo.mem_nhds hq)).differentiableAt (by simp)
  have hslice : HasDerivAt (fun r => A (q.1, r)) (jetY A q) q.2 := by
    have := hAd.hasFDerivAt.comp_hasDerivAt q.2 hcurve
    exact this
  have hmem : ∀ᶠ r in 𝓝 q.2, ((q.1, r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hVo.mem_nhds hq)
  have hsym : ∀ r, ((q.1, r) : ℝ × ℝ) ∈ V → varT g γ W Z (q.1, r) = ψ.symm (A (q.1, r)) := fun r hr =>
    varT_eq_symm g td hV hr
  have hsrc : ∀ r, ((q.1, r) : ℝ × ℝ) ∈ V → varT g γ W Z (q.1, r) ∈ ψ.source := fun r hr => by
    have h := (hV _ hr).2
    rw [← comp_add_smul p₀ (hV _ hr).1] at h
    have h2 := td.exp_mem _ h
    rw [zetaMap_comp p₀ (hV _ hr).1] at h2
    exact h2
  have hchart : ∀ r, ((q.1, r) : ℝ × ℝ) ∈ V → ψ (varT g γ W Z (q.1, r)) = A (q.1, r) := fun r hr =>
    chart_varT g p₀ td γ W Z (hV _ hr).1 (hV _ hr).2
  have hAt : A q ∈ ψ.target := by
    rw [← hchart q.2 hq]
    exact ψ.map_source (hsrc q.2 hq)
  -- the slice is differentiable as a map to `M`
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => varT g γ W Z (q.1, r)) q.2 := by
    have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun r => A (q.1, r)) q.2 :=
      mdifferentiableAt_iff_differentiableAt.2 hslice.differentiableAt
    have h2 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ.symm (A q) :=
      ((contMDiffOn_extChartAt_symm p₀).contMDiffAt ((isOpen_extChartAt_target p₀).mem_nhds hAt)).mdifferentiableAt
        one_ne_zero
    have h3 := h2.comp q.2 h1
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with r hr using hsym r hr
  have hderiv : deriv (fun r => ψ (varT g γ W Z (q.1, r))) q.2 = jetY A q := by
    refine (hslice.congr_of_eventuallyEq ?_).deriv
    filter_upwards [hmem] with r hr using hchart r hr
  exact ⟨hdiff, hsrc q.2 hq, hderiv, hchart q.2 hq⟩

/-- **The pairing of the `t`-velocity of the intrinsic variation is the chart pairing of `jetY`.** -/
theorem pairT_varT (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V) {q : ℝ × ℝ} (hq : q ∈ V) :
    pairT g (varT g γ W Z) q = gpairAt (g.coordMetric p₀)
      (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t)) q)
      (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t))) q)
      (jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t))) q) := by
  obtain ⟨hdiff, hsrc, hderiv, hchart⟩ := varT_slice g td hVo hV hA hq
  rw [pairT_eq_chart g p₀ hdiff hsrc]
  simp only [hderiv, hchart]

/-- **The `s`-derivative of the intrinsic pairing is `2 g(K, Y)` and its second derivative at `s = 0` is
`2 ·` the second-order coefficient.** -/
theorem pairT_second_deriv (hg : Lightlike.IsCoordMetric (g.coordMetric p₀) U) (hVo : IsOpen V)
    (hV : ∀ q ∈ V, γ q.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet ∧
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ q.2), q.1 • comp p₀ (W q.2) + q.1 ^ 2 • comp p₀ (Z q.2)) ∈ td.D)
    (hA : ContDiffOn ℝ 3 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t))) V)
    (hcU : ∀ q ∈ V, varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
      (fun t => comp p₀ (Z t)) q ∈ U) {t : ℝ} (ht : ((0 : ℝ), t) ∈ V) :
    HasDerivAt (fun s => deriv (fun s' => pairT g (varT g γ W Z) (s', t)) s)
      (2 * coeffK (g.coordMetric p₀) (fun s t => varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t))
          (fun t => comp p₀ (W t)) (fun t => comp p₀ (Z t)) (s, t))
        (fun s t => jetC1 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t))
        (fun s t => jetC2 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t))
        (fun s t => jetY (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t))
        (fun s t => jetY1 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t))
        (fun s t => jetY2 (varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
          (fun t => comp p₀ (Z t))) (s, t)) 0 t) 0 := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set A := varA td.Θ (fun t => ψ (γ t)) (fun t => comp p₀ (W t)) (fun t => comp p₀ (Z t)) with hAdef
  have hJ := fun (q : ℝ × ℝ) (hq : q ∈ V) => hasDerivAt_jets hVo hA hq
  have hmemS : ∀ᶠ s in 𝓝 (0 : ℝ), ((s, t) : ℝ × ℝ) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hVo.mem_nhds ht)
  have hmemS' : ∀ s, ((s, t) : ℝ × ℝ) ∈ V → ∀ᶠ s' in 𝓝 s, ((s', t) : ℝ × ℝ) ∈ V := fun s hs =>
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hVo.mem_nhds hs)
  -- the first derivative
  have hfirst : ∀ s, ((s, t) : ℝ × ℝ) ∈ V →
      HasDerivAt (fun s' => pairT g (varT g γ W Z) (s', t))
        (2 * gpairAt (g.coordMetric p₀) (A (s, t))
          (covK (g.coordMetric p₀) (fun r => A (r, t)) (fun r => jetC1 A (r, t)) (fun r => jetY A (r, t))
            (fun r => jetY1 A (r, t)) s) (jetY A (s, t))) s := by
    intro s hs
    have h := hasDerivAt_normK hg (c := fun r => A (r, t)) (c1 := fun r => jetC1 A (r, t))
      (Y := fun r => jetY A (r, t)) (Y1 := fun r => jetY1 A (r, t)) (s := s) (hJ _ hs).1
      (hJ _ hs).2.2.1 (hcU _ hs)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hmemS' s hs] with s' hs'
    exact pairT_varT g td hVo hV hA hs'
  have hmain := hasDerivAt_normK_second hg (c := fun r => A (r, t)) (c1 := fun r => jetC1 A (r, t))
    (c2 := fun r => jetC2 A (r, t)) (Y := fun r => jetY A (r, t)) (Y1 := fun r => jetY1 A (r, t))
    (Y2 := fun r => jetY2 A (r, t)) (s := 0) (hJ _ ht).1 (hJ _ ht).2.1 (hJ _ ht).2.2.1 (hJ _ ht).2.2.2
    (hcU _ ht)
  refine (hmain.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hmemS] with s hs
    exact (hfirst s hs).deriv
  · unfold coeffK
    simp only [covK]

end Variation

end Lightlike.Penrose
