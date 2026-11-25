import Lightlike.Spacetime.PenroseSingularity.ExpGerm
import Lightlike.Spacetime.PenroseSingularity.ExpIntrinsic
import Lightlike.Spacetime.PenroseSingularity.GeodesicChartConverse
import Lightlike.Spacetime.PenroseSingularity.JacobiVarChart
import Lightlike.Spacetime.PenroseSingularity.FormContinuity

/-!
# The exponential map in a chart: smoothness and the two-jet along rays (G1-012, step D4)

`Θ (q, w) = ψ (Ξ ⟨ψ⁻¹ q, e⁻¹ w⟩)` is smooth near `(ψ p₀, 0)`, `Θ (q, 0) = q`, `D_w Θ (q, 0) = id` and
`D_w² Θ (q, 0) (w, w) = -Γ (q) (w, w)` (the geodesic equation of the coordinate metric of the chart at `p₀`).
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- A real function of one variable that agrees on `(0, δ)` with a function that is continuous at `0` has the
same limit; for functions continuous at `0` that agree on `(0, δ)`, the values at `0` agree. -/
theorem eq_at_zero_of_eq_right {f h : ℝ → (Fin n → ℝ)} {δ : ℝ} (hδ : 0 < δ) (hf : ContinuousAt f 0)
    (hh : ContinuousAt h 0) (heq : ∀ c ∈ Ioo 0 δ, f c = h c) : f 0 = h 0 := by
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) := hh.tendsto.mono_left nhdsWithin_le_nhds
  have h3 : f =ᶠ[𝓝[>] 0] h := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with c hc using heq c hc
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-- **A ray in the chart is a chart geodesic**: for a base vector `c₁ w` whose segment to `0` stays in the domain
of the flow germ, `τ ↦ ψ (Γ ⟨ψ⁻¹ q, τ e⁻¹ (c₁ w)⟩ 1)` agrees on `(0, min η 1)` with a chart geodesic `C` with
`C 0 = q` and `C' 0 = c₁ w`. -/
theorem theta_ray (p₀ : M) {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (1 + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    {q v : Fin n → ℝ} (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target)
    (hray : ∀ τ ∈ Ioc (0 : ℝ) 1, zetaMap (n := n) p₀ (q, τ • v) ∈ N) (hz0 : zetaMap (n := n) p₀ (q, v) ∈ N) :
    ∃ (C C1 : ℝ → Fin n → ℝ) (η : ℝ), 0 < η ∧ C 0 = q ∧ C1 0 = v ∧
      (∀ τ ∈ Ioo (-η) η, HasDerivAt C (C1 τ) τ ∧
        HasDerivAt C1 (Lightlike.Geodesic.accel (g.coordMetric p₀) (C τ) (C1 τ)) τ) ∧
      ∀ τ ∈ Ioo (0 : ℝ) (min η 1), (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀) (Γ (zetaMap (n := n) p₀ (q, τ • v)) 1) = C τ := by
  classical
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  have hbase : ψ.symm q ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := by
    have hs : ψ.symm q ∈ ψ.source := ψ.map_target hq
    have hs' : ψ.symm q ∈ (chartAt (Fin n → ℝ) p₀).source := by
      have := hs; rw [hψ, extChartAt_source] at this; exact this
    exact (by simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet] using hs')
  set z₁ := zetaMap (n := n) p₀ (q, v) with hz₁
  obtain ⟨hγ, hph⟩ := hgeo _ hz0
  set γt := Γ z₁ with hγt
  have hγ0 : γt 0 = ψ.symm q := by
    have := congrArg Bundle.TotalSpace.proj hph
    rw [hz₁, zetaMap_eq p₀ (q, v) hbase] at this
    exact this
  have hcont : ContinuousAt γt 0 := IsGeodesicCurveOn.continuousAt g hγ (show (0:ℝ) ∈ Ioo (-ε) (1 + ε) from ⟨by linarith, by linarith⟩)
  have hsrc : ∀ᶠ τ in 𝓝 (0 : ℝ), γt τ ∈ ψ.source ∧ τ ∈ Ioo (-ε) (1 + ε) := by
    refine (hcont.eventually (isOpen_extChartAt_source p₀ |>.mem_nhds (by rw [hγ0]; exact ψ.map_target hq))).and ?_
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨η₀, hη₀, hball⟩ := Metric.eventually_nhds_iff.1 hsrc
  set η := min η₀ ε with hη
  have hηpos : 0 < η := lt_min hη₀ hε
  have hηO : ∀ τ ∈ Ioo (-η) η, γt τ ∈ ψ.source := fun τ hτ =>
    (hball (by rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le (abs_lt.2 ⟨hτ.1, hτ.2⟩) (min_le_left _ _))).1
  have hgeoO : IsGeodesicCurveOn g γt (Ioo (-η) η) := hγ.mono fun τ hτ =>
    ⟨by linarith [hτ.1, min_le_right η₀ ε], by linarith [hτ.2, min_le_right η₀ ε]⟩
  obtain ⟨w, hw⟩ := geodesicOn_chart_of_curve g p₀ isOpen_Ioo hηO hgeoO
  have h00 : (0 : ℝ) ∈ Ioo (-η) η := ⟨by linarith, hηpos⟩
  have hpc := phase_coord g p₀ isOpen_Ioo hηO hw h00
  have hw0 : w 0 = v := by
    rw [← hpc.2, hph, hz₁, tTriv_zetaMap p₀ q v hbase]
  refine ⟨fun τ => ψ (γt τ), w, η, hηpos, ?_, hw0, fun τ hτ => ⟨hw.pos τ hτ, hw.vel τ hτ⟩, ?_⟩
  · show ψ (γt 0) = q
    rw [hγ0]; exact ψ.right_inv hq
  · intro τ hτ
    have hτ1 : τ ≤ 1 := le_trans hτ.2.le (min_le_right _ _)
    have hz' := hray τ ⟨hτ.1, hτ1⟩
    have hsm := zetaMap_smul p₀ q v τ hbase
    have hflow := flow_smul g hε hgeo (p := z₁.proj) (v := z₁.snd) (c := τ) hτ.1 hτ1 hz0
      (by rw [← hsm]; exact hz')
    show ψ (Γ (zetaMap p₀ (q, τ • v)) 1) = ψ (γt τ)
    rw [hsm]
    exact congrArg ψ hflow

/-- **The jets of `Θ` along the fibre at `(q, 0)`.** -/
theorem theta_jets (p₀ : M) {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (1 + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    {D : Set ((Fin n → ℝ) × (Fin n → ℝ))} {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ}
    (hDo : IsOpen D) (hDN : ∀ x ∈ D, zetaMap (n := n) p₀ x ∈ N)
    (hΘ : ∀ x, Θ x = extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (Γ (zetaMap (n := n) p₀ x) 1))
    (hsm : ContDiffOn ℝ ∞ Θ D) {q : Fin n → ℝ} (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target)
    (hq0 : (q, (0 : Fin n → ℝ)) ∈ D) (w : Fin n → ℝ) :
    fderiv ℝ Θ (q, 0) (0, w) = w ∧
      fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) = Lightlike.Geodesic.accel (g.coordMetric p₀) q w := by
  classical
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  by_cases hw0 : w = 0
  · subst hw0
    have hacc : Lightlike.Geodesic.accel (g.coordMetric p₀) q (0 : Fin n → ℝ) = 0 := by
      have := Lightlike.Geodesic.accel_smul (g.coordMetric p₀) q 0 (0 : Fin n → ℝ)
      simpa using this
    refine ⟨?_, ?_⟩
    · show fderiv ℝ Θ (q, 0) 0 = 0
      exact map_zero _
    · rw [hacc]
      show fderiv ℝ (fderiv ℝ Θ) (q, 0) 0 0 = 0
      rw [map_zero]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hDo (q, 0) hq0
  set c₁ : ℝ := r / (2 * (‖w‖ + 1)) with hc₁
  have hwp : 0 < ‖w‖ + 1 := by positivity
  have hc₁pos : 0 < c₁ := by positivity
  have hc₁w : c₁ * ‖w‖ < r := by
    rw [hc₁, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  have hseg : ∀ c : ℝ, |c| ≤ c₁ → (q, c • w) ∈ D := by
    intro c hc
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, dist_zero_right, norm_smul, Real.norm_eq_abs]
    exact max_lt hr (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) hc₁w)
  set v : Fin n → ℝ := c₁ • w with hv
  have hray : ∀ τ ∈ Ioc (0 : ℝ) 1, zetaMap (n := n) p₀ (q, τ • v) ∈ N := by
    intro τ hτ
    apply hDN
    have e : τ • v = (τ * c₁) • w := by rw [hv, smul_smul]
    rw [e]
    apply hseg
    rw [abs_of_pos (mul_pos hτ.1 hc₁pos)]
    nlinarith [hτ.2, hc₁pos]
  have hz0 : zetaMap (n := n) p₀ (q, v) ∈ N := by
    have := hray 1 ⟨one_pos, le_rfl⟩; simpa using this
  obtain ⟨C, C1, η, hη, hC0, hC10, hCg, hrel⟩ := theta_ray g p₀ hε hgeo hq hray hz0
  set ρ : ℝ := c₁ * min η 1 with hρ
  have hρpos : 0 < ρ := mul_pos hc₁pos (lt_min hη one_pos)
  have hρc : ρ ≤ c₁ := by
    have := min_le_right η 1
    nlinarith
  set F : ℝ → Fin n → ℝ := fun c => Θ (q, c • w) with hF
  set Fd : ℝ → Fin n → ℝ := fun c => fderiv ℝ Θ (q, c • w) (0, w) with hFd
  set Fdd : ℝ → Fin n → ℝ := fun c => fderiv ℝ (fderiv ℝ Θ) (q, c • w) (0, w) (0, w) with hFdd
  have hcurve : ∀ c : ℝ, HasDerivAt (fun c : ℝ => ((q, c • w) : (Fin n → ℝ) × (Fin n → ℝ)))
      ((0 : Fin n → ℝ), w) c := fun c =>
    (hasDerivAt_const c q).prodMk (by simpa using (hasDerivAt_id c).smul_const w)
  have hΘd : ∀ x ∈ D, DifferentiableAt ℝ Θ x := fun x hx =>
    (hsm.differentiableOn (by simp)).differentiableAt (hDo.mem_nhds hx)
  have hΘ2 : ContDiffOn ℝ ∞ (fderiv ℝ Θ) D := hsm.fderiv_of_isOpen hDo (by simp)
  have hΘ2d : ∀ x ∈ D, DifferentiableAt ℝ (fderiv ℝ Θ) x := fun x hx =>
    (hΘ2.differentiableOn (by simp)).differentiableAt (hDo.mem_nhds hx)
  have hFderiv : ∀ c : ℝ, |c| ≤ c₁ → HasDerivAt F (Fd c) c := fun c hc =>
    (hΘd _ (hseg c hc)).hasFDerivAt.comp_hasDerivAt c (hcurve c)
  have hFdderiv : ∀ c : ℝ, |c| ≤ c₁ → HasDerivAt Fd (Fdd c) c := fun c hc =>
    hasDerivAt_fderiv_comp' (hΘ2d _ (hseg c hc)) (hcurve c) (0, w)
  have hτmem : ∀ c ∈ Ioo 0 ρ, c / c₁ ∈ Ioo (0 : ℝ) (min η 1) := fun c hc =>
    ⟨div_pos hc.1 hc₁pos, by rw [div_lt_iff₀ hc₁pos]; nlinarith [hc.2]⟩
  have hFC : ∀ c ∈ Ioo 0 ρ, F c = C (c / c₁) := by
    intro c hc
    have h := hrel (c / c₁) (hτmem c hc)
    have e : (c / c₁) • v = c • w := by
      rw [hv, smul_smul]; congr 1; field_simp
    rw [e] at h
    show Θ (q, c • w) = _
    rw [hΘ]; exact h
  have hηmem : ∀ c ∈ Ioo 0 ρ, c / c₁ ∈ Ioo (-η) η := fun c hc => by
    have := hτmem c hc
    exact ⟨by linarith [this.1], lt_of_lt_of_le this.2 (min_le_left _ _)⟩
  have hCd : ∀ c ∈ Ioo 0 ρ, HasDerivAt (fun c => C (c / c₁)) ((1 / c₁) • C1 (c / c₁)) c := fun c hc =>
    (hCg _ (hηmem c hc)).1.scomp c ((hasDerivAt_id c).div_const c₁)
  have hFdC : ∀ c ∈ Ioo 0 ρ, Fd c = (1 / c₁) • C1 (c / c₁) := by
    intro c hc
    have hF1 := hFderiv c (by rw [abs_of_pos hc.1]; linarith [hc.2])
    have hF2 : HasDerivAt F ((1 / c₁) • C1 (c / c₁)) c :=
      (hCd c hc).congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhds hc.1 hc.2] with c' hc' using hFC c' hc')
    exact hF1.unique hF2
  have hC1d : ∀ c ∈ Ioo 0 ρ, HasDerivAt (fun c => (1 / c₁) • C1 (c / c₁))
      ((1 / c₁) • ((1 / c₁) • Lightlike.Geodesic.accel (g.coordMetric p₀) (C (c / c₁)) (C1 (c / c₁)))) c :=
    fun c hc => ((hCg _ (hηmem c hc)).2.scomp c ((hasDerivAt_id c).div_const c₁)).const_smul (1 / c₁)
  have hFddC : ∀ c ∈ Ioo 0 ρ, Fdd c = (1 / c₁) • ((1 / c₁) • Lightlike.Geodesic.accel (g.coordMetric p₀)
      (C (c / c₁)) (C1 (c / c₁))) := by
    intro c hc
    have hF1 := hFdderiv c (by rw [abs_of_pos hc.1]; linarith [hc.2])
    have hF2 : HasDerivAt Fd _ c := (hC1d c hc).congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hc.1 hc.2] with c' hc' using hFdC c' hc')
    exact hF1.unique hF2
  have h0c : |(0 : ℝ)| ≤ c₁ := by simp [hc₁pos.le]
  have hmem0 : (0 : ℝ) ∈ Ioo (-η) η := ⟨by linarith, hη⟩
  -- first jet
  have hCt : ContinuousAt (fun c => (1 / c₁) • C1 (c / c₁)) 0 := by
    have h1 : ContinuousAt C1 ((fun c : ℝ => c / c₁) 0) := by simpa using (hCg 0 hmem0).2.continuousAt
    exact (ContinuousAt.comp (f := fun c : ℝ => c / c₁) h1 (continuous_id.div_const c₁).continuousAt).const_smul (1 / c₁)
  have hFd0 : Fd 0 = w := by
    have := eq_at_zero_of_eq_right hρpos (hFdderiv 0 h0c).continuousAt hCt hFdC
    have e : Fd 0 = (1 / c₁) • C1 (0 / c₁) := this
    rw [e, zero_div, hC10, hv, smul_smul, one_div, inv_mul_cancel₀ hc₁pos.ne', one_smul]
  refine ⟨?_, ?_⟩
  · have : Fd 0 = fderiv ℝ Θ (q, 0) (0, w) := by simp [hFd]
    rw [← this]; exact hFd0
  · have hg₁ := g.toNondegMetric.isCoordMetric_coordMetric p₀
    have hx : ContinuousAt (fun c : ℝ => C (c / c₁)) 0 :=
      ContinuousAt.comp (f := fun c : ℝ => c / c₁) (by simpa using (hCg 0 hmem0).1.continuousAt)
        (continuous_id.div_const c₁).continuousAt
    have hvc : ContinuousAt (fun c : ℝ => C1 (c / c₁)) 0 :=
      ContinuousAt.comp (f := fun c : ℝ => c / c₁) (by simpa using (hCg 0 hmem0).2.continuousAt)
        (continuous_id.div_const c₁).continuousAt
    have hxU : (fun c : ℝ => C (c / c₁)) 0 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target := by
      simp only [zero_div, hC0]; exact hq
    have hacc : ContinuousAt (fun c => (1 / c₁) • ((1 / c₁) • Lightlike.Geodesic.accel (g.coordMetric p₀)
        (C (c / c₁)) (C1 (c / c₁)))) 0 := by
      have hG := continuousAt_gammaApply hg₁ hx hvc hvc hxU
      have e : ∀ x v : Fin n → ℝ, Lightlike.Geodesic.accel (g.coordMetric p₀) x v =
          -Lightlike.Geodesic.gammaApply (g.coordMetric p₀) x v v := fun x v =>
        Lightlike.Geodesic.accel_eq_neg_gammaApply x v
      simp only [e]
      exact (hG.neg.const_smul (1 / c₁)).const_smul (1 / c₁)
    have hΘ3 : ContinuousOn (fderiv ℝ (fderiv ℝ Θ)) D := hΘ2.continuousOn_fderiv_of_isOpen hDo (by simp)
    have hq0' : ((q, (0 : ℝ) • w) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by simpa using hq0
    have hFddc : ContinuousAt Fdd 0 := by
      have h2 : ContinuousAt (fun c : ℝ => fderiv ℝ (fderiv ℝ Θ) (q, c • w)) 0 :=
        ContinuousAt.comp (f := fun c : ℝ => ((q, c • w) : (Fin n → ℝ) × (Fin n → ℝ)))
          (hΘ3.continuousAt (hDo.mem_nhds hq0')) (hcurve 0).continuousAt
      exact (h2.clm_apply continuousAt_const).clm_apply continuousAt_const
    have heq := eq_at_zero_of_eq_right hρpos hFddc hacc hFddC
    have e : Fdd 0 = (1 / c₁) • ((1 / c₁) • Lightlike.Geodesic.accel (g.coordMetric p₀) q (c₁ • w)) := by
      rw [heq]; simp only [zero_div, hC0, hC10, hv]
    have e2 : Fdd 0 = fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) := by simp [hFdd]
    rw [← e2, e, Lightlike.Geodesic.accel_smul, smul_smul, smul_smul]
    have : (1 / c₁ * (1 / c₁) * c₁ ^ 2) = 1 := by field_simp
    rw [this, one_smul]

/-- The smooth exponential map in a chart: `Θ (q, w) = ψ (Γ ⟨ψ⁻¹ q, e⁻¹ w⟩ 1)`. -/
structure ThetaData (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (p₀ : M) where
  /-- The open domain of `Θ`, a neighbourhood of `(ψ p₀, 0)`. -/
  D : Set ((Fin n → ℝ) × (Fin n → ℝ))
  /-- The chart expression of the exponential map. -/
  Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ
  isOpen : IsOpen D
  mem0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ p₀, (0 : Fin n → ℝ)) ∈ D
  smooth : ContDiffOn ℝ ∞ Θ D
  zero : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q
  /-- `D_w Θ (q, 0) = id`. -/
  jet1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w
  /-- `D_w² Θ (q, 0) (w, w) = -Γ (q) (w, w)`. -/
  jet2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
    Lightlike.Geodesic.accel (g.coordMetric p₀) q w
  /-- `Θ` is the chart expression of the intrinsic exponential map applied to the tangent vector with the
  coordinates `(q, w)` in the chart at `p₀`. -/
  exp_eq : ∀ x ∈ D, Θ x = extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (expT g (zetaMap (n := n) p₀ x))

/-- The smooth exponential map in the chart at `p₀` exists. -/
theorem exists_thetaData (p₀ : M) : Nonempty (ThetaData g p₀) := by
  classical
  obtain ⟨N, ε, Γ, hNo, hz0N, hε, hgeo, hsm⟩ := expGerm_exists g p₀
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ with hψ
  set ζ := zetaMap (n := n) p₀ with hζ
  have hζs := contMDiffOn_zetaMap (n := n) p₀
  have hζc : ContinuousOn ζ (ψ.target ×ˢ univ) := hζs.continuousOn
  -- the time-one map is smooth on `N`
  have hΞ : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => Γ z 1) N := by
    have hpr : ContMDiff (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => z.proj) :=
      Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)
    have h1 : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
        ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) ∞
        (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => (z, (1 : ℝ))) N :=
      contMDiffOn_id.prodMk contMDiffOn_const
    have h2 := hsm.comp h1 (fun z hz => ⟨hz, ⟨by linarith, by linarith⟩⟩)
    exact (hpr.comp_contMDiffOn h2)
  set D₁ : Set ((Fin n → ℝ) × (Fin n → ℝ)) := (ψ.target ×ˢ univ) ∩ ζ ⁻¹' N with hD₁
  have hD₁o : IsOpen D₁ :=
    hζc.isOpen_inter_preimage ((isOpen_extChartAt_target p₀).prod isOpen_univ) hNo
  have hX : ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun x => Γ (ζ x) 1) D₁ := hΞ.comp (hζs.mono inter_subset_left) (fun x hx => hx.2)
  set D : Set ((Fin n → ℝ) × (Fin n → ℝ)) := D₁ ∩ (fun x => Γ (ζ x) 1) ⁻¹' ψ.source with hD
  have hDo : IsOpen D := hX.continuousOn.isOpen_inter_preimage hD₁o (isOpen_extChartAt_source p₀)
  have hbase : ∀ q ∈ ψ.target, ψ.symm q ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := fun q hq => by
    have hs : ψ.symm q ∈ ψ.source := ψ.map_target hq
    have hs' : ψ.symm q ∈ (chartAt (Fin n → ℝ) p₀).source := by
      have := hs; rw [hψ, extChartAt_source] at this; exact this
    exact (by simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet] using hs')
  have hζ0 : ∀ q ∈ ψ.target, ζ (q, 0) = ⟨ψ.symm q, 0⟩ := fun q hq => by
    rw [hζ, zetaMap_eq p₀ (q, 0) (hbase q hq)]
    show (⟨ψ.symm q, (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ (ψ.symm q) 0⟩ :
      TangentBundle 𝓘(ℝ, Fin n → ℝ) M) = ⟨ψ.symm q, 0⟩
    rw [map_zero]
  have hmem0 : (ψ p₀, (0 : Fin n → ℝ)) ∈ D := by
    have hq : ψ p₀ ∈ ψ.target := ψ.map_source (mem_extChartAt_source p₀)
    have hsymm : ψ.symm (ψ p₀) = p₀ := ψ.left_inv (mem_extChartAt_source p₀)
    have hz : ζ (ψ p₀, 0) = ⟨p₀, 0⟩ := by rw [hζ0 _ hq, hsymm]
    have hz0 : (⟨p₀, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ N := hz0N
    refine ⟨⟨⟨hq, mem_univ _⟩, by rw [mem_preimage, hz]; exact hz0⟩, ?_⟩
    show Γ (ζ (ψ p₀, 0)) 1 ∈ ψ.source
    rw [hz, flow_zero g hε hgeo hz0]
    exact mem_extChartAt_source p₀
  have hΘsm : ContDiffOn ℝ ∞ (fun x => ψ (Γ (ζ x) 1)) D := by
    have h1 : ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun x => ψ (Γ (ζ x) 1)) D :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) (x := p₀)).comp (hX.mono inter_subset_left)
        (fun x hx => by have h := hx.2; rw [mem_preimage, hψ, extChartAt_source] at h; exact h)
    exact contMDiffOn_iff_contDiffOn.1 h1
  refine ⟨⟨D, fun x => ψ (Γ (ζ x) 1), hDo, hmem0, hΘsm, ?_, ?_, ?_, ?_⟩⟩
  · intro q hq
    have hq' : q ∈ ψ.target := hq.1.1.1
    have hz : ζ (q, 0) = ⟨ψ.symm q, 0⟩ := hζ0 q hq'
    have hzN : (⟨ψ.symm q, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ N := by
      have := hq.1.2; rw [mem_preimage, hz] at this; exact this
    show ψ (Γ (ζ (q, 0)) 1) = q
    rw [hz, flow_zero g hε hgeo hzN]
    exact ψ.right_inv hq'
  · intro q hq0 w
    exact (theta_jets g p₀ hε hgeo hDo (fun x hx => hx.1.2) (fun x => rfl) hΘsm hq0.1.1.1 hq0 w).1
  · intro q hq0 w
    exact (theta_jets g p₀ hε hgeo hDo (fun x hx => hx.1.2) (fun x => rfl) hΘsm hq0.1.1.1 hq0 w).2
  · intro x hx
    show ψ (Γ (ζ x) 1) = ψ (expT g (ζ x))
    rw [expT_eq_flow g hε hgeo hx.1.2]

end Lightlike.Penrose
