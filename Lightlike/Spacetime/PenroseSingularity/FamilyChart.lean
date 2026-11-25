import Lightlike.Spacetime.PenroseSingularity.JacobiVarChart
import Lightlike.Spacetime.PenroseSingularity.FlowSmooth
import Lightlike.Spacetime.PenroseSingularity.GeodesicChartConverse
import Lightlike.Spacetime.PenroseSingularity.ExpFlow
import Lightlike.Spacetime.PenroseSingularity.Orthogonality

/-!
# A family of geodesics from the flow, in a chart (G1-012, step D3b wiring)

If `Γ z` is the geodesic with initial phase `z` and `σ ↦ zS σ` is a smooth family of initial phases, then in a
chart at `x₀` the map `H (t, σ) = ψ (Γ (zS σ) t)` is smooth near `(t₀, 0)` and, for each `σ`, a geodesic of the
coordinate metric in `t` (`ChartFamily`).
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

/-- The hypotheses of the chart-level lemmas on a family `H (t, σ)`. -/
structure ChartFamily {n m : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (H : ℝ × (Fin m → ℝ) → Fin n → ℝ) (W : Set (ℝ × (Fin m → ℝ))) : Prop where
  isOpen : IsOpen W
  smooth : ContDiffOn ℝ 3 H W
  mem : ∀ p ∈ W, H p ∈ U
  geo : ∀ p ∈ W, Lightlike.Geodesic.IsGeodesicOn g (fun t => H (t, p.2))
    (fun t => fderiv ℝ H (t, p.2) (1, 0)) {t | (t, p.2) ∈ W}
  null : ∀ p ∈ W, gpairAt g (H p) (fderiv ℝ H p (1, 0)) (fderiv ℝ H p (1, 0)) = 0

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The family `F (t, σ) = Γ (zS σ) t` is smooth, as a map of manifolds into the tangent bundle (its phase). -/
theorem contMDiffOn_phaseFamily {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
    {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
    {J : Set ℝ} {Sg : Set (Fin m → ℝ)}
    (hsm : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2) (Nz ×ˢ J))
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg)
    (hzN : ∀ σ ∈ Sg, zS σ ∈ Nz) :
    ContMDiffOn 𝓘(ℝ, ℝ × (Fin m → ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun p : ℝ × (Fin m → ℝ) => phase (n := n) (Γ (zS p.2)) p.1) (J ×ˢ Sg) := by
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ × (Fin m → ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun p : ℝ × (Fin m → ℝ) => zS p.2) (J ×ˢ Sg) :=
    hzS.comp (contDiff_snd.contMDiff.contMDiffOn) (fun p hp => hp.2)
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ × (Fin m → ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × (Fin m → ℝ) => p.1) (J ×ˢ Sg) := contDiff_fst.contMDiff.contMDiffOn
  have h3 := h1.prodMk h2
  exact hsm.comp h3 (fun p hp => ⟨hzN _ hp.2, hp.1⟩)

/-- The chart expression `H (t, σ) = ψ (Γ (zS σ) t)` is `C^∞` on the open set where it is defined. -/
theorem contDiffOn_chartFamily (x₀ : M) {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
    {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
    {J : Set ℝ} {Sg : Set (Fin m → ℝ)}
    (hsm : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2) (Nz ×ˢ J))
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg)
    (hzN : ∀ σ ∈ Sg, zS σ ∈ Nz) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1))
      {p ∈ J ×ˢ Sg | Γ (zS p.2) p.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source} := by
  have hph := contMDiffOn_phaseFamily hsm hzS hzN
  have hproj : ContMDiffOn 𝓘(ℝ, ℝ × (Fin m → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun p : ℝ × (Fin m → ℝ) => Γ (zS p.2) p.1) (J ×ˢ Sg) := by
    have hpr : ContMDiff (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => z.proj) :=
      Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)
    exact hpr.comp_contMDiffOn hph
  have hψ := contMDiffOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀) (n := ∞)
  have hcomp := hψ.comp (hproj.mono inter_subset_left) (fun p hp => hp.2)
  have hset : {p ∈ J ×ˢ Sg | Γ (zS p.2) p.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source} =
      J ×ˢ Sg ∩ (fun p : ℝ × (Fin m → ℝ) => Γ (zS p.2) p.1) ⁻¹' (chartAt (Fin n → ℝ) x₀).source := by
    ext p; simp [extChartAt_source]
  rw [hset]
  exact contMDiffOn_iff_contDiffOn.1 hcomp

theorem gpairAt_eq_bil {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (x u v : Fin n → ℝ) :
    gpairAt g x u v = Lightlike.bil (g x) u v := by
  unfold gpairAt Lightlike.bil
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The chart data of a smooth family of geodesics from the flow** (no nullness assumed). -/
theorem exists_chartGeo (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M)
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
    {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
    {J : Set ℝ} (hJ : IsOpen J) {Sg : Set (Fin m → ℝ)} (hSg : IsOpen Sg)
    (hgeo : ∀ z ∈ Nz, IsGeodesicCurveOn g (Γ z) J)
    (hsm : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2) (Nz ×ˢ J))
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg)
    (hzN : ∀ σ ∈ Sg, zS σ ∈ Nz)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) {σ₀ : Fin m → ℝ} (h0 : σ₀ ∈ Sg) (hx₀ : Γ (zS σ₀) t₀ = x₀) :
    ∃ W : Set (ℝ × (Fin m → ℝ)), (t₀, σ₀) ∈ W ∧ IsOpen W ∧
      ContDiffOn ℝ 3 (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1)) W ∧
      (∀ p ∈ W, extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1) ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) ∧
      (∀ p ∈ W, Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀)
        (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) t))
        (fun t => fderiv ℝ (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1))
          (t, p.2) (1, 0)) {t | (t, p.2) ∈ W}) ∧
      (∀ p ∈ W, p.2 ∈ Sg ∧ p.1 ∈ J ∧ Γ (zS p.2) p.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source ∧
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS p.2)) p.1)).2 =
          fderiv ℝ (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1))
            p (1, 0)) := by
  classical
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  set F : ℝ × (Fin m → ℝ) → M := fun p => Γ (zS p.2) p.1 with hF
  have hph := contMDiffOn_phaseFamily hsm hzS hzN
  have hFc : ContinuousOn F (J ×ˢ Sg) := by
    have hpr : ContMDiff (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => z.proj) :=
      Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)
    exact (hpr.comp_contMDiffOn hph).continuousOn
  set W : Set (ℝ × (Fin m → ℝ)) := {p ∈ J ×ˢ Sg | F p ∈ ψ.source} with hW
  have hWo : IsOpen W := hFc.isOpen_inter_preimage (hJ.prod hSg) (isOpen_extChartAt_source x₀)
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin m → ℝ) => ψ (F p)) W :=
    contDiffOn_chartFamily x₀ hsm hzS hzN
  have h0W : ((t₀, σ₀) : ℝ × (Fin m → ℝ)) ∈ W := by
    refine ⟨⟨ht₀, h0⟩, ?_⟩
    show Γ (zS σ₀) t₀ ∈ ψ.source
    rw [hx₀]; exact mem_extChartAt_source x₀
  set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := fun p => ψ (F p) with hH
  have key : ∀ p ∈ W, Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x₀) (fun t => H (t, p.2))
      (fun t => fderiv ℝ H (t, p.2) (1, 0)) {t | (t, p.2) ∈ W} ∧
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS p.2)) p.1)).2 =
        fderiv ℝ H p (1, 0) := by
    intro p hp
    set σ := p.2 with hσ
    have hσS : σ ∈ Sg := hp.1.2
    set O : Set ℝ := {t' | ((t', σ) : ℝ × (Fin m → ℝ)) ∈ W} with hO
    have hOo : IsOpen O := hWo.preimage (by fun_prop)
    have hOJ : O ⊆ J := fun t' ht' => ht'.1.1
    have hsrc : ∀ s ∈ O, Γ (zS σ) s ∈ ψ.source := fun s hs => hs.2
    have hcurve := (hgeo (zS σ) (hzN σ hσS)).mono hOJ
    obtain ⟨w, hw⟩ := geodesicOn_chart_of_curve g x₀ hOo hsrc hcurve
    have hwd : ∀ t' ∈ O, w t' = fderiv ℝ H (t', σ) (1, 0) := by
      intro t' ht'
      have hdiff : DifferentiableAt ℝ H (t', σ) :=
        (hsmooth.contDiffAt (hWo.mem_nhds ht')).differentiableAt (by simp)
      have hq : HasDerivAt (fun s : ℝ => ((s, σ) : ℝ × (Fin m → ℝ))) ((1, 0) : ℝ × (Fin m → ℝ)) t' := by
        simpa using (hasDerivAt_id t').prodMk (hasDerivAt_const t' σ)
      have h1 := hdiff.hasFDerivAt.comp_hasDerivAt t' hq
      exact (hw.pos t' ht').unique h1
    have hpO : p.1 ∈ O := by simpa [hO, hσ] using hp
    refine ⟨⟨fun t' ht' => ?_, fun t' ht' => ?_⟩, ?_⟩
    · rw [← hwd t' ht']; exact hw.pos t' ht'
    · rw [← hwd t' ht']
      have := hw.vel t' ht'
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [hOo.mem_nhds ht'] with s hs using (hwd s hs).symm
    · have := (phase_coord g x₀ hOo hsrc hw hpO).2
      rw [this, hwd p.1 hpO]
  exact ⟨W, h0W, hWo, hsmooth.of_le (by norm_num), fun p hp => ψ.map_source hp.2,
    fun p hp => (key p hp).1, fun p hp => ⟨hp.1.2, hp.1.1, hp.2, (key p hp).2⟩⟩

/-- **The chart family of a smooth family of geodesics from the flow.** -/
theorem exists_chartFamily (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M)
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
    {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
    {J : Set ℝ} (hJ : IsOpen J) {Sg : Set (Fin m → ℝ)} (hSg : IsOpen Sg)
    (hgeo : ∀ z ∈ Nz, IsGeodesicCurveOn g (Γ z) J)
    (hsm : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2) (Nz ×ˢ J))
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg)
    (hzN : ∀ σ ∈ Sg, zS σ ∈ Nz)
    (hnull : ∀ σ ∈ Sg, ∀ t ∈ J, g.g (phase (n := n) (Γ (zS σ)) t).proj
      (phase (n := n) (Γ (zS σ)) t).snd (phase (n := n) (Γ (zS σ)) t).snd = 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) {σ₀ : Fin m → ℝ} (h0 : σ₀ ∈ Sg) (hx₀ : Γ (zS σ₀) t₀ = x₀) :
    ∃ W : Set (ℝ × (Fin m → ℝ)), (t₀, σ₀) ∈ W ∧
      ChartFamily (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target
        (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1)) W ∧
      (∀ p ∈ W, p.2 ∈ Sg ∧ p.1 ∈ J ∧ Γ (zS p.2) p.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source ∧
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS p.2)) p.1)).2 =
          fderiv ℝ (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1))
            p (1, 0)) := by
  classical
  obtain ⟨W, hW0, hWo, hsm', hmem, hgeo', hvel⟩ :=
    exists_chartGeo g x₀ hJ hSg hgeo hsm hzS hzN ht₀ h0 hx₀
  refine ⟨W, hW0, ⟨hWo, hsm', hmem, hgeo', ?_⟩, hvel⟩
  intro p hp
  obtain ⟨hσS, hpJ, hsrc, hv⟩ := hvel p hp
  set z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M := phase (n := n) (Γ (zS p.2)) p.1 with hz
  have hb : z.proj ∈ (chartTriv n x₀).baseSet := by
    rw [chartTriv_baseSet_eq]; exact hsrc
  have hdec : z.snd = (chartTriv n x₀).symmL ℝ z.proj ((chartTriv n x₀ z).2) := by
    rw [Bundle.Trivialization.symmL_apply (chartTriv n x₀) (R := ℝ) hb]
    exact (Bundle.Trivialization.symm_apply_apply_mk (chartTriv n x₀) hb z.snd).symm
  have hmetric := metric_eq_bil_at g.toNondegMetric x₀ z.proj hsrc ((chartTriv n x₀ z).2)
    ((chartTriv n x₀ z).2)
  have hn := hnull p.2 hσS p.1 hpJ
  rw [← hz, hdec, hmetric] at hn
  rw [gpairAt_eq_bil, ← hv]
  exact hn

end Lightlike.Penrose
