import Lightlike.Rows.G1_012.ExpFlow
import Lightlike.Rows.G1_012.Defs
import Lightlike.Rows.G1_012.Orthogonality

/-!
# Compactness of the exponential image of compact null data (G1-012)

For a null geodesically complete Lorentzian manifold, the image of a compact set `K` of null
vectors under `(z, t) ↦ γ_z(t)`, `t ∈ [0, Λ]`, is compact (`compact_nullExp_image`): the null geodesic
from each `z ∈ K` is complete, and the geodesic flow is continuous along it (`flowGerm_along`).
-/

open Bundle Manifold Set Filter Topology Metric Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **A chart geodesic whose velocity vanishes at one time vanishes on the whole interval.** -/
theorem IsGeodesicOn.velocity_zero (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected) (h : IsGeodesicOn g γ w I)
    (hU : ∀ t ∈ I, γ t ∈ U) {t₁ : ℝ} (ht₁ : t₁ ∈ I) (h0 : w t₁ = 0) {t : ℝ} (ht : t ∈ I) :
    w t = 0 := by
  have hconst : IsGeodesicOn g (fun _ => γ t₁) (fun _ => (0 : Fin n → ℝ)) univ := by
    refine ⟨fun s _ => hasDerivAt_const s _, fun s _ => ?_⟩
    have h0 : accel g (γ t₁) 0 = 0 := by
      have := accel_smul g (γ t₁) 0 0
      simpa using this
    rw [h0]; exact hasDerivAt_const s _
  rcases le_total t₁ t with hle | hle
  · have hsub : Icc t₁ t ⊆ I := hIc.out ht₁ ht
    have := IsGeodesicOn.eqOn_Icc hg hI isOpen_univ hsub (subset_univ _) h hconst
      (fun s hs => hU s (hsub hs)) rfl (by simpa using h0) t ⟨hle, le_rfl⟩
    simpa using this.2
  · -- reverse the parameter
    have hsub : Icc t t₁ ⊆ I := hIc.out ht ht₁
    have hr := (h.scale (-1))
    have hI' : IsOpen ((fun s : ℝ => -1 * s) ⁻¹' I) := hI.preimage (by fun_prop)
    have hsub' : Icc (-t₁) (-t) ⊆ (fun s : ℝ => -1 * s) ⁻¹' I := by
      intro s hs
      show -1 * s ∈ I
      exact hsub ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hconst' := hconst.scale (-1)
    have := IsGeodesicOn.eqOn_Icc hg hI' isOpen_univ hsub' (subset_univ _) hr
      (by simpa using hconst') (fun s hs => hU _ (hsub (by
        constructor <;> linarith [hs.1, hs.2]))) (by simp) (by simpa using h0) (-t) ⟨by linarith, le_rfl⟩
    simpa using this.2

end Lightlike.Geodesic

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The velocity of `γ` at `t` is a nonzero null vector. -/
def NullAt (γ : ℝ → M) (t : ℝ) : Prop :=
  g.g (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t (1 : ℝ)) = 0 ∧
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t (1 : ℝ) ≠ 0

/-- In a chart in which the curve has chart velocity `w t`, the velocity is a nonzero null vector iff
`w t` is a nonzero null vector of the coordinate metric. -/
theorem nullAt_iff_chart (x : M) {γ : ℝ → M} {t : ℝ} {w : Fin n → ℝ}
    (hsrc : γ t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    (hw : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x (phase (n := n) γ t)).2 = w) :
    NullAt g γ t ↔ bil (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ t))) w w = 0 ∧ w ≠ 0 := by
  have hb := mem_baseSet_of_mem_source x (γ t) hsrc
  have hvq := eq_symmL_of_tTriv x (γ t) hb
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t (1 : ℝ)) hw
  have hmet := metric_eq_bil_at g.toNondegMetric x (γ t) hsrc w w
  unfold NullAt
  rw [hvq]
  refine and_congr (by rw [hmet]) ?_
  constructor
  · intro hne h0
    apply hne
    rw [h0, map_zero]
  · intro hne h0
    apply hne
    have : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨γ t, ((chartTriv n x).symmL ℝ (γ t) w)⟩).2 = w := by
      rw [← hvq] at *
      exact hw
    rw [h0] at this
    rw [← this]
    have hlin : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨γ t, (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t))⟩).2 =
        (chartTriv n x).linearEquivAt ℝ (γ t) hb 0 := by
      rw [Trivialization.linearEquivAt_apply]
    rw [hlin, map_zero]

/-- **Nullness of the velocity is locally constant along a geodesic curve.** -/
theorem nullAt_local {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (h : IsGeodesicCurveOn g γ J) {t₁ : ℝ}
    (ht₁ : t₁ ∈ J) : ∃ V ∈ 𝓝 t₁, V ⊆ J ∧ ∀ t ∈ V, (NullAt g γ t ↔ NullAt g γ t₁) := by
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t₁ ht₁
  set x := γ t₁ with hx
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Ioo (t₁ - r) (t₁ + r) ⊆ interior O ∩ J := by
    have : interior O ∩ J ∈ 𝓝 t₁ := Filter.inter_mem (interior_mem_nhds.2 hO) (hJ.mem_nhds ht₁)
    obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨r, hr, by simpa [Real.ball_eq_Ioo] using hb⟩
  set V : Set ℝ := Ioo (t₁ - r) (t₁ + r) with hV
  have hVo : IsOpen V := isOpen_Ioo
  have ht₁V : t₁ ∈ V := ⟨by linarith, by linarith⟩
  have hgeoV : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x)
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) w V :=
    ⟨fun s hs => hgeo.pos s (interior_subset (hball hs).1),
     fun s hs => hgeo.vel s (interior_subset (hball hs).1)⟩
  have hsrcV : ∀ s ∈ V, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source :=
    fun s hs => hsrc s (interior_subset (hball hs).1)
  have hcoord : ∀ s ∈ V, (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x (phase (n := n) γ s)).2 = w s :=
    fun s hs => (phase_coord g x hVo hsrcV hgeoV hs).2
  have hg1 := g.toNondegMetric.isCoordMetric_coordMetric x
  have hsp : ∀ s ∈ V, HasDerivAt (fun r => Lightlike.Geodesic.normSq (g.coordMetric x)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ r)) (w r)) 0 s := fun s hs =>
    hgeoV.hasDerivAt_speed hg1 hs (ψ.map_source (hsrcV s hs))
  refine ⟨V, hVo.mem_nhds ht₁V, fun s hs => (hball hs).2, fun t ht => ?_⟩
  rw [nullAt_iff_chart g x (hsrcV t ht) (hcoord t ht), nullAt_iff_chart g x (hsrcV t₁ ht₁V) (hcoord t₁ ht₁V)]
  have hconst := Lightlike.Geodesic.eq_of_hasDerivAt_zero_Ioo hsp ht ht₁V
  have hbil : ∀ s, bil (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s))) (w s) (w s) =
      Lightlike.Geodesic.normSq (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) (w s) := by
    intro s
    rw [← Lightlike.Geodesic.pairing_self, pairing_eq_bil]
  rw [hbil, hbil, hconst]
  refine and_congr Iff.rfl ⟨fun hne h0 => hne ?_, fun hne h0 => hne ?_⟩
  · exact Lightlike.Geodesic.IsGeodesicOn.velocity_zero hg1 hVo ordConnected_Ioo hgeoV
      (fun s hs => ψ.map_source (hsrcV s hs)) ht₁V h0 ht
  · exact Lightlike.Geodesic.IsGeodesicOn.velocity_zero hg1 hVo ordConnected_Ioo hgeoV
      (fun s hs => ψ.map_source (hsrcV s hs)) ht h0 ht₁V

/-- **A geodesic curve whose velocity is a nonzero null vector at one time is a null geodesic.** -/
theorem isNullGeodesicOn_of_nullAt {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : J.OrdConnected)
    (h : IsGeodesicCurveOn g γ J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hnull : NullAt g γ t₀) :
    IsNullGeodesicOn g γ J := by
  set A : Set ℝ := {t | t ∈ J ∧ NullAt g γ t} with hA
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro t ⟨htJ, htN⟩
    obtain ⟨V, hV, hVJ, hVN⟩ := nullAt_local g hJ h htJ
    filter_upwards [hV] with s hs
    exact ⟨hVJ hs, (hVN s hs).2 htN⟩
  have hclos : J ∩ closure A ⊆ A := by
    rintro t ⟨htJ, htc⟩
    obtain ⟨V, hV, hVJ, hVN⟩ := nullAt_local g hJ h htJ
    obtain ⟨s, hsV, hsA⟩ := mem_closure_iff_nhds.1 htc V hV
    exact ⟨htJ, (hVN s hsV).1 hsA.2⟩
  have hall : J ⊆ A := hJc.isPreconnected.subset_of_closure_inter_subset hAo
    ⟨t₀, ht₀, ht₀, hnull⟩ (by rw [inter_comm]; exact hclos)
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t ht
  have hO' : IsOpen (interior O) := isOpen_interior
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) w (interior O) :=
    ⟨fun s hs => hgeo.pos s (interior_subset hs), fun s hs => hgeo.vel s (interior_subset hs)⟩
  have hcoord := (phase_coord g (γ t) hO' (fun s hs => hsrc s (interior_subset hs)) hgeo'
    (mem_interior_iff_mem_nhds.2 hO)).2
  have hsrct := hsrc t (mem_of_mem_nhds hO)
  have := (nullAt_iff_chart g (γ t) hsrct hcoord).1 (hall ht).2
  exact ⟨w, O, hO, hsrc, hgeo, this.2, this.1⟩

/-- A nonzero null vector of the tangent bundle. -/
def IsNullVec (z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) : Prop :=
  g.g z.proj z.snd z.snd = 0 ∧ z.snd ≠ 0

theorem nullAt_iff_isNullVec (γ : ℝ → M) (t : ℝ) :
    NullAt g γ t ↔ IsNullVec g (phase (n := n) γ t) := Iff.rfl

/-- **A nonzero null vector is the initial phase of a complete null geodesic** when the manifold is
null geodesically complete. -/
theorem exists_complete_null (hc : NullGeodesicallyComplete g)
    (z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (hz : IsNullVec g z) :
    ∃ γ : ℝ → M, IsNullGeodesicOn g γ univ ∧ phase (n := n) γ 0 = z := by
  obtain ⟨N, δ, Γ, hNo, hz₀, hδ, hgeo, -⟩ := exists_local_flow g z
  obtain ⟨hgeoz, hph⟩ := hgeo z hz₀
  have h0 : (0 : ℝ) ∈ Ioo (-δ) (0 + δ) := ⟨by linarith, by linarith⟩
  have hnull : IsNullGeodesicOn g (Γ z) (Ioo (-δ) δ) := by
    have := isNullGeodesicOn_of_nullAt g isOpen_Ioo ordConnected_Ioo (J := Ioo (-δ) δ)
      (by simpa using hgeoz) (t₀ := 0) (by simpa using h0) (by rw [nullAt_iff_isNullVec, hph]; exact hz)
    exact this
  obtain ⟨γ', hγ', heq⟩ := hc (Γ z) (-δ) δ (by linarith) hnull
  refine ⟨γ', hγ', ?_⟩
  have hev : Γ z =ᶠ[𝓝 0] γ' := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)] with r hr
      using heq hr
  rw [← hph]
  exact (phase_congr g isOpen_Ioo (hgeoz.mono (by simp)) (hγ'.isGeodesicCurveOn.mono (subset_univ _))
    (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩) hev).symm

/-- **Compactness of the exponential image of compact null data.** In a null geodesically complete
manifold, for a compact set `K` of nonzero null vectors and `Λ ≥ 0` there is a compact set `C`
containing `γ t` for every complete null geodesic `γ` with initial phase in `K` and `t ∈ [0, Λ]`. -/
theorem compact_nullExp_image (hc : NullGeodesicallyComplete g)
    {K : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} (hK : IsCompact K) (hKn : ∀ z ∈ K, IsNullVec g z)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ C : Set M, IsCompact C ∧ ∀ z ∈ K, ∀ γ : ℝ → M, IsNullGeodesicOn g γ univ →
      phase (n := n) γ 0 = z → ∀ t ∈ Icc 0 Λ, γ t ∈ C := by
  classical
  by_cases hne : K.Nonempty
  swap
  · refine ⟨∅, isCompact_empty, fun z hz => absurd ⟨z, hz⟩ hne⟩
  obtain ⟨z₁, hz₁⟩ := hne
  haveI : Nonempty M := ⟨z₁.proj⟩
  set Γc : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M := fun z =>
    if h : IsNullVec g z then Classical.choose (exists_complete_null g hc z h) else fun _ => z.proj
    with hΓc
  have hΓcspec : ∀ z ∈ K, IsNullGeodesicOn g (Γc z) univ ∧ phase (n := n) (Γc z) 0 = z := by
    intro z hz
    have := Classical.choose_spec (exists_complete_null g hc z (hKn z hz))
    simpa [hΓc, hKn z hz] using this
  have huniq : ∀ z ∈ K, ∀ γ : ℝ → M, IsNullGeodesicOn g γ univ → phase (n := n) γ 0 = z →
      ∀ t, γ t = Γc z t := by
    intro z hz γ hγ hph t
    exact eqOn_of_phase_eq' g isOpen_univ isPreconnected_univ
      (hγ.isGeodesicCurveOn.mono (subset_univ _)) ((hΓcspec z hz).1.isGeodesicCurveOn.mono (subset_univ _))
      (mem_univ 0) (by rw [hph, (hΓcspec z hz).2]) (mem_univ t)
  have hcont : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => Γc zs.1 zs.2)
      (K ×ˢ Icc 0 Λ) := by
    intro p hp
    obtain ⟨hpK, hpt⟩ := hp
    obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcontΓ⟩ :=
      flowGerm_along g (z₀ := p.1) (γ₀ := Γc p.1) isOpen_univ ordConnected_univ
        (hΓcspec p.1 hpK).1.isGeodesicCurveOn (hΓcspec p.1 hpK).2 (mem_univ 0) hΛ (subset_univ _)
        Λ ⟨hΛ, le_rfl⟩
    have hpt' : p.2 ∈ Ioo (-ε) (Λ + ε) := ⟨by linarith [hpt.1], by linarith [hpt.2]⟩
    have hNJ : N ×ˢ Ioo (-ε) (Λ + ε) ∈ 𝓝 p :=
      (hNo.prod isOpen_Ioo).mem_nhds ⟨hz₀, hpt'⟩
    have hproj : ContinuousAt (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
        (phase (n := n) (Γ zs.1) zs.2).proj) p :=
      (FiberBundle.continuous_proj (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ))).continuousAt.comp
        (hcontΓ.continuousAt hNJ)
    refine hproj.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hNJ, self_mem_nhdsWithin] with zs hzs hzsK
      have := eqOn_of_phase_eq' g (isOpen_Ioo (a := -ε) (b := Λ + ε)) isPreconnected_Ioo
        (hgeo zs.1 hzs.1).1 ((hΓcspec zs.1 hzsK.1).1.isGeodesicCurveOn.mono (subset_univ _))
        (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Ioo (-ε) (Λ + ε))
        (by rw [(hgeo zs.1 hzs.1).2, (hΓcspec zs.1 hzsK.1).2]) hzs.2
      exact this.symm
    · have := eqOn_of_phase_eq' g (isOpen_Ioo (a := -ε) (b := Λ + ε)) isPreconnected_Ioo
        (hgeo p.1 hz₀).1 ((hΓcspec p.1 hpK).1.isGeodesicCurveOn.mono (subset_univ _))
        (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Ioo (-ε) (Λ + ε))
        (by rw [(hgeo p.1 hz₀).2, (hΓcspec p.1 hpK).2]) hpt'
      exact this.symm
  refine ⟨(fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => Γc zs.1 zs.2) '' (K ×ˢ Icc 0 Λ),
    (hK.prod isCompact_Icc).image_of_continuousOn hcont, ?_⟩
  intro z hz γ hγ hph t ht
  exact ⟨(z, t), ⟨hz, ht⟩, (huniq z hz γ hγ hph t).symm⟩

end Lightlike.Penrose
