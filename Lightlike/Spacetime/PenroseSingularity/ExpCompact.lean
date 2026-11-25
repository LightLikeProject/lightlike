import Lightlike.Spacetime.PenroseSingularity.ExpFlow
import Lightlike.Spacetime.PenroseSingularity.Defs
import Lightlike.Spacetime.PenroseSingularity.Orthogonality
import Lightlike.Geodesic.TimeBall
import Lightlike.Spacetime.PenroseSingularity.LocalGenerators
import Lightlike.Spacetime.PenroseSingularity.ExpMap
import Lightlike.Spacetime.PenroseSingularity.Generators

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

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Normalised null vectors over a compact set of base points are bounded** in chart
coordinates. -/
theorem bounded_null_normalised (hL : Lightlike.IsLorentzianCoordMetric g U)
    {Kc : Set (Fin n → ℝ)} (hKc : IsCompact Kc) (hKcU : Kc ⊆ U)
    {X : (Fin n → ℝ) → Fin n → ℝ} (hX : ContinuousOn X U)
    (hXt : ∀ y ∈ U, pairing g y (X y) (X y) < 0) :
    ∃ R : ℝ, ∀ u ∈ Kc, ∀ w : Fin n → ℝ, pairing g u w w = 0 → pairing g u (X u) w = -1 →
      ‖w‖ ≤ R := by
  set Sg : Set ((Fin n → ℝ) × (Fin n → ℝ)) := Kc ×ˢ sphere (0 : Fin n → ℝ) 1 with hSgd
  have hSgc : IsCompact Sg := hKc.prod (isCompact_sphere 0 1)
  have hg := hL.1
  have hQ : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => pairing g q.1 q.2 q.2) Sg := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (continuous_apply i |>.comp_continuousOn continuousOn_snd).mul
      (((hg.smooth i j).continuousOn.comp continuousOn_fst
        (fun q hq => hKcU hq.1)).mul (continuous_apply j |>.comp_continuousOn continuousOn_snd))
  have hℓ : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => pairing g q.1 (X q.1) q.2) Sg := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i |>.comp_continuousOn
      (hX.comp continuousOn_fst (fun q hq => hKcU hq.1)))).mul
      (((hg.smooth i j).continuousOn.comp continuousOn_fst
        (fun q hq => hKcU hq.1)).mul (continuous_apply j |>.comp_continuousOn continuousOn_snd))
  have hF : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      max |pairing g q.1 q.2 q.2| |pairing g q.1 (X q.1) q.2|) Sg :=
    hQ.abs.sup hℓ.abs
  by_cases hne : Sg.Nonempty
  · obtain ⟨q₀, hq₀, hmin⟩ := hSgc.exists_isMinOn hne hF
    set c : ℝ := max |pairing g q₀.1 q₀.2 q₀.2| |pairing g q₀.1 (X q₀.1) q₀.2| with hc
    have hcpos : 0 < c := by
      by_contra hcon
      have h0 : c = 0 := le_antisymm (not_lt.1 hcon) (le_max_of_le_left (abs_nonneg _))
      have hQ0 : pairing g q₀.1 q₀.2 q₀.2 = 0 := abs_eq_zero.1 (le_antisymm
        ((le_max_left _ _).trans h0.le) (abs_nonneg _))
      have hℓ0 : pairing g q₀.1 (X q₀.1) q₀.2 = 0 := abs_eq_zero.1 (le_antisymm
        ((le_max_right _ _).trans h0.le) (abs_nonneg _))
      have hy : q₀.1 ∈ U := hKcU hq₀.1
      have hLf := isLorentzianForm_matForm hL hy
      have hq : ∀ a b, pairing g q₀.1 a b = matForm (g q₀.1) a b := fun a b =>
        pairing_eq_matForm g _ a b
      have := hLf.eq_zero_of_orthogonal_timelike (X := X q₀.1) (w := q₀.2)
        (by rw [← hq]; exact hXt _ hy) (by rw [← hq, pairing_comm hg hy]; exact hℓ0)
        (by rw [← hq]; exact hQ0.le)
      have hn : ‖q₀.2‖ = 1 := mem_sphere_zero_iff_norm.1 hq₀.2
      rw [this] at hn
      simp at hn
    refine ⟨c⁻¹, fun u hu w hQw hℓw => ?_⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp [pairing] at hℓw
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set ŵ : Fin n → ℝ := ‖w‖⁻¹ • w with hŵ
    have hŵs : ŵ ∈ sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, hŵ, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
    have hmem : (u, ŵ) ∈ Sg := ⟨hu, hŵs⟩
    have hQŵ : pairing g u ŵ ŵ = 0 := by
      rw [hŵ, pairing_smul_left, pairing_smul_right, hQw]; ring
    have hℓŵ : pairing g u (X u) ŵ = -‖w‖⁻¹ := by
      rw [hŵ, pairing_smul_right, hℓw]; ring
    have hle : c ≤ max |pairing g u ŵ ŵ| |pairing g u (X u) ŵ| := hmin hmem
    rw [hQŵ, hℓŵ, abs_zero, abs_neg, abs_of_pos (inv_pos.2 hwn), max_eq_right (inv_nonneg.2 hwn.le)]
      at hle
    exact (le_inv_comm₀ hcpos hwn).1 hle
  · refine ⟨0, fun u hu w hQw hℓw => ?_⟩
    exfalso
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp [pairing] at hℓw
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    refine hne ⟨(u, ‖w‖⁻¹ • w), hu, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']

end Lightlike.Geodesic

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- The vector with chart coordinates `w` at `p` is zero iff `w = 0`. -/
theorem symmL_eq_zero_iff (x p : M) (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    (w : Fin n → ℝ) : (chartTriv n x).symmL ℝ p w = 0 ↔ w = 0 := by
  constructor
  · intro h0
    have hb := mem_baseSet_of_mem_source x p hp
    have h1 : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨p, (chartTriv n x).symmL ℝ p w⟩).2 = w := by
      rw [Trivialization.symmL_apply _ hb]
      exact (Trivialization.apply_mk_symm (chartTriv n x) hb w) ▸ rfl
    rw [h0] at h1
    have hlin : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨p, (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) p)⟩).2 =
        (chartTriv n x).linearEquivAt ℝ p hb 0 := by
      rw [Trivialization.linearEquivAt_apply]
    rw [hlin, map_zero] at h1
    exact h1.symm
  · rintro rfl; exact map_zero _

/-- A tangent vector given by chart coordinates `w` is a nonzero null vector iff `w` is. -/
theorem isNullVec_symmL_iff (x p : M) (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    (w : Fin n → ℝ) :
    IsNullVec g (⟨p, (chartTriv n x).symmL ℝ p w⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ↔
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) w w = 0 ∧
        w ≠ 0 := by
  unfold IsNullVec
  show g.g p ((chartTriv n x).symmL ℝ p w) ((chartTriv n x).symmL ℝ p w) = 0 ∧
    (chartTriv n x).symmL ℝ p w ≠ 0 ↔ _
  rw [metric_eq_bil_at g.toNondegMetric x p hp w w, pairing_eq_bil]
  exact and_congr Iff.rfl (not_congr (symmL_eq_zero_iff x p hp w))

/-- The pairing with the time orientation field, in chart coordinates. -/
theorem pairing_timeOrientation_symmL (T : Causal.TimeOrientation g) (x p : M)
    (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) (w : Fin n → ℝ) :
    g.g p ((chartTriv n x).symmL ℝ p w) (T.X p) =
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) w
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x p)) := by
  rw [timeOrientation_eq_symmL T x p hp, metric_eq_bil_at g.toNondegMetric x p hp,
    pairing_eq_bil]

/-- The compact piece of normalised null vectors over `S ∩ P`, `P` compact in the chart at `x`. -/
theorem compact_normalised_null_piece (T : Causal.TimeOrientation g) (x : M) {S : Set M}
    (hS : IsCompact S) {P : Set M} (hP : IsCompact P)
    (hPs : P ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) :
    IsCompact {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∩ P ∧ IsNullVec g z ∧
      g.g z.proj z.snd (T.X z.proj) = -1} := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set e := chartTriv n x with he
  have hSP : IsCompact (S ∩ P) := hS.inter_right hP.isClosed
  set Kc : Set (Fin n → ℝ) := ψ '' (S ∩ P) with hKc
  have hKcc : IsCompact Kc :=
    hSP.image_of_continuousOn ((continuousOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) x).mono
      (inter_subset_right.trans hPs))
  have hKct : Kc ⊆ ψ.target := by
    rintro _ ⟨s, hs, rfl⟩
    exact ψ.map_source (hPs hs.2)
  have hL := g.isLorentzianCoordMetric_coordMetric x
  obtain ⟨R, hR⟩ := Lightlike.Geodesic.bounded_null_normalised hL hKcc hKct
    (continuousOn_timeCoord T x) (fun y hy => timeCoord_timelike T x hy)
  set Kp : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | q.1 ∈ Kc ∧
    Lightlike.Geodesic.pairing (g.coordMetric x) q.1 q.2 q.2 = 0 ∧
    Lightlike.Geodesic.pairing (g.coordMetric x) q.1 (timeCoord T x q.1) q.2 = -1} with hKp
  have hKpc : IsCompact Kp := by
    refine (hKcc.prod (isCompact_closedBall (0 : Fin n → ℝ) R)).of_isClosed_subset ?_ ?_
    · -- closed
      have hg1 := hL.1
      have hQc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
          Lightlike.Geodesic.pairing (g.coordMetric x) q.1 q.2 q.2) (Kc ×ˢ univ) := by
        simp only [Lightlike.Geodesic.pairing]
        refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
        exact (continuous_apply i |>.comp_continuousOn continuousOn_snd).mul
          (((hg1.smooth i j).continuousOn.comp continuousOn_fst
            (fun q hq => hKct hq.1)).mul (continuous_apply j |>.comp_continuousOn continuousOn_snd))
      have hℓc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
          Lightlike.Geodesic.pairing (g.coordMetric x) q.1 (timeCoord T x q.1) q.2) (Kc ×ˢ univ) := by
        simp only [Lightlike.Geodesic.pairing]
        refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
        exact ((continuous_apply i |>.comp_continuousOn
          ((continuousOn_timeCoord T x).comp continuousOn_fst (fun q hq => hKct hq.1)))).mul
          (((hg1.smooth i j).continuousOn.comp continuousOn_fst
            (fun q hq => hKct hq.1)).mul (continuous_apply j |>.comp_continuousOn continuousOn_snd))
      have hC : IsClosed (Kc ×ˢ (univ : Set (Fin n → ℝ))) := hKcc.isClosed.prod isClosed_univ
      have h1 := hQc.preimage_isClosed_of_isClosed hC (isClosed_singleton (x := (0 : ℝ)))
      have h2 := (hℓc.mono inter_subset_left).preimage_isClosed_of_isClosed h1
        (isClosed_singleton (x := (-1 : ℝ)))
      convert h2 using 1
      ext q
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨⟨h1, mem_univ _⟩, h2⟩, h3⟩
      · rintro ⟨⟨⟨h1, -⟩, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · rintro q ⟨hq1, hq2, hq3⟩
      refine ⟨hq1, ?_⟩
      rw [mem_closedBall_zero_iff]
      exact hR q.1 hq1 q.2 hq2 hq3
  -- the image under the inverse trivialization
  set Φ : (Fin n → ℝ) × (Fin n → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M := fun q =>
    TotalSpace.mk' (Fin n → ℝ) (ψ.symm q.1) (e.symm (ψ.symm q.1) q.2) with hΦ
  have hΦc : ContinuousOn Φ Kp := by
    have hsymm := e.continuousOn_symm
    have hmap : MapsTo (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (ψ.symm q.1, q.2)) Kp
        (e.baseSet ×ˢ univ) := fun q hq => by
      refine ⟨?_, trivial⟩
      rw [he, chartTriv_baseSet_eq]
      exact ψ.map_target (hKct hq.1)
    exact hsymm.comp (((continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x).comp
      continuousOn_fst (fun q hq => hKct hq.1)).prodMk continuousOn_snd) hmap
  have hg1 := hL.1
  have hΦeq : ∀ q ∈ Kp, ∃ s ∈ S ∩ P, ψ s = q.1 ∧
      Φ q = (⟨s, (chartTriv n x).symmL ℝ s q.2⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := hq.1
    refine ⟨s, hs, hsq, ?_⟩
    have hb : s ∈ e.baseSet := by
      rw [he, chartTriv_baseSet_eq]; exact hPs hs.2
    show (⟨ψ.symm q.1, e.symm (ψ.symm q.1) q.2⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) = _
    rw [← hsq, ψ.left_inv (hPs hs.2), Trivialization.symmL_apply e (R := ℝ) hb]
  have hset : {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∩ P ∧ IsNullVec g z ∧
      g.g z.proj z.snd (T.X z.proj) = -1} = Φ '' Kp := by
    ext z
    constructor
    · rintro ⟨hzP, hz1, hz2⟩
      have hsP : z.proj ∈ ψ.source := hPs hzP.2
      have hb : z.proj ∈ e.baseSet := mem_baseSet_of_mem_source x z.proj hsP
      have hzsrc : z ∈ e.source := by rw [e.mem_source]; exact hb
      set w : Fin n → ℝ := (e z).2 with hw
      have hzs : z = (⟨z.proj, (chartTriv n x).symmL ℝ z.proj w⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := by
        have h1 := Trivialization.symm_apply_apply e hzsrc
        have h2 : e z = (z.proj, w) := Prod.ext (e.coe_fst hzsrc) rfl
        rw [h2] at h1
        rw [Trivialization.symmL_apply e (R := ℝ) hb, Trivialization.mk_symm e hb]
        exact h1.symm
      rw [hzs] at hz1 hz2
      have hnv := (isNullVec_symmL_iff x z.proj hsP w).1 hz1
      refine ⟨(ψ z.proj, w), ⟨⟨z.proj, hzP, rfl⟩, hnv.1, ?_⟩, ?_⟩
      · rw [pairing_timeOrientation_symmL T x z.proj hsP w] at hz2
        rw [Lightlike.Geodesic.pairing_comm hg1 (ψ.map_source hsP)]
        exact hz2
      · obtain ⟨s, hs, hsq, hΦs⟩ := hΦeq (ψ z.proj, w) ⟨⟨z.proj, hzP, rfl⟩, hnv.1, by
          rw [Lightlike.Geodesic.pairing_comm hg1 (ψ.map_source hsP)]
          rw [pairing_timeOrientation_symmL T x z.proj hsP w] at hz2
          exact hz2⟩
        have hs' : s = z.proj := ψ.injOn (hPs hs.2) hsP hsq
        subst hs'
        rw [hΦs]
        exact hzs.symm
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨s, hs, hsq, hΦs⟩ := hΦeq q hq
      have hsP : s ∈ ψ.source := hPs hs.2
      rw [hΦs]
      have hQ := hq.2.1
      have hℓ := hq.2.2
      rw [← hsq] at hQ hℓ
      have hw0 : q.2 ≠ 0 := by
        rintro h0
        rw [h0] at hℓ
        simp [Lightlike.Geodesic.pairing] at hℓ
      refine ⟨hs, (isNullVec_symmL_iff x s hsP q.2).2 ⟨hQ, hw0⟩, ?_⟩
      show g.g s ((chartTriv n x).symmL ℝ s q.2) (T.X s) = -1
      rw [pairing_timeOrientation_symmL T x s hsP q.2,
        Lightlike.Geodesic.pairing_comm hg1 (ψ.map_source hsP)]
      exact hℓ
  rw [hset]
  exact hKpc.image_of_continuousOn hΦc

/-- **The normalised null vectors over a compact set are a compact set of the tangent bundle.** -/
theorem compact_normalised_null (T : Causal.TimeOrientation g) {S : Set M} (hS : IsCompact S) :
    IsCompact {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∧ IsNullVec g z ∧
      g.g z.proj z.snd (T.X z.proj) = -1} := by
  classical
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
  have hloc : ∀ p : M, ∃ P : Set M, IsCompact P ∧ p ∈ interior P ∧
      P ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source := fun p =>
    exists_compact_subset (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)
      (mem_extChartAt_source p)
  choose P hPc hPi hPs using hloc
  obtain ⟨b, hbS, hbfin, hbcov⟩ := hS.elim_finite_subcover_image
    (fun p _ => isOpen_interior (s := P p)) (fun p hp => mem_iUnion₂.2 ⟨p, hp, hPi p⟩)
  have hset : {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∧ IsNullVec g z ∧
      g.g z.proj z.snd (T.X z.proj) = -1} =
      ⋃ p ∈ b, {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∩ P p ∧ IsNullVec g z ∧
        g.g z.proj z.snd (T.X z.proj) = -1} := by
    ext z
    constructor
    · rintro ⟨hzS, hz1, hz2⟩
      obtain ⟨p, hpb, hzp⟩ := mem_iUnion₂.1 (hbcov hzS)
      exact mem_iUnion₂.2 ⟨p, hpb, ⟨hzS, interior_subset hzp⟩, hz1, hz2⟩
    · intro hz
      obtain ⟨p, -, ⟨hzS, -⟩, hz1, hz2⟩ := mem_iUnion₂.1 hz
      exact ⟨hzS, hz1, hz2⟩
  rw [hset]
  exact hbfin.isCompact_biUnion fun p _ => compact_normalised_null_piece T p hS (hPc p) (hPs p)

end Lightlike.Penrose

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- A geodesic curve is differentiable (as a map of manifolds) at each point of its domain. -/
theorem IsGeodesicCurveOn.mdifferentiableAt {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (h : IsGeodesicCurveOn g γ J) {t : ℝ} (ht : t ∈ J) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t := by
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t ht
  have hO' : IsOpen (interior O) := isOpen_interior
  exact (phase_coord g (γ t) hO' (fun s hs => hsrc s (interior_subset hs))
    ⟨fun s hs => hgeo.pos s (interior_subset hs), fun s hs => hgeo.vel s (interior_subset hs)⟩
    (mem_interior_iff_mem_nhds.2 hO)).1

/-- **A null geodesic on `[0, L]` extends to a complete null geodesic**, with the same one-sided
velocity at `0`. -/
theorem generator_extend (hc : NullGeodesicallyComplete g) {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : IsNullGeodesicOn g γ (Icc 0 L)) :
    ∃ γ' : ℝ → M, IsNullGeodesicOn g γ' univ ∧ EqOn γ γ' (Icc 0 L) ∧
      (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0 : Fin n → ℝ) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' 0 (1 : ℝ) := by
  obtain ⟨γ', hγ', heq⟩ := hc γ 0 L hL (hγ.mono Ioo_subset_Icc_self)
  have hcont : ContinuousOn γ (Icc 0 L) := fun t ht =>
    (IsGeodesicCurveOn.continuousAt g hγ.isGeodesicCurveOn ht).continuousWithinAt
  have hcont' : ContinuousOn γ' (Icc 0 L) := fun t ht =>
    (IsGeodesicCurveOn.continuousAt g hγ'.isGeodesicCurveOn (mem_univ t)).continuousWithinAt
  have heqI : EqOn γ γ' (Icc 0 L) := by
    refine heq.of_subset_closure hcont hcont' Ioo_subset_Icc_self ?_
    rw [closure_Ioo hL.ne]
  refine ⟨γ', hγ', heqI, ?_⟩
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' 0 :=
    IsGeodesicCurveOn.mdifferentiableAt isOpen_univ hγ'.isGeodesicCurveOn (mem_univ 0)
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) L) 0 :=
    (uniqueDiffOn_Icc hL 0 ⟨le_rfl, hL.le⟩).uniqueMDiffWithinAt
  unfold Causal.velocity
  have hev : γ =ᶠ[𝓝[Icc 0 L] 0] γ' := by
    filter_upwards [self_mem_nhdsWithin] with t ht using heqI ht
  rw [hev.mfderivWithin_eq (heqI ⟨le_rfl, hL.le⟩), mfderivWithin_eq_mfderiv hu hmd]
  rfl

end Lightlike.Penrose

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- A null geodesic has a nonzero null velocity at each parameter. -/
theorem nullAt_of_isNullGeodesicOn {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (h : IsNullGeodesicOn g γ J) {t : ℝ} (ht : t ∈ J) : NullAt g γ t := by
  obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := h t ht
  have hO' : IsOpen (interior O) := isOpen_interior
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) w (interior O) :=
    ⟨fun s hs => hgeo.pos s (interior_subset hs), fun s hs => hgeo.vel s (interior_subset hs)⟩
  have hcoord := (phase_coord g (γ t) hO' (fun s hs => hsrc s (interior_subset hs)) hgeo'
    (mem_interior_iff_mem_nhds.2 hO)).2
  exact (nullAt_iff_chart g (γ t) (hsrc t (mem_of_mem_nhds hO)) hcoord).2 ⟨hbil, hw0⟩

/-- **The phase of a rescaled geodesic curve.** For a geodesic curve `γ` on an open set containing
`c t`, the velocity of `s ↦ γ (c s)` at `t` is `c` times the velocity of `γ` at `c t`. -/
theorem velocity_scale {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (h : IsGeodesicCurveOn g γ J)
    (c : ℝ) {t : ℝ} (ht : c * t ∈ J) :
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun s => γ (c * s)) t (1 : ℝ) : Fin n → ℝ) =
      c • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (c * t) (1 : ℝ) := by
  have hJ' : IsOpen ((fun s : ℝ => c * s) ⁻¹' J) := hJ.preimage (by fun_prop)
  have hsc := IsGeodesicCurveOn.scale g h c
  have ht' : t ∈ (fun s : ℝ => c * s) ⁻¹' J := ht
  set x := γ (c * t) with hx
  have e1 := deriv_chart_eq_phase g hJ' hsc ht'
  have e2 := deriv_chart_eq_phase g hJ h ht
  have hd : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ (c * s))) t =
      c • deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) (c * t) := by
    have := deriv_comp_mul_left (c := c) (x := t)
      (f := fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s))
    simpa [smul_eq_mul] using this
  have hxb : x ∈ (chartTriv n x).baseSet := mem_baseSet_of_mem_source x x (mem_extChartAt_source x)
  have hLE : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨x, v⟩).2 =
      (chartTriv n x).linearEquivAt ℝ x hxb v := fun v => by
    rw [Trivialization.linearEquivAt_apply]
  have e1' : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ (c * s))) t =
      (chartTriv n x).linearEquivAt ℝ x hxb
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun s => γ (c * s)) t (1 : ℝ)) := by
    rw [← hLE]; exact e1
  have e2' : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) (c * t) =
      (chartTriv n x).linearEquivAt ℝ x hxb
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (c * t) (1 : ℝ)) := by
    rw [← hLE]; exact e2
  rw [hd, e2', ← map_smul] at e1'
  exact ((chartTriv n x).linearEquivAt ℝ x hxb).injective e1'.symm

/-- **The normalised focal bound** (the output of the focusing theorem, a hypothesis of the cover):
every future null geodesic from `S` to a point outside `I⁺(S)` has normalised affine length
`-g(γ'(0), X) · L ≤ Λ`. -/
def NormalisedFocalBound (T : Causal.TimeOrientation g) (S : Set M) (Λ : ℝ) : Prop :=
  ∀ (γ : ℝ → M) (L : ℝ), 0 < L → IsFutureNullGeodesicOn T γ (Icc 0 L) → γ 0 ∈ S →
    γ L ∉ Causal.chronFutureSet T S →
    -(g.g (γ 0) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0) (T.X (γ 0))) * L ≤ Λ

/-- **A compact cover of the boundary of the causal future** from the focal bound. -/
theorem exists_compact_cover_of_focal (T : Causal.TimeOrientation g)
    (hc : NullGeodesicallyComplete g) {S : Set M} (hS : IsCompact S) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hfocal : NormalisedFocalBound T S Λ) (hclosed : IsClosed (Causal.causalFutureSet T S)) :
    ∃ C : Set M, IsCompact C ∧ frontier (Causal.causalFutureSet T S) ⊆ C := by
  obtain ⟨C₀, hC₀, hC₀prop⟩ := compact_nullExp_image g hc (compact_normalised_null T hS)
    (fun z hz => hz.2.1) hΛ
  refine ⟨S ∪ C₀, hS.union hC₀, fun q hq => ?_⟩
  have hqJ : q ∈ Causal.causalFutureSet T S := by
    have := hq.1
    rwa [hclosed.closure_eq] at this
  have hqI : q ∉ Causal.chronFutureSet T S := fun h =>
    hq.2 (Causal.chronFutureSet_subset_interior T S h)
  rcases exists_generator T hqJ hqI with hqS | ⟨s, hs, γ, L, hL, hγ, h0, hLq⟩
  · exact Or.inl hqS
  · right
    obtain ⟨γ', hγ', heq, hvel⟩ := generator_extend hc hL hγ.1
    have h0L : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
    have hfut := hγ.2 0 h0L
    set c : ℝ := -(g.g (γ 0) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0) (T.X (γ 0))) with hcdef
    have hcpos : 0 < c := by rw [hcdef]; linarith
    have hfoc := hfocal γ L hL hγ (h0 ▸ hs) (hLq ▸ hqI)
    set γ'' : ℝ → M := fun τ => γ' (c⁻¹ * τ) with hγ''
    have hγ''null : IsNullGeodesicOn g γ'' univ := by
      have := hγ'.comp_affine (inv_ne_zero hcpos.ne') 0
      simpa [hγ''] using this
    have hγ0 : γ' 0 = γ 0 := (heq h0L).symm
    have hp0 : γ' (c⁻¹ * 0) = γ 0 := by rw [mul_zero]; exact hγ0
    have hnull0 := nullAt_of_isNullGeodesicOn isOpen_univ hγ' (mem_univ (c⁻¹ * 0))
    have hsnd := velocity_scale (g := g) isOpen_univ hγ'.isGeodesicCurveOn c⁻¹ (t := 0) (mem_univ _)
    have hu : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ) : Fin n → ℝ) =
        Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0 := by
      rw [hvel, mul_zero]
    have key : ∀ (p q : M) (h : p = q) (w : Fin n → ℝ), g.g p w (T.X p) = g.g q w (T.X q) := by
      intro p q h w; subst h; rfl
    have hz : phase (n := n) γ'' 0 ∈ {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M | z.proj ∈ S ∧
        IsNullVec g z ∧ g.g z.proj z.snd (T.X z.proj) = -1} := by
      refine ⟨by show γ' (c⁻¹ * 0) ∈ S; rw [hp0, h0]; exact hs, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · show g.g (γ'' 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ'' 0 (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ'' 0 (1 : ℝ)) = 0
          rw [hsnd]
          have h1 := hnull0.1
          simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
          have h1' : g.g (γ' (c⁻¹ * 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ)) = 0 := h1
          rw [h1']; ring
        · show mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ'' 0 (1 : ℝ) ≠ 0
          rw [hsnd]
          exact smul_ne_zero (inv_ne_zero hcpos.ne') hnull0.2
      · show g.g (γ'' 0) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ'' 0 (1 : ℝ)) (T.X (γ'' 0)) = -1
        rw [hsnd]
        simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        have e1 := key (γ' (c⁻¹ * 0)) (γ 0) hp0
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ))
        have e2 : g.g (γ' (c⁻¹ * 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ))
            (T.X (γ' (c⁻¹ * 0))) = -c := by
          rw [e1, hu, hcdef]; ring
        show c⁻¹ * g.g (γ' (c⁻¹ * 0)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ' (c⁻¹ * 0) (1 : ℝ))
            (T.X (γ' (c⁻¹ * 0))) = -1
        rw [e2]; field_simp
    have hmem := hC₀prop _ hz γ'' hγ''null rfl (c * L) ⟨mul_nonneg hcpos.le hL.le, hfoc⟩
    have : γ'' (c * L) = q := by
      simp only [hγ'']
      rw [inv_mul_cancel_left₀ hcpos.ne', ← hLq]
      exact (heq ⟨hL.le, le_rfl⟩).symm
    rwa [this] at hmem

end Lightlike.Penrose
