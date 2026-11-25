import Lightlike.Spacetime.PenroseSingularity.GeodesicChartConverse
import Lightlike.Spacetime.PenroseSingularity.GeodesicUnique
import Lightlike.Spacetime.PenroseSingularity.NullGeodGlue
import Lightlike.Geodesic.ExpJoint

/-!
# Continuity of the geodesic flow of a Lorentzian manifold (G1-012)

The geodesic flow `(p, v, t) ↦ (γ t, γ' t)` is jointly continuous on its (open) domain, where
`(p, v)` are chart coordinates of an initial point and velocity. The local statement is the flow box
of the geodesic spray in a chart (`exists_phase_flow`); it is propagated along a compact interval of
times by continuous induction (`flow_continuous`), changing charts with the `C¹` coordinate changes.
-/

open Bundle Manifold Set Filter Topology Matrix Metric
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The phase flow box of the geodesic equation near a point of phase space.** -/
theorem exists_phase_flow (hg : Lightlike.IsCoordMetric g U) {p₀ v₀ : Fin n → ℝ} (hp : p₀ ∈ U) :
    ∃ (r T : ℝ) (Φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)),
      0 < r ∧ 0 < T ∧
      ContinuousOn (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Φ q.1 q.2)
        (Ioo (-T) T ×ˢ ball ((p₀, v₀) : (Fin n → ℝ) × (Fin n → ℝ)) r) ∧
      (∀ q ∈ ball ((p₀, v₀) : (Fin n → ℝ) × (Fin n → ℝ)) r, Φ 0 q = q) ∧
      ∀ q ∈ ball ((p₀, v₀) : (Fin n → ℝ) × (Fin n → ℝ)) r, ∀ t ∈ Ioo (-T) T,
        (Φ t q).1 ∈ U ∧ HasDerivAt (fun s => (Φ s q).1) (Φ t q).2 t ∧
        HasDerivAt (fun s => (Φ s q).2) (accel g (Φ t q).1 (Φ t q).2) t := by
  set q₀ : (Fin n → ℝ) × (Fin n → ℝ) := (p₀, v₀) with hq₀
  have hopen : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hg.isOpen.prod isOpen_univ
  obtain ⟨aU, haU, hballU⟩ := Metric.isOpen_iff.mp hopen q₀ (mk_mem_prod hp (mem_univ _))
  obtain ⟨A, hA, H⟩ := Lightlike.ODE.exists_isFlowBox (contDiffAt_geodField hg hp v₀)
  set a : ℝ := min A aU with ha
  have ha0 : 0 < a := lt_min hA haU
  obtain ⟨r, T, K, Φ, h⟩ := H a ha0 (min_le_left _ _)
  have hsm : ContDiffOn ℝ ∞ (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Φ q.1 q.2)
      (Ioo (-T) T ×ˢ ball q₀ r) :=
    h.contDiffOn_uncurry_infty ((contDiffOn_geodField hg).mono
      ((ball_subset_ball (min_le_right _ _)).trans hballU))
  refine ⟨r, T, Φ, h.r_pos, h.T_pos, hsm.continuousOn, h.flow_zero, fun q hq t ht => ?_⟩
  have htI : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
  have hmem := h.flow_mem q hq t htI
  have hU1 : (Φ t q).1 ∈ U :=
    (ball_subset_ball (min_le_right _ _)).trans hballU hmem |>.1
  have hd := h.hasDerivAt q hq t htI
  exact ⟨hU1, hd.fst, hd.snd⟩

end Lightlike.Geodesic

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The phase `(γ t, γ' t)` of a curve as a point of the tangent bundle. -/
def phase (γ : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, Fin n → ℝ) M :=
  ⟨γ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ t (1 : ℝ)⟩

/-- **A chart geodesic is differentiable, and its tangent has the chart velocity as coordinates.** -/
theorem phase_coord (x : M) {γ : ℝ → M} {O : Set ℝ} (hO : IsOpen O)
    (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) {w : ℝ → Fin n → ℝ}
    (hgeo : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x)
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) x (γ s)) w O) {s : ℝ} (hs : s ∈ O) :
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ∧
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x (phase γ s)).2 = w s := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set u : ℝ → Fin n → ℝ := fun s => ψ (γ s) with hu
  have hdu : HasDerivAt u (w s) s := hgeo.pos s hs
  have htarget : ∀ t' ∈ O, u t' ∈ ψ.target := fun t' ht' => ψ.map_source (hsrc t' ht')
  obtain ⟨hmd, hvel⟩ := Causal.mdifferentiableWithinAt_chart_symm (I := 𝓘(ℝ, Fin n → ℝ)) x
    (hO.uniqueDiffWithinAt hs) hs hdu.hasDerivWithinAt htarget
  have hnhds : O ∈ 𝓝 s := hO.mem_nhds hs
  have hev : γ =ᶠ[𝓝 s] ψ.symm ∘ u := by
    filter_upwards [hnhds] with r hr
    exact (ψ.left_inv (hsrc r hr)).symm
  have hmd' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (ψ.symm ∘ u) s :=
    hmd.mdifferentiableAt hnhds
  refine ⟨hmd'.congr_of_eventuallyEq hev, ?_⟩
  have hγs : γ s = (ψ.symm ∘ u) s := (ψ.left_inv (hsrc s hs)).symm
  have hv1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s (1 : ℝ) =
      Causal.velocity 𝓘(ℝ, Fin n → ℝ) (ψ.symm ∘ u) O s := by
    unfold Causal.velocity
    rw [mfderivWithin_of_mem_nhds hnhds, hev.mfderiv_eq]
    rfl
  have key : ∀ (a b : M) (v : Fin n → ℝ), a = b →
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨a, v⟩).2 = (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨b, v⟩).2 := by
    intro a b v h; subst h; rfl
  unfold phase
  rw [key _ _ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s (1 : ℝ)) hγs, hv1]
  exact hvel

/-- **The phase of a geodesic curve is continuous** (in the topology of the tangent bundle). -/
theorem phase_continuousAt {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (h : IsGeodesicCurveOn g γ I)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) : ContinuousAt (phase (n := n) γ) t₀ := by
  refine (FiberBundle.continuousAt_totalSpace (F := Fin n → ℝ)
    (E := TangentSpace 𝓘(ℝ, Fin n → ℝ)) (phase γ)).2 ⟨IsGeodesicCurveOn.continuousAt g h ht₀, ?_⟩
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t₀ ht₀
  set O' : Set ℝ := interior O ∩ I with hO'
  have hO'o : IsOpen O' := isOpen_interior.inter hI
  have ht₀O' : t₀ ∈ O' := ⟨mem_interior_iff_mem_nhds.2 hO, ht₀⟩
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t₀))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t₀) (γ s)) w O' :=
    ⟨fun s hs => hgeo.pos s (interior_subset hs.1), fun s hs => hgeo.vel s (interior_subset hs.1)⟩
  have hcoord : ∀ s ∈ O', (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t₀) (phase γ s)).2 = w s := fun s hs =>
    (phase_coord g (γ t₀) hO'o (fun r hr => hsrc r (interior_subset hr.1)) hgeo' hs).2
  have hwc : ContinuousAt w t₀ := (hgeo.vel t₀ (mem_of_mem_nhds hO)).continuousAt
  refine hwc.congr ?_
  filter_upwards [hO'o.mem_nhds ht₀O'] with s hs
  exact (hcoord s hs).symm

/-- **Geodesic curves with the same phase at one time agree.** -/
theorem eqOn_of_phase_eq {γ₁ γ₂ : ℝ → M} {J : Set ℝ} (hJo : IsOpen J) (hJc : IsPreconnected J)
    (h₁ : IsGeodesicCurveOn g γ₁ J) (h₂ : IsGeodesicCurveOn g γ₂ J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (h0 : γ₁ t₀ = γ₂ t₀)
    (h1 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ₁ t₀ (1 : ℝ) : Fin n → ℝ) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ₂ t₀ (1 : ℝ)) : EqOn γ₁ γ₂ J := by
  refine IsGeodesicCurveOn.eqOn g hJo hJc h₁ h₂ ht₀ h0 ?_
  obtain ⟨w₁, O₁, hO₁, hs₁, hg₁⟩ := h₁ t₀ ht₀
  obtain ⟨w₂, O₂, hO₂, hs₂, hg₂⟩ := h₂ t₀ ht₀
  have hs₂' : ∀ s ∈ O₂, γ₂ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ₁ t₀)).source := by
    intro s hs; rw [h0]; exact hs₂ s hs
  have hg₂' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ₁ t₀))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ₁ t₀) (γ₂ s)) w₂ O₂ := by
    rw [h0]; exact hg₂
  have hO₁' : IsOpen (interior O₁) := isOpen_interior
  have hO₂' : IsOpen (interior O₂) := isOpen_interior
  have e1 := phase_coord g (γ₁ t₀) hO₁' (fun s hs => hs₁ s (interior_subset hs))
    ⟨fun s hs => hg₁.pos s (interior_subset hs), fun s hs => hg₁.vel s (interior_subset hs)⟩
    (mem_interior_iff_mem_nhds.2 hO₁)
  have e2 := phase_coord g (γ₁ t₀) hO₂' (fun s hs => hs₂' s (interior_subset hs))
    ⟨fun s hs => hg₂'.pos s (interior_subset hs), fun s hs => hg₂'.vel s (interior_subset hs)⟩
    (mem_interior_iff_mem_nhds.2 hO₂)
  have d1 := (hg₁.pos t₀ (mem_of_mem_nhds hO₁)).deriv
  have d2 := (hg₂'.pos t₀ (mem_of_mem_nhds hO₂)).deriv
  rw [d1, d2, ← e1.2, ← e2.2]
  unfold phase
  have key : ∀ (a b : M) (v w : Fin n → ℝ), a = b → v = w →
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ₁ t₀) ⟨a, v⟩).2 = (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ₁ t₀) ⟨b, w⟩).2 := by
    intro a b v w ha hv; subst ha; subst hv; rfl
  exact key _ _ _ _ h0 h1

theorem chartTriv_baseSet_eq (x : M) :
    (Lightlike.chartTriv n x).baseSet = (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := by
  simp [Lightlike.chartTriv]

/-- **Local flow of the geodesic equation, on the tangent bundle.** -/
theorem exists_local_flow (z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) :
    ∃ (N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (δ : ℝ)
      (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M),
      IsOpen N ∧ z₀ ∈ N ∧ 0 < δ ∧ (∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-δ) δ) ∧ phase (n := n) (Γ z) 0 = z) ∧
      ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2)
        (N ×ˢ Ioo (-δ) δ) := by
  set x : M := z₀.proj with hx
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set e := Lightlike.chartTriv n x with he
  have hg := g.toNondegMetric.isCoordMetric_coordMetric x
  have hxs : x ∈ ψ.source := mem_extChartAt_source x
  have hxt : ψ x ∈ ψ.target := ψ.map_source hxs
  obtain ⟨r, T, Φ, hr, hT, hΦc, hΦ0, hΦ⟩ :=
    Lightlike.Geodesic.exists_phase_flow hg hxt (v₀ := (e z₀).2)
  set q₀ : (Fin n → ℝ) × (Fin n → ℝ) := (ψ x, (e z₀).2) with hq₀
  set c : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → (Fin n → ℝ) × (Fin n → ℝ) := fun z =>
    (ψ z.proj, (e z).2) with hc
  have hzsrc : ∀ z ∈ e.source, z.proj ∈ ψ.source := fun z hz => by
    have := e.mem_source.1 hz
    rwa [he, chartTriv_baseSet_eq] at this
  have hcc : ContinuousOn c e.source := by
    refine ContinuousOn.prodMk ?_ ?_
    · exact (continuousOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) x).comp e.continuousOn_proj
        (fun z hz => hzsrc z hz)
    · exact continuous_snd.comp_continuousOn e.continuousOn
  have hz₀ : z₀ ∈ e.source := by
    rw [e.mem_source, he, chartTriv_baseSet_eq]; exact hxs
  set N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := e.source ∩ c ⁻¹' ball q₀ r with hN
  have hNo : IsOpen N := hcc.isOpen_inter_preimage e.open_source isOpen_ball
  have hz₀N : z₀ ∈ N := ⟨hz₀, by
    show c z₀ ∈ ball q₀ r
    have : c z₀ = q₀ := by simp only [hc, hq₀, hx]
    rw [this]; exact mem_ball_self hr⟩
  have hΦU : ∀ z ∈ N, ∀ t ∈ Ioo (-T) T, (Φ t (c z)).1 ∈ ψ.target := fun z hz t ht =>
    (hΦ (c z) hz.2 t ht).1
  set Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M := fun z t => ψ.symm (Φ t (c z)).1 with hΓ
  have hgeoΓ : ∀ z ∈ N, Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x)
      (fun s => ψ (Γ z s)) (fun s => (Φ s (c z)).2) (Ioo (-T) T) := by
    intro z hz
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · refine ((hΦ (c z) hz.2 t ht).2.1).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      simp only [hΓ]
      exact ψ.right_inv (hΦU z hz s hs)
    · have h2 := (hΦ (c z) hz.2 t ht).2.2
      simp only [hΓ]
      rw [ψ.right_inv (hΦU z hz t ht)]
      exact h2
  have hΓsrc : ∀ z ∈ N, ∀ s ∈ Ioo (-T) T, Γ z s ∈ ψ.source := fun z hz s hs =>
    ψ.map_target (hΦU z hz s hs)
  have hΓgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-T) T) := fun z hz =>
    isGeodesicCurveOn_of_chart g x isOpen_Ioo (hΓsrc z hz) (hgeoΓ z hz)
  -- the phase of the local flow in the trivialization
  have hphase : ∀ z ∈ N, ∀ t ∈ Ioo (-T) T,
      e (phase (n := n) (Γ z) t) = (Γ z t, (Φ t (c z)).2) := by
    intro z hz t ht
    obtain ⟨-, hco⟩ := phase_coord g x isOpen_Ioo (hΓsrc z hz) (hgeoΓ z hz) ht
    have hb : Γ z t ∈ e.baseSet := by
      rw [he, chartTriv_baseSet_eq]; exact hΓsrc z hz t ht
    have hsrc' : phase (n := n) (Γ z) t ∈ e.source := by
      rw [e.mem_source]; exact hb
    have h1 : (e (phase (n := n) (Γ z) t)).1 = Γ z t := by
      rw [e.coe_fst hsrc']; rfl
    exact Prod.ext h1 hco
  have hT0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT⟩
  have hphase0 : ∀ z ∈ N, phase (n := n) (Γ z) 0 = z := by
    intro z hz
    have h1 := hphase z hz 0 hT0
    have hzs := hzsrc z hz.1
    have hΓ0 : Γ z 0 = z.proj := by
      simp only [hΓ, hΦ0 (c z) hz.2]
      exact ψ.left_inv hzs
    have hz2 : e z = (z.proj, (e z).2) := by
      refine Prod.ext (e.coe_fst hz.1) rfl
    have hb : Γ z 0 ∈ e.baseSet := by
      rw [he, chartTriv_baseSet_eq]; exact hΓsrc z hz 0 hT0
    have hsrc' : phase (n := n) (Γ z) 0 ∈ e.source := by
      rw [e.mem_source]; exact hb
    refine e.toOpenPartialHomeomorph.injOn hsrc' hz.1 ?_
    show e (phase (n := n) (Γ z) 0) = e z
    rw [h1, hz2, hΓ0, hΦ0 (c z) hz.2]
  refine ⟨N, T, Γ, hNo, hz₀N, hT, fun z hz => ⟨hΓgeo z hz, hphase0 z hz⟩, ?_⟩
  -- continuity
  have hmaps : MapsTo (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (zs.2, c zs.1))
      (N ×ˢ Ioo (-T) T) (Ioo (-T) T ×ˢ ball q₀ r) := fun zs hzs => ⟨hzs.2, hzs.1.2⟩
  have hcN : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (zs.2, c zs.1))
      (N ×ˢ Ioo (-T) T) :=
    continuousOn_snd.prodMk ((hcc.mono (fun z hz => hz.1)).comp continuousOn_fst
      (fun zs hzs => hzs.1))
  have hΦcont : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      Φ zs.2 (c zs.1)) (N ×ˢ Ioo (-T) T) := hΦc.comp hcN hmaps
  have hbcont : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => Γ zs.1 zs.2)
      (N ×ˢ Ioo (-T) T) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x).comp
      (continuous_fst.comp_continuousOn hΦcont) (fun zs hzs => hΦU zs.1 hzs.1 zs.2 hzs.2)
  have hsymm := e.continuousOn_symm
  have hmap2 : MapsTo (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (Γ zs.1 zs.2, (Φ zs.2 (c zs.1)).2))
      (N ×ˢ Ioo (-T) T) (e.baseSet ×ˢ univ) := fun zs hzs => by
    refine ⟨?_, trivial⟩
    rw [he, chartTriv_baseSet_eq]; exact hΓsrc zs.1 hzs.1 zs.2 hzs.2
  have hcomp := hsymm.comp (hbcont.prodMk (continuous_snd.comp_continuousOn hΦcont)) hmap2
  refine hcomp.congr fun zs hzs => ?_
  have h1 := hphase zs.1 hzs.1 zs.2 hzs.2
  have hb : Γ zs.1 zs.2 ∈ e.baseSet := by
    rw [he, chartTriv_baseSet_eq]; exact hΓsrc zs.1 hzs.1 zs.2 hzs.2
  have hsrc' : phase (n := n) (Γ zs.1) zs.2 ∈ e.source := by
    rw [e.mem_source]; exact hb
  have := e.symm_apply_apply hsrc'
  rw [h1] at this
  show phase (n := n) (Γ zs.1) zs.2 = TotalSpace.mk' (Fin n → ℝ) (Γ zs.1 zs.2) (e.symm (Γ zs.1 zs.2) (Φ zs.2 (c zs.1)).2)
  exact this.symm.trans (Trivialization.mk_symm e hb (Φ zs.2 (c zs.1)).2).symm

/-- **Geodesic curves are local**: they depend only on the germ of the curve at each parameter. -/
theorem IsGeodesicCurveOn.congr_eventuallyEq {γ γ' : ℝ → M} {J : Set ℝ}
    (h : IsGeodesicCurveOn g γ J) (hev : ∀ t ∈ J, γ =ᶠ[𝓝 t] γ') : IsGeodesicCurveOn g γ' J := by
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t ht
  have hev' := hev t ht
  have hγt : γ' t = γ t := (hev'.self_of_nhds).symm
  set O' : Set ℝ := {s | γ s = γ' s} ∩ O with hO'
  have hO'n : O' ∈ 𝓝 t := Filter.inter_mem hev' hO
  refine ⟨w, interior O', interior_mem_nhds.2 hO'n, fun s hs => ?_, ?_⟩
  · have hs' := interior_subset hs
    rw [hγt, ← hs'.1]; exact hsrc s hs'.2
  · refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs' := interior_subset hs
      have h1 := hgeo.pos s hs'.2
      rw [hγt]
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [mem_interior_iff_mem_nhds.1 hs] with r hr
      show _ = _
      rw [hr.1]
    · have hs' := interior_subset hs
      have h1 := hgeo.vel s hs'.2
      rw [hγt]
      rw [show γ' s = γ s from hs'.1.symm]
      exact h1

open Classical in
/-- **Gluing geodesic curves**: two geodesic curves on open intervals that agree on the overlap
glue to a geodesic curve on the union. -/
theorem IsGeodesicCurveOn.exists_union {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ}
    (h₁ : IsGeodesicCurveOn g γ₁ J₁) (h₂ : IsGeodesicCurveOn g γ₂ J₂) (hJ₁ : IsOpen J₁)
    (hJ₂ : IsOpen J₂) (hag : EqOn γ₁ γ₂ (J₁ ∩ J₂)) :
    ∃ γ : ℝ → M, IsGeodesicCurveOn g γ (J₁ ∪ J₂) ∧ (∀ σ ∈ J₁, γ σ = γ₁ σ) ∧
      ∀ σ ∈ J₂, γ σ = γ₂ σ := by
  have e1 : ∀ σ ∈ J₁, (fun s => if s ∈ J₁ then γ₁ s else γ₂ s) σ = γ₁ σ := fun σ hσ => by simp [hσ]
  have e2 : ∀ σ ∈ J₂, (fun s => if s ∈ J₁ then γ₁ s else γ₂ s) σ = γ₂ σ := by
    intro σ hσ
    by_cases h1 : σ ∈ J₁
    · simp [h1, hag ⟨h1, hσ⟩]
    · simp [h1]
  refine ⟨_, ?_, e1, e2⟩
  intro t ht
  rcases ht with ht | ht
  · exact (IsGeodesicCurveOn.congr_eventuallyEq g h₁ (fun s hs => by
      filter_upwards [hJ₁.mem_nhds hs] with r hr using (e1 r hr).symm)) t ht
  · exact (IsGeodesicCurveOn.congr_eventuallyEq g h₂ (fun s hs => by
      filter_upwards [hJ₂.mem_nhds hs] with r hr using (e2 r hr).symm)) t ht

/-- **Shifting a geodesic curve in the parameter.** -/
theorem IsGeodesicCurveOn.shift {γ : ℝ → M} {J : Set ℝ} (h : IsGeodesicCurveOn g γ J) (a : ℝ) :
    IsGeodesicCurveOn g (fun s => γ (s - a)) ((fun s => s - a) ⁻¹' J) := by
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h (t - a) ht
  refine ⟨fun s => w (s - a), (fun s => s - a) ⁻¹' O, ?_, fun s hs => hsrc _ hs, hgeo.shift a⟩
  exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds hO

/-- The derivative of the chart expression of a geodesic curve, in the chart at the point itself, is
the tangent coordinate of its phase. -/
theorem deriv_chart_eq_phase {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (h : IsGeodesicCurveOn g γ J)
    {t : ℝ} (ht : t ∈ J) :
    deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) t =
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) γ t)).2 := by
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h t ht
  have hO' : IsOpen (interior O) := isOpen_interior
  have e1 := phase_coord g (γ t) hO' (fun s hs => hsrc s (interior_subset hs))
    ⟨fun s hs => hgeo.pos s (interior_subset hs), fun s hs => hgeo.vel s (interior_subset hs)⟩
    (mem_interior_iff_mem_nhds.2 hO)
  rw [e1.2]
  exact (hgeo.pos t (mem_of_mem_nhds hO)).deriv

/-- **Two points of the tangent bundle over `x` with the same tangent coordinates in the chart at
`x` are equal.** -/
theorem tangent_ext (x : M) (z z' : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (hp : z.proj = x)
    (hp' : z'.proj = x)
    (hc : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x z).2 = (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x z').2) :
    z = z' := by
  set e := Lightlike.chartTriv n x with he
  have hz : z ∈ e.source := by
    rw [e.mem_source, he, chartTriv_baseSet_eq, hp]; exact mem_extChartAt_source x
  have hz' : z' ∈ e.source := by
    rw [e.mem_source, he, chartTriv_baseSet_eq, hp']; exact mem_extChartAt_source x
  refine e.toOpenPartialHomeomorph.injOn hz hz' ?_
  show e z = e z'
  refine Prod.ext ?_ hc
  rw [e.coe_fst hz, e.coe_fst hz', hp, hp']

/-- **The phase is determined by the germ of the curve.** -/
theorem phase_congr {γ γ' : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (h : IsGeodesicCurveOn g γ J)
    (h' : IsGeodesicCurveOn g γ' J) {t : ℝ} (ht : t ∈ J) (hev : γ =ᶠ[𝓝 t] γ') :
    phase (n := n) γ t = phase γ' t := by
  have hb : γ t = γ' t := hev.self_of_nhds
  refine tangent_ext (γ t) _ _ rfl hb.symm ?_
  have e1 := deriv_chart_eq_phase g hJ h ht
  have e2 := deriv_chart_eq_phase g hJ h' ht
  have hd : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) t =
      deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ' s)) t :=
    Filter.EventuallyEq.deriv_eq (hev.mono fun s hs => by simp only [hs])
  have e2' : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ' s)) t =
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) γ' t)).2 := by
    rw [hb]; exact e2
  show (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) γ t)).2 =
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) γ' t)).2
  rw [← e1, hd, e2']

/-- **The phase of a shifted curve.** -/
theorem phase_shift {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (h : IsGeodesicCurveOn g γ J) (a : ℝ)
    {t : ℝ} (ht : t ∈ J) :
    phase (n := n) (fun s => γ (s - a)) (t + a) = phase γ t := by
  have hJ' : IsOpen ((fun s : ℝ => s - a) ⁻¹' J) := hJ.preimage (continuous_id.sub continuous_const)
  have hsh := IsGeodesicCurveOn.shift g h a
  have hta : t + a ∈ (fun s : ℝ => s - a) ⁻¹' J := by simpa using ht
  have hb : (fun s => γ (s - a)) (t + a) = γ t := by simp
  refine tangent_ext (γ t) _ _ hb rfl ?_
  have e1 := deriv_chart_eq_phase g hJ' hsh hta
  have e2 := deriv_chart_eq_phase g hJ h ht
  simp only [add_sub_cancel_right] at e1
  have hd : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ (s - a))) (t + a) =
      deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) t := by
    have := deriv_comp_sub_const (a := a) (x := t + a)
      (f := fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s))
    simpa using this
  show (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) (fun s => γ (s - a)) (t + a))).2 =
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) (phase (n := n) γ t)).2
  rw [← e1, hd, e2]

/-- **Geodesic curves with the same phase at one time agree** (phase form). -/
theorem eqOn_of_phase_eq' {γ₁ γ₂ : ℝ → M} {J : Set ℝ} (hJo : IsOpen J) (hJc : IsPreconnected J)
    (h₁ : IsGeodesicCurveOn g γ₁ J) (h₂ : IsGeodesicCurveOn g γ₂ J) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hph : phase (n := n) γ₁ t₀ = phase γ₂ t₀) : EqOn γ₁ γ₂ J := by
  have h0 : γ₁ t₀ = γ₂ t₀ := congrArg Bundle.TotalSpace.proj hph
  refine IsGeodesicCurveOn.eqOn g hJo hJc h₁ h₂ ht₀ h0 ?_
  have e1 := deriv_chart_eq_phase g hJo h₁ ht₀
  have e2 := deriv_chart_eq_phase g hJo h₂ ht₀
  rw [← h0] at e2
  rw [e1, e2, hph]

/-- **The germ of the geodesic flow along `[0, t]` at `z₀`**: a neighbourhood `N` of `z₀` and
geodesic curves `Γ z`, `z ∈ N`, with phase `z` at `0`, defined on `(-ε, t + ε)`, whose phase is jointly
continuous. -/
def FlowGerm (z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ) : Prop :=
  ∃ (N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (ε : ℝ) (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M),
    IsOpen N ∧ z₀ ∈ N ∧ 0 < ε ∧
    (∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (t + ε)) ∧ phase (n := n) (Γ z) 0 = z) ∧
    ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2)
      (N ×ˢ Ioo (-ε) (t + ε))

/-- **Extending a flow germ by a local flow box.** -/
theorem flowGerm_step {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {t : ℝ} (ht : 0 ≤ t)
    {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hNo : IsOpen N) (hz₀ : z₀ ∈ N) (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (t + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    (hcont : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ zs.1) zs.2) (N ×ˢ Ioo (-ε) (t + ε)))
    {N' : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {δ' : ℝ}
    {Γ' : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hN'o : IsOpen N') (hδ' : 0 < δ')
    (hgeo' : ∀ z ∈ N', IsGeodesicCurveOn g (Γ' z) (Ioo (-δ') δ') ∧ phase (n := n) (Γ' z) 0 = z)
    (hcont' : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ' zs.1) zs.2) (N' ×ˢ Ioo (-δ') δ'))
    (hF : phase (n := n) (Γ z₀) t ∈ N') {t₂ : ℝ} (h1 : t ≤ t₂) (h2 : t₂ < t + δ') :
    FlowGerm g z₀ t₂ := by
  classical
  haveI : Nonempty M := ⟨z₀.proj⟩
  set J₁ : Set ℝ := Ioo (-ε) (t + ε) with hJ₁
  set J₂ : Set ℝ := Ioo (t - δ') (t + δ') with hJ₂
  have htJ₁ : t ∈ J₁ := ⟨by linarith, by linarith⟩
  have htJ₂ : t ∈ J₂ := ⟨by linarith, by linarith⟩
  set F : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → TangentBundle 𝓘(ℝ, Fin n → ℝ) M :=
    fun z => phase (n := n) (Γ z) t with hFdef
  have hFc : ContinuousOn F N :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz, htJ₁⟩)
  set N₁ := N ∩ F ⁻¹' N' with hN₁
  have hN₁o : IsOpen N₁ := hFc.isOpen_inter_preimage hNo hN'o
  have hz₀N₁ : z₀ ∈ N₁ := ⟨hz₀, hF⟩
  set G : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M := fun z s => Γ' (F z) (s - t) with hG
  have hJ₂eq : (fun s : ℝ => s - t) ⁻¹' Ioo (-δ') δ' = J₂ := by
    ext s
    simp only [mem_preimage, mem_Ioo, hJ₂]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hGgeo : ∀ z ∈ N₁, IsGeodesicCurveOn g (G z) J₂ := by
    intro z hz
    have := IsGeodesicCurveOn.shift g (hgeo' (F z) hz.2).1 t
    rw [hJ₂eq] at this
    exact this
  have hGphase : ∀ z ∈ N₁, phase (n := n) (G z) t = F z := by
    intro z hz
    have := phase_shift g isOpen_Ioo (hgeo' (F z) hz.2).1 t (t := 0) ⟨by linarith, hδ'⟩
    simp only [zero_add] at this
    have e : G z = fun s => Γ' (F z) (s - t) := rfl
    rw [e, this]
    exact (hgeo' (F z) hz.2).2
  have hagr : ∀ z ∈ N₁, EqOn (Γ z) (G z) (J₁ ∩ J₂) := by
    intro z hz
    exact eqOn_of_phase_eq' g (isOpen_Ioo.inter isOpen_Ioo)
      (ordConnected_Ioo.inter ordConnected_Ioo).isPreconnected
      ((hgeo z hz.1).1.mono inter_subset_left) ((hGgeo z hz).mono inter_subset_right)
      ⟨htJ₁, htJ₂⟩ (by rw [hGphase z hz])
  choose! Γ₂ hΓ₂ using fun z (hz : z ∈ N₁) =>
    IsGeodesicCurveOn.exists_union g (hgeo z hz.1).1 (hGgeo z hz) isOpen_Ioo isOpen_Ioo (hagr z hz)
  set ε₂ : ℝ := min ε (t + δ' - t₂) with hε₂
  have hε₂pos : 0 < ε₂ := lt_min hε (by linarith)
  have hsub : Ioo (-ε₂) (t₂ + ε₂) ⊆ J₁ ∪ J₂ := by
    intro σ hσ
    by_cases h : σ < t + ε
    · exact Or.inl ⟨by linarith [hσ.1, min_le_left ε (t + δ' - t₂)], h⟩
    · exact Or.inr ⟨by linarith [not_lt.1 h], by linarith [hσ.2, min_le_right ε (t + δ' - t₂)]⟩
  have hΓ₂J₁ : ∀ z ∈ N₁, ∀ s ∈ J₁, Γ₂ z s = Γ z s := fun z hz s hs => (hΓ₂ z hz).2.1 s hs
  have hΓ₂J₂ : ∀ z ∈ N₁, ∀ s ∈ J₂, Γ₂ z s = G z s := fun z hz s hs => (hΓ₂ z hz).2.2 s hs
  have hphJ₁ : ∀ z ∈ N₁, ∀ s ∈ J₁, phase (n := n) (Γ₂ z) s = phase (Γ z) s := by
    intro z hz s hs
    refine phase_congr g isOpen_Ioo ((hΓ₂ z hz).1.mono subset_union_left) (hgeo z hz.1).1 hs ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using hΓ₂J₁ z hz r hr
  have hphJ₂ : ∀ z ∈ N₁, ∀ s ∈ J₂, phase (n := n) (Γ₂ z) s = phase (Γ' (F z)) (s - t) := by
    intro z hz s hs
    have hs' : s - t ∈ Ioo (-δ') δ' := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have e1 : phase (n := n) (Γ₂ z) s = phase (G z) s := by
      refine phase_congr g isOpen_Ioo ((hΓ₂ z hz).1.mono subset_union_right) (hGgeo z hz) hs ?_
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using hΓ₂J₂ z hz r hr
    have e2 := phase_shift g isOpen_Ioo (hgeo' (F z) hz.2).1 t hs'
    simp only [sub_add_cancel] at e2
    rw [e1]
    exact e2
  refine ⟨N₁, ε₂, Γ₂, hN₁o, hz₀N₁, hε₂pos, fun z hz => ⟨(hΓ₂ z hz).1.mono hsub, ?_⟩, ?_⟩
  · have h0 : (0 : ℝ) ∈ J₁ := ⟨by linarith, by linarith⟩
    rw [hphJ₁ z hz 0 h0]
    exact (hgeo z hz.1).2
  · -- continuity
    have hA1 : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
        phase (n := n) (Γ₂ zs.1) zs.2) (N₁ ×ˢ J₁) := by
      refine (hcont.mono (prod_mono inter_subset_left subset_rfl)).congr fun zs hzs => ?_
      exact hphJ₁ zs.1 hzs.1 zs.2 hzs.2
    have hA2 : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
        phase (n := n) (Γ₂ zs.1) zs.2) (N₁ ×ˢ J₂) := by
      have hmap : MapsTo (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (F zs.1, zs.2 - t))
          (N₁ ×ˢ J₂) (N' ×ˢ Ioo (-δ') δ') := fun zs hzs =>
        ⟨hzs.1.2, ⟨by linarith [hzs.2.1], by linarith [hzs.2.2]⟩⟩
      have hc2 : ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (F zs.1, zs.2 - t))
          (N₁ ×ˢ J₂) :=
        ((hFc.mono inter_subset_left).comp continuousOn_fst (fun zs hzs => hzs.1)).prodMk
          (continuousOn_snd.sub continuousOn_const)
      refine (hcont'.comp hc2 hmap).congr fun zs hzs => ?_
      exact hphJ₂ zs.1 hzs.1 zs.2 hzs.2
    intro p hp
    by_cases h1 : p.2 ∈ J₁
    · exact ((hA1.continuousAt ((hN₁o.prod isOpen_Ioo).mem_nhds ⟨hp.1, h1⟩))).continuousWithinAt
    · have h2 : p.2 ∈ J₂ := by
        rcases hsub hp.2 with h | h
        · exact absurd h h1
        · exact h
      exact ((hA2.continuousAt ((hN₁o.prod isOpen_Ioo).mem_nhds ⟨hp.1, h2⟩))).continuousWithinAt

/-- **A flow germ restricts to earlier times.** -/
theorem FlowGerm.mono {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {t t' : ℝ}
    (h : FlowGerm g z₀ t) (h0 : 0 ≤ t') (htt : t' ≤ t) : FlowGerm g z₀ t' := by
  obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcont⟩ := h
  have hsub : Ioo (-ε) (t' + ε) ⊆ Ioo (-ε) (t + ε) := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨N, ε, Γ, hNo, hz₀, hε, fun z hz => ⟨(hgeo z hz).1.mono hsub, (hgeo z hz).2⟩,
    hcont.mono (prod_mono subset_rfl hsub)⟩

/-- A flow germ at `z₀` follows the given geodesic curve through `z₀`. -/
theorem FlowGerm.phase_eq {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {γ₀ : ℝ → M} {I₀ : Set ℝ}
    (hI₀ : IsOpen I₀) (hI₀c : I₀.OrdConnected) (hγ₀ : IsGeodesicCurveOn g γ₀ I₀)
    (hph : phase (n := n) γ₀ 0 = z₀)
    (h0 : 0 ∈ I₀) {t : ℝ} (ht : 0 ≤ t) (htI : t ∈ I₀) {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
    {ε : ℝ} {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hz₀ : z₀ ∈ N) (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (t + ε)) ∧ phase (n := n) (Γ z) 0 = z) :
    phase (n := n) (Γ z₀) t = phase γ₀ t := by
  have hJo : IsOpen (Ioo (-ε) (t + ε) ∩ I₀) := isOpen_Ioo.inter hI₀
  have hJc : IsPreconnected (Ioo (-ε) (t + ε) ∩ I₀) :=
    (ordConnected_Ioo.inter hI₀c).isPreconnected
  have h0J : (0 : ℝ) ∈ Ioo (-ε) (t + ε) ∩ I₀ := ⟨⟨by linarith, by linarith⟩, h0⟩
  have htJ : t ∈ Ioo (-ε) (t + ε) ∩ I₀ := ⟨⟨by linarith, by linarith⟩, htI⟩
  have heq := eqOn_of_phase_eq' g hJo hJc ((hgeo z₀ hz₀).1.mono inter_subset_left)
    (hγ₀.mono inter_subset_right) h0J (by rw [(hgeo z₀ hz₀).2, hph])
  refine phase_congr g hJo ((hgeo z₀ hz₀).1.mono inter_subset_left) (hγ₀.mono inter_subset_right)
    htJ ?_
  filter_upwards [hJo.mem_nhds htJ] with r hr using heq hr

/-- **The geodesic flow is continuous along a geodesic**: if `γ₀` is a geodesic curve on an open
interval `I₀ ⊇ [0, Λ]` with phase `z₀` at `0`, then there is a flow germ at `z₀` along `[0, Λ]`: all
geodesics with initial phase `z` near `z₀` exist on `(-ε, Λ + ε)` and their phases depend continuously on
`(z, s)`. -/
theorem flowGerm_along {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {γ₀ : ℝ → M} {I₀ : Set ℝ}
    (hI₀ : IsOpen I₀) (hI₀c : I₀.OrdConnected) (hγ₀ : IsGeodesicCurveOn g γ₀ I₀)
    (hph : phase (n := n) γ₀ 0 = z₀) (h0 : 0 ∈ I₀) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hsub : Icc 0 Λ ⊆ I₀) :
    ∀ t ∈ Icc 0 Λ, FlowGerm g z₀ t := by
  set s : Set ℝ := {t | FlowGerm g z₀ t} with hs
  -- the local flow box along `γ₀`
  have hbox : ∀ t ∈ Icc 0 Λ, ∃ (N' : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (δ' : ℝ)
      (Γ' : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M), IsOpen N' ∧ phase (n := n) γ₀ t ∈ N' ∧
      0 < δ' ∧ (∀ z ∈ N', IsGeodesicCurveOn g (Γ' z) (Ioo (-δ') δ') ∧ phase (n := n) (Γ' z) 0 = z) ∧
      ContinuousOn (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ' zs.1) zs.2)
        (N' ×ˢ Ioo (-δ') δ') := fun t _ => exists_local_flow g (phase (n := n) γ₀ t)
  have hmain : Icc 0 Λ ⊆ s := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · -- closedness
      refine isClosed_of_closure_subset fun t' ht' => ?_
      have ht'I : t' ∈ Icc 0 Λ := isClosed_Icc.closure_subset_iff.2 inter_subset_right ht'
      refine ⟨?_, ht'I⟩
      obtain ⟨N', δ', Γ', hN'o, hw, hδ', hgeo', hcont'⟩ := hbox t' ht'I
      have hpc : ContinuousAt (phase (n := n) γ₀) t' :=
        phase_continuousAt g hI₀ hγ₀ (hsub ht'I)
      obtain ⟨η, hη, hηN⟩ := Metric.eventually_nhds_iff.1 (hpc.eventually (hN'o.mem_nhds hw))
      set m : ℝ := min η δ' with hm
      have hmpos : 0 < m := lt_min hη hδ'
      obtain ⟨t, htm, hts⟩ := mem_closure_iff.1 ht' (Ioo (t' - m) (t' + m)) isOpen_Ioo
        ⟨by linarith, by linarith⟩
      have htI : t ∈ Icc 0 Λ := hts.2
      by_cases hle : t' ≤ t
      · exact FlowGerm.mono g hts.1 ht'I.1 hle
      · have hlt : t < t' := not_le.1 hle
        obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcont⟩ := hts.1
        have hF : phase (n := n) (Γ z₀) t ∈ N' := by
          rw [FlowGerm.phase_eq g hI₀ hI₀c hγ₀ hph h0 htI.1 (hsub htI) hz₀ hε hgeo]
          refine hηN ?_
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [htm.1, htm.2, min_le_left η δ']
        exact flowGerm_step g htI.1 hNo hz₀ hε hgeo hcont hN'o hδ' hgeo' hcont' hF hlt.le
          (by linarith [htm.1, min_le_right η δ'])
    · -- the start
      obtain ⟨N, δ, Γ, hNo, hz₀, hδ, hgeo, hcont⟩ := exists_local_flow g z₀
      exact ⟨N, δ, Γ, hNo, hz₀, hδ, fun z hz => by simpa using hgeo z hz, by simpa using hcont⟩
    · -- extension to the right
      rintro x ⟨hxs, hx0, hxΛ⟩
      have hxI : x ∈ Icc 0 Λ := ⟨hx0, hxΛ.le⟩
      obtain ⟨N', δ', Γ', hN'o, hw, hδ', hgeo', hcont'⟩ := hbox x hxI
      obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcont⟩ := hxs
      have hF : phase (n := n) (Γ z₀) x ∈ N' := by
        rw [FlowGerm.phase_eq g hI₀ hI₀c hγ₀ hph h0 hx0 (hsub hxI) hz₀ hε hgeo]
        exact hw
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show x < x + δ' by linarith)) ?_
      intro t₂ ht₂
      exact flowGerm_step g hx0 hNo hz₀ hε hgeo hcont hN'o hδ' hgeo' hcont' hF ht₂.1.le (by linarith [ht₂.2])
  exact fun t ht => hmain ht

end Lightlike.Penrose
