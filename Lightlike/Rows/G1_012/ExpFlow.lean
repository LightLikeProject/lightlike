import Lightlike.Rows.G1_012.GeodesicChartConverse
import Lightlike.Rows.G1_012.GeodesicUnique
import Lightlike.Rows.G1_012.NullGeodGlue
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
      N ∈ 𝓝 z₀ ∧ 0 < δ ∧ (∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-δ) δ) ∧ phase (n := n) (Γ z) 0 = z) ∧
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
  refine ⟨N, T, Γ, hNo.mem_nhds hz₀N, hT, fun z hz => ⟨hΓgeo z hz, hphase0 z hz⟩, ?_⟩
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

end Lightlike.Penrose
