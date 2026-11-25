import Lightlike.Spacetime.PenroseSingularity.ExpFlow

/-!
# Smoothness of the geodesic flow of a Lorentzian manifold (G1-012, step D1)

The local flow box of the geodesic equation of `ExpFlow.lean`, with its flow map `C^∞` jointly in
time and the initial phase (the continuity statement there is the `C⁰` shadow of this one).
-/

open Bundle Manifold Set Filter Topology Matrix Metric
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The phase flow box of the geodesic equation near a point of phase space.** -/
theorem exists_phase_flow_smooth (hg : Lightlike.IsCoordMetric g U) {p₀ v₀ : Fin n → ℝ} (hp : p₀ ∈ U) :
    ∃ (r T : ℝ) (Φ : ℝ → (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)),
      0 < r ∧ 0 < T ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Φ q.1 q.2)
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
  refine ⟨r, T, Φ, h.r_pos, h.T_pos, hsm, h.flow_zero, fun q hq t ht => ?_⟩
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

/-- **Local flow of the geodesic equation, on the tangent bundle.** -/
theorem exists_local_flow_smooth (z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) :
    ∃ (N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (δ : ℝ)
      (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M),
      IsOpen N ∧ z₀ ∈ N ∧ 0 < δ ∧ (∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-δ) δ) ∧ phase (n := n) (Γ z) 0 = z) ∧
      ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2)
        (N ×ˢ Ioo (-δ) δ) := by
  set x : M := z₀.proj with hx
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set e := Lightlike.chartTriv n x with he
  have hg := g.toNondegMetric.isCoordMetric_coordMetric x
  have hxs : x ∈ ψ.source := mem_extChartAt_source x
  have hxt : ψ x ∈ ψ.target := ψ.map_source hxs
  obtain ⟨r, T, Φ, hr, hT, hΦs, hΦ0, hΦ⟩ :=
    Lightlike.Geodesic.exists_phase_flow_smooth hg hxt (v₀ := (e z₀).2)
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
  -- smoothness
  have hcsm : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) ∞
      c e.source := by
    refine ContMDiffOn.prodMk_space ?_ ?_
    · refine ContMDiffOn.comp (contMDiffOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) (x := x))
        (contMDiffOn_proj (E := TangentSpace 𝓘(ℝ, Fin n → ℝ)) (s := e.source))
        (fun z hz => ?_)
      have := hzsrc z hz
      rwa [extChartAt_source] at this
    · have hid : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
          (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (id : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) e.source :=
        contMDiffOn_id
      have := (Trivialization.contMDiffOn_iff (IM := 𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
        (IB := 𝓘(ℝ, Fin n → ℝ)) (e := e) (f := id) (s := e.source) (n := ∞)
        (mapsTo_id _)).1 hid
      exact this.2
  set IM : ModelWithCorners ℝ _ _ :=
    (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ) with hIM
  set D : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ) := N ×ˢ Ioo (-T) T with hD
  have hargs : ContMDiffOn IM 𝓘(ℝ, ℝ × ((Fin n → ℝ) × (Fin n → ℝ))) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (zs.2, c zs.1)) D := by
    refine ContMDiffOn.prodMk_space ?_ ?_
    · exact (contMDiff_snd (I := 𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) (J := 𝓘(ℝ, ℝ))
        (n := ∞) |>.contMDiffOn)
    · exact ContMDiffOn.comp (hcsm) (contMDiffOn_fst (I := 𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
        (J := 𝓘(ℝ, ℝ)) (s := D)) (fun zs hzs => hzs.1.1)
  have hP : ContMDiffOn IM 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => Φ zs.2 (c zs.1)) D :=
    ContMDiffOn.comp (g := fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Φ q.1 q.2)
      hΦs.contMDiffOn hargs (fun zs hzs => ⟨hzs.2, hzs.1.2⟩)
  have hP1 : ContMDiffOn IM 𝓘(ℝ, Fin n → ℝ) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (Φ zs.2 (c zs.1)).1) D :=
    contDiff_fst.contMDiff.comp_contMDiffOn hP
  have hP2 : ContMDiffOn IM 𝓘(ℝ, Fin n → ℝ) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (Φ zs.2 (c zs.1)).2) D :=
    contDiff_snd.contMDiff.comp_contMDiffOn hP
  have hbase : ContMDiffOn IM 𝓘(ℝ, Fin n → ℝ) ∞
      (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => Γ zs.1 zs.2) D := by
    refine ContMDiffOn.comp (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x) hP1 ?_
    exact fun zs hzs => hΦU zs.1 hzs.1 zs.2 hzs.2
  have hmaps : MapsTo (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ zs.1) zs.2) D e.source := fun zs hzs => by
    rw [e.mem_source, he, chartTriv_baseSet_eq]
    exact hΓsrc zs.1 hzs.1 zs.2 hzs.2
  refine (Trivialization.contMDiffOn_iff (IM := IM) (IB := 𝓘(ℝ, Fin n → ℝ)) (e := e)
    (f := fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2)
    (s := D) (n := ∞) hmaps).2 ⟨hbase, hP2.congr fun zs hzs => ?_⟩
  have := hphase zs.1 hzs.1 zs.2 hzs.2
  exact congrArg Prod.snd this



/-- **The germ of the geodesic flow along `[0, t]` at `z₀`**: a neighbourhood `N` of `z₀` and
geodesic curves `Γ z`, `z ∈ N`, with phase `z` at `0`, defined on `(-ε, t + ε)`, whose phase is jointly
smooth (`C^∞`) in `(z, s)`. -/
def SFlowGerm (z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ) : Prop :=
  ∃ (N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (ε : ℝ) (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M),
    IsOpen N ∧ z₀ ∈ N ∧ 0 < ε ∧
    (∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (t + ε)) ∧ phase (n := n) (Γ z) 0 = z) ∧
    ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ zs.1) zs.2)
      (N ×ˢ Ioo (-ε) (t + ε))

/-- **Extending a flow germ by a local flow box.** -/
theorem sflowGerm_step {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {t : ℝ} (ht : 0 ≤ t)
    {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hNo : IsOpen N) (hz₀ : z₀ ∈ N) (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (t + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    (hcont : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ zs.1) zs.2) (N ×ˢ Ioo (-ε) (t + ε)))
    {N' : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {δ' : ℝ}
    {Γ' : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hN'o : IsOpen N') (hδ' : 0 < δ')
    (hgeo' : ∀ z ∈ N', IsGeodesicCurveOn g (Γ' z) (Ioo (-δ') δ') ∧ phase (n := n) (Γ' z) 0 = z)
    (hcont' : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ' zs.1) zs.2) (N' ×ˢ Ioo (-δ') δ'))
    (hF : phase (n := n) (Γ z₀) t ∈ N') {t₂ : ℝ} (h1 : t ≤ t₂) (h2 : t₂ < t + δ') :
    SFlowGerm g z₀ t₂ := by
  classical
  haveI : Nonempty M := ⟨z₀.proj⟩
  set J₁ : Set ℝ := Ioo (-ε) (t + ε) with hJ₁
  set J₂ : Set ℝ := Ioo (t - δ') (t + δ') with hJ₂
  have htJ₁ : t ∈ J₁ := ⟨by linarith, by linarith⟩
  have htJ₂ : t ∈ J₂ := ⟨by linarith, by linarith⟩
  set F : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → TangentBundle 𝓘(ℝ, Fin n → ℝ) M :=
    fun z => phase (n := n) (Γ z) t with hFdef
  have hFc : ContMDiffOn (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ F N :=
    hcont.comp (contMDiffOn_id.prodMk contMDiffOn_const) (fun z hz => ⟨hz, htJ₁⟩)
  set N₁ := N ∩ F ⁻¹' N' with hN₁
  have hN₁o : IsOpen N₁ := hFc.continuousOn.isOpen_inter_preimage hNo hN'o
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
    have hA1 : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
        phase (n := n) (Γ₂ zs.1) zs.2) (N₁ ×ˢ J₁) := by
      refine (hcont.mono (prod_mono inter_subset_left subset_rfl)).congr fun zs hzs => ?_
      exact hphJ₁ zs.1 hzs.1 zs.2 hzs.2
    have hA2 : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
        phase (n := n) (Γ₂ zs.1) zs.2) (N₁ ×ˢ J₂) := by
      have hmap : MapsTo (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (F zs.1, zs.2 - t))
          (N₁ ×ˢ J₂) (N' ×ˢ Ioo (-δ') δ') := fun zs hzs =>
        ⟨hzs.1.2, ⟨by linarith [hzs.2.1], by linarith [hzs.2.2]⟩⟩
      have hc2 : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => (F zs.1, zs.2 - t))
          (N₁ ×ˢ J₂) :=
        (((hFc.mono inter_subset_left).comp contMDiffOn_fst (fun zs hzs => hzs.1)).prodMk
          ((contDiff_id.sub contDiff_const).contMDiff.comp_contMDiffOn contMDiffOn_snd))
      refine (hcont'.comp hc2 hmap).congr fun zs hzs => ?_
      exact hphJ₂ zs.1 hzs.1 zs.2 hzs.2
    refine contMDiffOn_of_locally_contMDiffOn fun p hp => ?_
    by_cases h1 : p.2 ∈ J₁
    · exact ⟨N₁ ×ˢ J₁, hN₁o.prod isOpen_Ioo, ⟨hp.1, h1⟩, hA1.mono inter_subset_right⟩
    · have h2 : p.2 ∈ J₂ := by
        rcases hsub hp.2 with h | h
        · exact absurd h h1
        · exact h
      exact ⟨N₁ ×ˢ J₂, hN₁o.prod isOpen_Ioo, ⟨hp.1, h2⟩, hA2.mono inter_subset_right⟩

/-- **A flow germ restricts to earlier times.** -/
theorem SFlowGerm.mono {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {t t' : ℝ}
    (h : SFlowGerm g z₀ t) (h0 : 0 ≤ t') (htt : t' ≤ t) : SFlowGerm g z₀ t' := by
  obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcont⟩ := h
  have hsub : Ioo (-ε) (t' + ε) ⊆ Ioo (-ε) (t + ε) := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨N, ε, Γ, hNo, hz₀, hε, fun z hz => ⟨(hgeo z hz).1.mono hsub, (hgeo z hz).2⟩,
    hcont.mono (prod_mono subset_rfl hsub)⟩

/-- **The geodesic flow is smooth along a geodesic**: if `γ₀` is a geodesic curve on an open
interval `I₀ ⊇ [0, Λ]` with phase `z₀` at `0`, then there is a flow germ at `z₀` along `[0, Λ]`: all
geodesics with initial phase `z` near `z₀` exist on `(-ε, Λ + ε)` and their phases depend smoothly on
`(z, s)`. -/
theorem sflowGerm_along {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {γ₀ : ℝ → M} {I₀ : Set ℝ}
    (hI₀ : IsOpen I₀) (hI₀c : I₀.OrdConnected) (hγ₀ : IsGeodesicCurveOn g γ₀ I₀)
    (hph : phase (n := n) γ₀ 0 = z₀) (h0 : 0 ∈ I₀) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hsub : Icc 0 Λ ⊆ I₀) :
    ∀ t ∈ Icc 0 Λ, SFlowGerm g z₀ t := by
  set s : Set ℝ := {t | SFlowGerm g z₀ t} with hs
  -- the local flow box along `γ₀`
  have hbox : ∀ t ∈ Icc 0 Λ, ∃ (N' : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (δ' : ℝ)
      (Γ' : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M), IsOpen N' ∧ phase (n := n) γ₀ t ∈ N' ∧
      0 < δ' ∧ (∀ z ∈ N', IsGeodesicCurveOn g (Γ' z) (Ioo (-δ') δ') ∧ phase (n := n) (Γ' z) 0 = z) ∧
      ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ =>
      phase (n := n) (Γ' zs.1) zs.2)
        (N' ×ˢ Ioo (-δ') δ') := fun t _ => exists_local_flow_smooth g (phase (n := n) γ₀ t)
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
      · exact SFlowGerm.mono g hts.1 ht'I.1 hle
      · have hlt : t < t' := not_le.1 hle
        obtain ⟨N, ε, Γ, hNo, hz₀, hε, hgeo, hcont⟩ := hts.1
        have hF : phase (n := n) (Γ z₀) t ∈ N' := by
          rw [FlowGerm.phase_eq g hI₀ hI₀c hγ₀ hph h0 htI.1 (hsub htI) hz₀ hε hgeo]
          refine hηN ?_
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [htm.1, htm.2, min_le_left η δ']
        exact sflowGerm_step g htI.1 hNo hz₀ hε hgeo hcont hN'o hδ' hgeo' hcont' hF hlt.le
          (by linarith [htm.1, min_le_right η δ'])
    · -- the start
      obtain ⟨N, δ, Γ, hNo, hz₀, hδ, hgeo, hcont⟩ := exists_local_flow_smooth g z₀
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
      exact sflowGerm_step g hx0 hNo hz₀ hε hgeo hcont hN'o hδ' hgeo' hcont' hF ht₂.1.le (by linarith [ht₂.2])
  exact fun t ht => hmain ht


end Lightlike.Penrose
