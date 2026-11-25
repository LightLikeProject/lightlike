import Lightlike.Spacetime.PenroseSingularity.FamilyChart

/-!
# Scalar quantities along a family of flow geodesics (G1-012, step D3b wiring)

For a smooth family `F (σ, t) = Γ (zS σ) t` of geodesics from the flow germ, the scalar functions of `t`
that are computed chartwise (`g(γ', γ')`, `g(γ', ∂_{σ_j} F)`) have zero derivative at every `t`, because the
chart-level lemmas apply in the chart at `γ(t)`; hence they are constant.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

/-- A function with zero derivative on an open interval is constant there. -/
theorem const_of_hasDerivAt_zero {J : Set ℝ} (hJc : Convex ℝ J) (hJ : IsOpen J) {f : ℝ → ℝ}
    (h : ∀ t ∈ J, HasDerivAt f 0 t) {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) : f a = f b := by
  refine hJc.is_const_of_fderivWithin_eq_zero (fun x hx => (h x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) ha hb
  have := (h x hx).hasFDerivAt.hasFDerivWithinAt (s := J)
  have hu : UniqueDiffWithinAt ℝ J x := hJ.uniqueDiffWithinAt hx
  rw [this.fderivWithin hu]
  simp

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The data of a smooth family of flow geodesics `Γ (zS σ)`, `σ ∈ Sg`, on the time interval `J ∋ 0`. -/
structure FlowFamily (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (J : Set ℝ) (Sg : Set (Fin m → ℝ)) : Prop where
  isOpen_J : IsOpen J
  convex_J : Convex ℝ J
  zero_mem : (0 : ℝ) ∈ J
  isOpen_Sg : IsOpen Sg
  geo : ∀ z ∈ Nz, IsGeodesicCurveOn g (Γ z) J
  smooth_flow : ContMDiffOn ((𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)).prod 𝓘(ℝ, ℝ))
    (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
    (fun zs : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ => phase (n := n) (Γ zs.1) zs.2) (Nz ×ˢ J)
  smooth_init : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg
  mem_Nz : ∀ σ ∈ Sg, zS σ ∈ Nz
  phase_zero : ∀ z ∈ Nz, phase (n := n) (Γ z) 0 = z

variable {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- The metric of two tangent vectors at a point of a chart, in coordinates. -/
theorem g_eq_gpair (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ p : M)
    (hsrc : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    g.g p u v = gpairAt (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨p, u⟩).2 (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨p, v⟩).2 := by
  have hb : p ∈ (chartTriv n x₀).baseSet := by
    rw [chartTriv_baseSet_eq]; exact hsrc
  have hdec : ∀ w : TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      w = (chartTriv n x₀).symmL ℝ p ((chartTriv n x₀ ⟨p, w⟩).2) := fun w => by
    rw [Bundle.Trivialization.symmL_apply (chartTriv n x₀) (R := ℝ) hb]
    exact (Bundle.Trivialization.symm_apply_apply_mk (chartTriv n x₀) hb w).symm
  rw [gpairAt_eq_bil]
  conv_lhs => rw [hdec u, hdec v]
  exact metric_eq_bil_at g.toNondegMetric x₀ p hsrc _ _

/-- **Nullness is conserved along the flow family.** -/
theorem FlowFamily.null_of_zero (hF : FlowFamily g Γ zS Nz J Sg)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0) :
    ∀ σ ∈ Sg, ∀ t ∈ J, g.g (phase (n := n) (Γ (zS σ)) t).proj
      (phase (n := n) (Γ (zS σ)) t).snd (phase (n := n) (Γ (zS σ)) t).snd = 0 := by
  intro σ hσ
  set f : ℝ → ℝ := fun t => g.g (phase (n := n) (Γ (zS σ)) t).proj
      (phase (n := n) (Γ (zS σ)) t).snd (phase (n := n) (Γ (zS σ)) t).snd with hf
  have hderiv : ∀ t ∈ J, HasDerivAt f 0 t := by
    intro t ht
    obtain ⟨W, hW0, hWo, hsm', hmem, hgeo', hvel⟩ :=
      exists_chartGeo g (Γ (zS σ) t) hF.isOpen_J hF.isOpen_Sg hF.geo hF.smooth_flow hF.smooth_init
        hF.mem_Nz ht hσ rfl
    set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) with hψ
    set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := fun p => ψ (Γ (zS p.2) p.1) with hH
    have hgc := hgeo' (t, σ) hW0
    have hγ := hgc.pos t hW0
    have hw := hgc.vel t hW0
    have hnc := null_hasDerivAt_zero (g.toNondegMetric.isCoordMetric_coordMetric (Γ (zS σ) t))
      (γ := fun t' => ψ (Γ (zS σ) t')) (w := fun t' => fderiv ℝ H (t', σ) (1, 0)) (t := t)
      hγ hw (hmem _ hW0)
    refine hnc.congr_of_eventuallyEq ?_
    have hcont : Continuous fun t' : ℝ => ((t', σ) : ℝ × (Fin m → ℝ)) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (hWo.mem_nhds hW0)] with t' ht'
    obtain ⟨-, -, hsrc, hv⟩ := hvel _ ht'
    have := g_eq_gpair g (Γ (zS σ) t) _ hsrc (phase (n := n) (Γ (zS σ)) t').snd
      (phase (n := n) (Γ (zS σ)) t').snd
    simp only [hf]
    refine this.trans ?_
    rw [← hv]
    rfl
  intro t ht
  have h0 := const_of_hasDerivAt_zero hF.convex_J hF.isOpen_J hderiv ht hF.zero_mem
  rw [show g.g (phase (n := n) (Γ (zS σ)) t).proj (phase (n := n) (Γ (zS σ)) t).snd
      (phase (n := n) (Γ (zS σ)) t).snd = f t from rfl, h0]
  show g.g (phase (n := n) (Γ (zS σ)) 0).proj (phase (n := n) (Γ (zS σ)) 0).snd
    (phase (n := n) (Γ (zS σ)) 0).snd = 0
  rw [hF.phase_zero _ (hF.mem_Nz σ hσ)]
  exact hk σ hσ

/-- The chart coordinates of a tangent vector are the derivative of the chart. -/
theorem tTriv_snd_eq_mfderiv (x₀ q : M) (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) q) :
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨q, u⟩).2 =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) q u := by
  have hq' : q ∈ (chartAt (Fin n → ℝ) x₀).source := by rwa [extChartAt_source] at hq
  have h1 := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := 𝓘(ℝ, Fin n → ℝ)) hq'
  have h2 := Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀) (R := ℝ) (show q ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀).baseSet from hq') u
  rw [h1] at h2
  exact h2.symm

/-- The coordinates of the derivative of a map into `M` are the derivative of its chart expression. -/
theorem fderiv_coord (x₀ : M) {f : (Fin m → ℝ) → M} {σ : Fin m → ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) f σ)
    (hsrc : f σ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (e : Fin m → ℝ) :
    fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f σ')) σ e =
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨f σ, mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) f σ e⟩).2 := by
  rw [tTriv_snd_eq_mfderiv x₀ _ hsrc]
  have hψ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) (f σ) :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ, Fin n → ℝ)) (n := 1)
      (by rw [extChartAt_source] at hsrc; exact hsrc)).mdifferentiableAt one_ne_zero
  have hcomp := mfderiv_comp σ hψ hf
  have hd : DifferentiableAt ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f σ')) σ := by
    have := (hψ.comp σ hf)
    exact mdifferentiableAt_iff_differentiableAt.1 this
  have h3 : mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f σ')) σ =
      fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (f σ')) σ := mfderiv_eq_fderiv
  rw [← h3]
  exact (congrArg (fun L => L e) hcomp)

/-- The `σ`-slices of the flow family are differentiable maps into `M`. -/
theorem FlowFamily.mdifferentiableAt_slice (hF : FlowFamily g Γ zS Nz J Sg) {σ : Fin m → ℝ}
    (hσ : σ ∈ Sg) {t : ℝ} (ht : t ∈ J) :
    MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ := by
  have hph := contMDiffOn_phaseFamily hF.smooth_flow hF.smooth_init hF.mem_Nz
  have hpr : ContMDiff (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => z.proj) :=
    Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)
  have hmap : ContDiff ℝ ∞ (fun σ' : Fin m → ℝ => ((t, σ') : ℝ × (Fin m → ℝ))) := by fun_prop
  have h1 := (hpr.comp_contMDiffOn hph).comp hmap.contMDiff.contMDiffOn
    (fun σ' hσ' => (⟨ht, hσ'⟩ : ((t, σ') : ℝ × (Fin m → ℝ)) ∈ J ×ˢ Sg))
  exact (h1.contMDiffAt (hF.isOpen_Sg.mem_nhds hσ)).mdifferentiableAt (by simp)

/-- **`g(γ', ∂_{σ_j} F) ≡ 0` along the flow family**, from its vanishing at `t = 0`. -/
theorem FlowFamily.omega_zero (hF : FlowFamily g Γ zS Nz J Sg)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0) :
    ∀ σ ∈ Sg, ∀ j : Fin m, ∀ t ∈ J, g.g (Γ (zS σ) t) (phase (n := n) (Γ (zS σ)) t).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ (Pi.single j 1)) = 0 := by
  intro σ hσ j
  have hnull := hF.null_of_zero hk
  set f : ℝ → ℝ := fun t => g.g (Γ (zS σ) t) (phase (n := n) (Γ (zS σ)) t).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ (Pi.single j 1)) with hf
  have hderiv : ∀ t ∈ J, HasDerivAt f 0 t := by
    intro t ht
    obtain ⟨W, hW0, hCF, hvel⟩ := exists_chartFamily g (Γ (zS σ) t) hF.isOpen_J hF.isOpen_Sg hF.geo
      hF.smooth_flow hF.smooth_init hF.mem_Nz hnull ht hσ rfl
    set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) with hψ
    set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := fun p => ψ (Γ (zS p.2) p.1) with hH
    have hω := omega_hasDerivAt_zero (g.toNondegMetric.isCoordMetric_coordMetric (Γ (zS σ) t))
      hCF.isOpen hCF.smooth hCF.mem hCF.geo hCF.null hW0 j
    refine hω.congr_of_eventuallyEq ?_
    have hcont : Continuous fun t' : ℝ => ((t', σ) : ℝ × (Fin m → ℝ)) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (hCF.isOpen.mem_nhds hW0)] with t' ht'
    obtain ⟨-, htJ, hsrc, hv⟩ := hvel _ ht'
    have hmd := hF.mdifferentiableAt_slice hσ htJ
    have hfd := fderiv_coord (Γ (zS σ) t) hmd hsrc (Pi.single j 1)
    have hdiffH : DifferentiableAt ℝ H (t', σ) :=
      (hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds ht')).differentiableAt (by simp)
    have hpart : fderiv ℝ (fun σ' => ψ (Γ (zS σ') t')) σ (Pi.single j 1) =
        fderiv ℝ H (t', σ) (0, Pi.single j 1) := by
      have hc : HasFDerivAt (fun σ' : Fin m → ℝ => ((t', σ') : ℝ × (Fin m → ℝ)))
          ((0 : (Fin m → ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Fin m → ℝ))) σ :=
        (hasFDerivAt_const t' σ).prodMk (hasFDerivAt_id σ)
      have := hdiffH.hasFDerivAt.comp σ hc
      show fderiv ℝ (H ∘ Prod.mk t') σ (Pi.single j 1) = _
      rw [this.fderiv]
      simp
    have hgp := g_eq_gpair g (Γ (zS σ) t) (Γ (zS σ) t') hsrc (phase (n := n) (Γ (zS σ)) t').snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t') σ (Pi.single j 1))
    simp only [hf]
    refine hgp.trans ?_
    rw [← hpart, hfd]
    show gpairAt _ _ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t)
      (phase (n := n) (Γ (zS σ)) t')).2 _ = _
    rw [hv]
  intro t ht
  have h0 := const_of_hasDerivAt_zero hF.convex_J hF.isOpen_J hderiv ht hF.zero_mem
  show f t = 0
  rw [h0]
  exact hperp σ hσ j

end Lightlike.Penrose
