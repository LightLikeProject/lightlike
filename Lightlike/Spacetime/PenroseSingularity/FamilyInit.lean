import Lightlike.Spacetime.PenroseSingularity.FamilyPoint
import Lightlike.Spacetime.GeodesicIntrinsic

/-!
# Initial data of a flow family (G1-012, step D3b wiring)

For a flow family whose initial phases are `zS σ = (xS σ, k (xS σ))` for a smooth vector field `k`, the
matrices `Qg` and `Cg` at `t = 0` are the first and second fundamental forms of the parametrised surface
`σ ↦ xS σ` with respect to `k`:
`Q_ij = g(∂_i xS, ∂_j xS)` and `C_ij = g(∇_{∂_i xS} k, ∂_j xS)`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

omit [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M]
  [BorelSpace M] in
/-- Chain rule: the derivative of `f ∘ xS` in the direction `e` is `mfderiv f (xS σ) (mfderiv xS σ e)`. -/
theorem fderiv_comp_mfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F}
    {xS : (Fin m → ℝ) → M} {σ : Fin m → ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) f (xS σ))
    (hx : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ) (e : Fin m → ℝ) :
    fderiv ℝ (fun σ' => f (xS σ')) σ e =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) f (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ e) := by
  have hcomp := mfderiv_comp σ hf hx
  have hd : DifferentiableAt ℝ (fun σ' => f (xS σ')) σ :=
    mdifferentiableAt_iff_differentiableAt.1 (hf.comp σ hx)
  have h3 : mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, F) (fun σ' => f (xS σ')) σ =
      fderiv ℝ (fun σ' => f (xS σ')) σ := mfderiv_eq_fderiv
  rw [← h3]
  exact congrArg (fun L => L e) hcomp

variable {gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)} {σ : Fin m → ℝ}

/-- **The mixed second derivative at `t = 0`** of the chart family: `∂_σ ∂_t H (0, σ)` is the derivative of
the components of the field `k` along `xS`. -/
theorem ChartJac.D2_init (hF : FlowFamily gM Γ zS Nz J Sg) (cj : ChartJac gM Γ zS J Sg σ 0)
    {xS : (Fin m → ℝ) → M} {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hz : ∀ σ' ∈ Sg, zS σ' = (⟨xS σ', k (xS σ')⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (hσ : σ ∈ Sg)
    (hk : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS σ))
    (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ)
    (hb : xS σ ∈ (tTriv (E := Fin n → ℝ) (Γ (zS σ) 0)).baseSet) (e : Fin m → ℝ) :
    fderiv ℝ (fderiv ℝ (chartH gM Γ zS (Γ (zS σ) 0))) (0, σ) (1, 0) (0, e) =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) (Γ (zS σ) 0) k) (xS σ)
        (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ e) := by
  classical
  obtain ⟨W, I, P, hIo, htI, hW0, hCF, hIW, hJ, hω, hQeq, hid⟩ := cj
  set x₀ : M := Γ (zS σ) 0 with hx₀
  set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := chartH gM Γ zS x₀ with hH
  have hC : ContDiffAt ℝ 3 H (0, σ) := hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds hW0)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ H) (0, σ) :=
    (hC.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).differentiableAt (by simp)
  have hsym : ∀ u v, fderiv ℝ (fderiv ℝ H) (0, σ) u v = fderiv ℝ (fderiv ℝ H) (0, σ) v u := fun u v =>
    (((hC.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])) u v)
  rw [hsym]
  -- the line in parameter space
  set q : ℝ → ℝ × (Fin m → ℝ) := fun r => (0, σ + r • e) with hq
  have hq0 : q 0 = (0, σ) := by simp [hq]
  have hqd : HasDerivAt q ((0 : ℝ), e) 0 := by
    have : HasDerivAt (fun r : ℝ => σ + r • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add σ
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk this
  have h1 := hasDerivAt_fderiv_comp' (f := H) (q := q) (r := 0) (by rw [hq0]; exact hf2) hqd (1, 0)
  rw [hq0] at h1
  -- the left side agrees with the components of `k` along `xS`
  have hqc : Continuous q := by fun_prop
  have hOpen : IsOpen {p : ℝ × (Fin m → ℝ) | p ∈ W ∧ p.2 ∈ Sg} :=
    hCF.isOpen.inter (hF.isOpen_Sg.preimage continuous_snd)
  have hev : ∀ᶠ r in nhds (0 : ℝ), fderiv ℝ H (q r) (1, 0) = hat (E := Fin n → ℝ) x₀ k (xS (σ + r • e)) := by
    have hmem : q 0 ∈ {p : ℝ × (Fin m → ℝ) | p ∈ W ∧ p.2 ∈ Sg} := by
      rw [hq0]; exact ⟨hW0, hσ⟩
    filter_upwards [hqc.continuousAt.eventually (hOpen.mem_nhds hmem)] with r hr
    obtain ⟨-, -, -, hv⟩ := hid (q r) hr.1
    have hN : zS (q r).2 ∈ Nz := hF.mem_Nz _ hr.2
    have hph := hF.phase_zero _ hN
    rw [← hv, hph, hz _ hr.2]
    rfl
  have h2 : HasDerivAt (fun r : ℝ => hat (E := Fin n → ℝ) x₀ k (xS (σ + r • e)))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) x₀ k) (xS σ)
        (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ e)) 0 := by
    have hhat : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) x₀ k) (xS σ) :=
      (mdiffAt_hat_iff x₀ k hb).1 hk
    have hd : DifferentiableAt ℝ (fun σ' => hat (E := Fin n → ℝ) x₀ k (xS σ')) σ :=
      mdifferentiableAt_iff_differentiableAt.1 (hhat.comp σ hxS)
    have hline : HasDerivAt (fun r : ℝ => σ + r • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add σ
    have h3 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    rw [← fderiv_comp_mfderiv hhat hxS e]
    exact h3
  have h4 := h1.congr_of_eventuallyEq (hev.mono fun r hr => hr.symm)
  exact (h4.unique h2) ▸ rfl

/-- The Christoffel tensor of the Levi-Civita connection in the components of the trivialization is
`gammaApply` of the coordinate metric. -/
theorem gamHat_eq_gammaApply {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (h : cov.IsLeviCivita g.toNondegMetric) (x₀ : M) {z : M}
    (hz : z ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (w u : Fin n → ℝ) :
    gamHat cov x₀ z w u = Lightlike.Geodesic.gammaApply (g.coordMetric x₀)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z) w u := by
  classical
  have hzs : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (by
      rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz)
  have hg : Lightlike.IsCoordMetric (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    g.toNondegMetric.isCoordMetric_coordMetric x₀
  have hw : w = ∑ b, w b • (Pi.single b 1 : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hu : u = ∑ c, u c • (Pi.single c 1 : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ a b c : Fin n, gamHat cov x₀ z (Pi.single b 1) (Pi.single c 1) a =
      Lightlike.christoffel (g.coordMetric x₀) a c b (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z) := by
    intro a b c
    rw [gamHat_coord cov x₀ g.toNondegMetric h hz c b]
    simp [Finset.sum_apply, Pi.single_apply]
  have hexp : gamHat cov x₀ z w u = ∑ b, ∑ c, (w b * u c) • gamHat cov x₀ z (Pi.single b 1) (Pi.single c 1) := by
    have e1 : gamHat cov x₀ z w u = gamHat cov x₀ z (∑ b, w b • (Pi.single b 1 : Fin n → ℝ))
        (∑ c, u c • (Pi.single c 1 : Fin n → ℝ)) :=
      congrArg₂ (fun a b => gamHat cov x₀ z a b) hw hu
    rw [e1]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  ext a
  rw [hexp]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key, Lightlike.Geodesic.gammaApply]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Lightlike.Geodesic.christoffel_symm_of_mem hg hzs a c b]
  ring

/-- **`C` at `t = 0` is the second fundamental form of the parametrised surface** along `k`:
`C_ij = g(∇_{∂_i xS} k, ∂_j xS)`. -/
theorem FlowFamily.Cg_zero_eq {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita gM.toNondegMetric) (hF : FlowFamily gM Γ zS Nz J Sg) (hm : 0 < m)
    (hk0 : ∀ σ ∈ Sg, gM.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, gM.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {xS : (Fin m → ℝ) → M} {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hz : ∀ σ' ∈ Sg, zS σ' = (⟨xS σ', k (xS σ')⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (hσ : σ ∈ Sg)
    (hk : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS σ))
    (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ) (i j : Fin m) :
    Cg gM Γ zS σ 0 i j = gM.g (xS σ)
      (cov k (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1)))
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1)) := by
  classical
  obtain ⟨cj⟩ := hF.exists_chartJac hm hk0 hperp hσ hF.zero_mem
  have hx0 : Γ (zS σ) 0 = xS σ := by
    have h := congrArg Bundle.TotalSpace.proj (hF.phase_zero _ (hF.mem_Nz σ hσ))
    exact (h : Γ (zS σ) 0 = (zS σ).proj).trans (by rw [hz σ hσ])
  have hb : xS σ ∈ (tTriv (E := Fin n → ℝ) (Γ (zS σ) 0)).baseSet := by
    rw [← hx0]; exact mem_baseSet_trivializationAt _ _ _
  have hC := cj.Cg_eq 0 cj.t_mem
  have hD2 := fun e => cj.D2_init hF hz hσ hk hxS hb e
  obtain ⟨W, I, P, hIo, htI, hW0, hCF, hIW, hJ, hω, hQeq, hid⟩ := cj
  set x₀ : M := Γ (zS σ) 0 with hx₀
  set gc := gM.coordMetric x₀ with hgc
  set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := chartH gM Γ zS x₀ with hH
  have hPi : ∀ i, P i 0 = fun a => covDAlong gc (H (0, σ)) (fderiv ℝ H (0, σ) (1, 0))
      (fderiv ℝ H (0, σ) (0, Pi.single i 1)) (fderiv ℝ (fderiv ℝ H) (0, σ) (1, 0) (0, Pi.single i 1)) a :=
    fun i => chart_P_eq hCF (Pi.single i 1) hIW (hJ i) 0 htI
  have hw0 : fderiv ℝ H (0, σ) (1, 0) = hat (E := Fin n → ℝ) x₀ k (xS σ) := by
    obtain ⟨-, -, -, hv⟩ := hid _ hW0
    rw [← hv, hF.phase_zero _ (hF.mem_Nz σ hσ), hz σ hσ]
    rfl
  have hdH : DifferentiableAt ℝ H (0, σ) :=
    (hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds hW0)).differentiableAt (by simp)
  have hψ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) (xS σ) := by
    refine (contMDiffAt_extChartAt' (I := 𝓘(ℝ, Fin n → ℝ)) (n := 1) ?_).mdifferentiableAt one_ne_zero
    rw [extChartAt_source] at *
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hb
  have hJ0 : ∀ e, fderiv ℝ H (0, σ) (0, e) = hv (E := Fin n → ℝ) x₀ (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ e) := by
    intro e
    rw [← fderiv_slice_snd hdH e]
    have hev : (fun σ' => H (0, σ')) =ᶠ[nhds σ] fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ') := by
      filter_upwards [hF.isOpen_Sg.mem_nhds hσ] with σ' hσ'
      show extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS σ') 0) = _
      have h := congrArg Bundle.TotalSpace.proj (hF.phase_zero _ (hF.mem_Nz σ' hσ'))
      have h0 : Γ (zS σ') 0 = xS σ' := (h : Γ (zS σ') 0 = (zS σ').proj).trans (by rw [hz σ' hσ'])
      rw [h0]
    rw [hev.fderiv_eq, fderiv_comp_mfderiv hψ hxS e]
    exact (hv_eq_mfderiv x₀ hb _).symm
  have hHσ : H (0, σ) = extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ) :=
    congrArg (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) hx0
  have hsrc : xS σ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hb
  have hPvec : ∀ i, P i 0 = hv (E := Fin n → ℝ) x₀ (xS σ)
      (cov k (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1))) := by
    intro i
    rw [hPi i, hat_cov cov x₀ hb hk, gamHat_eq_gammaApply gM hLC x₀ hb, hw0, hJ0 (Pi.single i 1),
      hD2 (Pi.single i 1), hHσ]
    funext a
    rfl
  rw [hC]
  simp only [gramC, Matrix.of_apply]
  rw [hPvec i, hJ0 (Pi.single j 1), hHσ, g_eq_gpair gM x₀ (xS σ) hsrc]

/-- `Q` at `t = 0` is the first fundamental form of the parametrised surface. -/
theorem FlowFamily.Qg_zero_eq (hF : FlowFamily gM Γ zS Nz J Sg) {xS : (Fin m → ℝ) → M}
    {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hz : ∀ σ' ∈ Sg, zS σ' = (⟨xS σ', k (xS σ')⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (hσ : σ ∈ Sg) (i j : Fin m) :
    Qg gM Γ zS σ 0 i j = gM.g (xS σ)
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1)) := by
  have hev : (fun σ' => Γ (zS σ') 0) =ᶠ[nhds σ] xS := by
    filter_upwards [hF.isOpen_Sg.mem_nhds hσ] with σ' hσ'
    have h := congrArg Bundle.TotalSpace.proj (hF.phase_zero _ (hF.mem_Nz σ' hσ'))
    exact (h : Γ (zS σ') 0 = (zS σ').proj).trans (by rw [hz σ' hσ'])
  have h0 : Γ (zS σ) 0 = xS σ := hev.self_of_nhds
  simp only [Qg, Matrix.of_apply]
  rw [hev.mfderiv_eq, h0]
  rfl

end Lightlike.Penrose
