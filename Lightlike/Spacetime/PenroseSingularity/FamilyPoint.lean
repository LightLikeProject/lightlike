import Lightlike.Spacetime.PenroseSingularity.FamilyGram

/-!
# Pointwise Riccati data of a flow family (G1-012, step D3b wiring)

At each time `t` the derivatives of the Gram matrix `Qg` of a flow family are those of the chart Gram
matrices of the Jacobi fields of the family in a chart at `Γ (zS σ) t`; the chart identities
(`jacobi_gram_derivs`, `gramP_eq`, `gramC_symm_of_omega`, `trace_gram_rho`) then give the data that
`gram_focusing_local` needs.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- In a chart family, the covariant derivative field `P` of the Jacobi field `∂_e H` is the covariant
derivative of `∂_e H` along `H (·, σ)`. -/
theorem chart_P_eq {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))}
    (hCF : ChartFamily g U H W) {σ : Fin m → ℝ} (e : Fin m → ℝ) {I : Set ℝ}
    (hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W) {P : ℝ → Fin n → ℝ}
    (hP : Lightlike.Geodesic.IsJacobiOn g (fun s => H (s, σ)) (fun s => fderiv ℝ H (s, σ) (1, 0))
      (fun s => fderiv ℝ H (s, σ) (0, e)) P I) :
    ∀ s ∈ I, P s = fun a => covDAlong g (H (s, σ)) (fderiv ℝ H (s, σ) (1, 0))
      (fderiv ℝ H (s, σ) (0, e)) (fderiv ℝ (fderiv ℝ H) (s, σ) (1, 0) (0, e)) a := by
  intro s hs
  have hq := hIW s hs
  have hC : ContDiffAt ℝ 3 H (s, σ) := hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds hq)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ H) (s, σ) :=
    ((hC.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).differentiableAt (by simp))
  have hcurve : HasDerivAt (fun r : ℝ => ((r, σ) : ℝ × (Fin m → ℝ))) ((1 : ℝ), (0 : Fin m → ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s σ)
  have h1 := hasDerivAt_fderiv_comp' hf2 hcurve (0, e)
  have h2 := hP.deriv_field s hs
  have h3 := h1.unique h2
  have h4 : fderiv ℝ (fderiv ℝ H) (s, σ) (1, 0) (0, e) =
      P s - Lightlike.Geodesic.gammaApply g (H (s, σ)) (fderiv ℝ H (s, σ) (1, 0))
        (fderiv ℝ H (s, σ) (0, e)) := h3
  rw [h4, covDAlong_of_deriv]

/-- The matrix `C = g(P_i, J_j)` of a null family with `ω ≡ 0` is symmetric along the interval. -/
theorem chart_C_symm (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hCF : ChartFamily g U H W)
    {σ : Fin m → ℝ} {I : Set ℝ}
    (hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W)
    (hω : ∀ q ∈ W, ∀ j : Fin m,
      gpairAt g (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0)
    {P : Fin m → ℝ → Fin n → ℝ}
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g (fun s => H (s, σ)) (fun s => fderiv ℝ H (s, σ) (1, 0))
      (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) (P i) I) :
    ∀ s ∈ I, (gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s)ᵀ =
      gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s := by
  intro s hs
  ext i j
  have hsym := gramC_symm_of_omega hg hCF.isOpen hCF.smooth hCF.mem hω (hIW s hs) i j
  have hPi := chart_P_eq hCF (Pi.single i 1) hIW (hJ i) s hs
  have hPj := chart_P_eq hCF (Pi.single j 1) hIW (hJ j) s hs
  simp only [Matrix.transpose_apply, gramC, Matrix.of_apply]
  rw [hPi, hPj]
  exact hsym.symm

/-- **Chart-level Riccati data of a null family**: Jacobi fields `∂_{σ_i} H (·, σ)` of a family of null
geodesics with `ω ≡ 0`, on an interval around `t`, satisfy the identities that `gram_focusing_local`
needs, at `t`; moreover `C` is symmetric along the whole interval. -/
theorem chart_point (hg : Lightlike.IsCoordMetric g U) (hnm : n = m + 2)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hCF : ChartFamily g U H W)
    {σ : Fin m → ℝ} {I : Set ℝ} (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W)
    (hω : ∀ q ∈ W, ∀ j : Fin m,
      gpairAt g (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0)
    {P : Fin m → ℝ → Fin n → ℝ}
    (hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn g (fun s => H (s, σ)) (fun s => fderiv ℝ H (s, σ) (1, 0))
      (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) (P i) I)
    (hw0 : ∀ s ∈ I, fderiv ℝ H (s, σ) (1, 0) ≠ 0)
    (hric : ∀ s ∈ I, 0 ≤ ∑ a, ∑ b, Lightlike.ricci g a b (H (s, σ)) *
      fderiv ℝ H (s, σ) (1, 0) a * fderiv ℝ H (s, σ) (1, 0) b)
    (hpd : (gramQ g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) t).PosDef) :
    (∀ s ∈ I, (gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s)ᵀ =
      gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s) ∧
    ∃ ρ : Matrix (Fin m) (Fin m) ℝ,
      (∀ s ∈ I, ∀ i j, HasDerivAt (fun s => gramQ g (fun s => H (s, σ))
        (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) s i j)
        ((gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s +
          (gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s)ᵀ) i j) s) ∧
      (∀ i j, HasDerivAt (fun s => gramC g (fun s => H (s, σ))
        (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s i j)
        ((-ρ + gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P t *
          (gramQ g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) t)⁻¹ *
          (gramC g (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P t)ᵀ) i j) t) ∧
      ρᵀ = ρ ∧ 0 ≤ Matrix.trace ((gramQ g (fun s => H (s, σ))
        (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) t)⁻¹ * ρ) := by
  classical
  set γ : ℝ → Fin n → ℝ := fun s => H (s, σ) with hγ
  set Jf : Fin m → ℝ → Fin n → ℝ := fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1) with hJf
  set w : ℝ → Fin n → ℝ := fun s => fderiv ℝ H (s, σ) (1, 0) with hw
  have hγU : ∀ s ∈ I, γ s ∈ U := fun s hs => hCF.mem _ (hIW s hs)
  have hwJ : ∀ s ∈ I, ∀ i, gpairAt g (γ s) (w s) (Jf i s) = 0 := fun s hs i => hω _ (hIW s hs) i
  have hwP : ∀ s ∈ I, ∀ i, gpairAt g (γ s) (w s) (P i s) = 0 := fun s hs i =>
    gpair_vel_cov_zero hg hI (hJ i) hγU (fun s' hs' => hwJ s' hs' i) s hs
  have hww : ∀ s ∈ I, gpairAt g (γ s) (w s) (w s) = 0 := fun s hs => hCF.null _ (hIW s hs)
  have hCs : ∀ s ∈ I, (gramC g γ Jf P s)ᵀ = gramC g γ Jf P s := chart_C_symm hg hCF hIW hω hJ
  refine ⟨hCs, Matrix.of fun i j => gpairAt g (γ t)
    (Lightlike.Geodesic.riemannApply g (γ t) (w t) (Jf i t)) (Jf j t), ?_, ?_, ?_, ?_⟩
  · intro s hs i j
    exact ((jacobi_gram_derivs hg hJ hγU hs).1 i j)
  · intro i j
    have h := (jacobi_gram_derivs hg hJ hγU ht).2 i j
    have hdet : (gramQ g γ Jf t).det ≠ 0 := hpd.det_pos.ne'
    have hP := gramP_eq hg hnm (hγU t ht) (hww t ht) (hw0 t ht) (hwJ t ht) (hwP t ht) hdet
    have hP' : gramP g γ P t = gramC g γ Jf P t * (gramQ g γ Jf t)⁻¹ * (gramC g γ Jf P t)ᵀ := hP
    rw [hP'] at h
    exact h
  · ext i j
    simp only [gramRho, Matrix.transpose_apply, Matrix.of_apply]
    exact gpair_riemannApply_symm hg (hγU t ht) (w t) (Jf j t) (Jf i t)
  · have := trace_gram_rho hg hnm (hγU t ht) (hww t ht) (hw0 t ht) (hwJ t ht) hpd
    rw [show gramQ g γ Jf t = Matrix.of fun i j => gpairAt g (γ t) (Jf i t) (Jf j t) from rfl, this]
    exact hric t ht

/-- `IsJacobiOn` restricts to a subset of the interval. -/
theorem IsJacobiOn.mono' {γ w J P : ℝ → Fin n → ℝ} {I I' : Set ℝ}
    (h : Lightlike.Geodesic.IsJacobiOn g γ w J P I) (hs : I' ⊆ I) :
    Lightlike.Geodesic.IsJacobiOn g γ w J P I' :=
  ⟨⟨fun t ht => h.geodesic.pos t (hs ht), fun t ht => h.geodesic.vel t (hs ht)⟩,
    fun t ht => h.deriv_field t (hs ht), fun t ht => h.deriv_cov t (hs ht)⟩

/-- A finite family of positive numbers has a common positive lower bound. -/
theorem exists_pos_le_all {m : ℕ} (hm : 0 < m) (f : Fin m → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  rw [hi]; exact hf i

section Global

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- The intrinsic matrix `C = ½ Q'` of a flow family. -/
def Cg (gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (σ : Fin m → ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 / 2 : ℝ) • Matrix.of fun i j => deriv (fun s => Qg gM Γ zS σ s i j) t

/-- The chart expression of a flow family at the base point `x₀`. -/
def chartH (gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) : ℝ × (Fin m → ℝ) → Fin n → ℝ :=
  fun p => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS p.2) p.1)

/-- **Chart Jacobi data of a flow family at `(t, σ)`**: a chart family at `Γ (zS σ) t`, an open interval
`I ∋ t`, Jacobi fields `∂_{σ_i} H (·, σ)` on `I`, `ω ≡ 0`, and the identification of the intrinsic Gram matrix
with the chart Gram matrix. -/
structure ChartJac (gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (J : Set ℝ) (Sg : Set (Fin m → ℝ))
    (σ : Fin m → ℝ) (t : ℝ) where
  /-- The domain of the chart family. -/
  W : Set (ℝ × (Fin m → ℝ))
  /-- The open interval around `t` on which the Jacobi fields are defined. -/
  I : Set ℝ
  /-- The covariant derivatives of the Jacobi fields along the geodesic. -/
  P : Fin m → ℝ → Fin n → ℝ
  isOpen_I : IsOpen I
  t_mem : t ∈ I
  hW0 : ((t, σ) : ℝ × (Fin m → ℝ)) ∈ W
  hCF : ChartFamily (gM.coordMetric (Γ (zS σ) t)) (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).target
    (chartH gM Γ zS (Γ (zS σ) t)) W
  hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W
  hJ : ∀ i, Lightlike.Geodesic.IsJacobiOn (gM.coordMetric (Γ (zS σ) t))
    (fun s => chartH gM Γ zS (Γ (zS σ) t) (s, σ))
    (fun s => fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) (s, σ) (1, 0))
    (fun s => fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) (s, σ) (0, Pi.single i 1)) (P i) I
  hω : ∀ q ∈ W, ∀ j : Fin m, gpairAt (gM.coordMetric (Γ (zS σ) t))
    (chartH gM Γ zS (Γ (zS σ) t) q) (fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) q (1, 0))
    (fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) q (0, Pi.single j 1)) = 0
  hQeq : ∀ s ∈ I, Qg gM Γ zS σ s = gramQ (gM.coordMetric (Γ (zS σ) t))
    (fun s => chartH gM Γ zS (Γ (zS σ) t) (s, σ))
    (fun i s => fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) (s, σ) (0, Pi.single i 1)) s
  hid : ∀ q ∈ W, q.2 ∈ Sg ∧ q.1 ∈ J ∧
    Γ (zS q.2) q.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).source ∧
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t) (phase (n := n) (Γ (zS q.2)) q.1)).2 =
      fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) q (1, 0)

/-- **The chart Jacobi data exist** at every `(t, σ)` of a null flow family. -/
theorem FlowFamily.exists_chartJac (hF : FlowFamily gM Γ zS Nz J Sg) (hm : 0 < m)
    (hk : ∀ σ ∈ Sg, gM.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, gM.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) {t : ℝ} (ht : t ∈ J) : Nonempty (ChartJac gM Γ zS J Sg σ t) := by
  classical
  obtain ⟨W, hW0, hCF, hQeq, hid⟩ := hF.exists_chart_gram hk hσ ht
  set x₀ : M := Γ (zS σ) t with hx₀
  set gc := gM.coordMetric x₀ with hgc
  have hg : Lightlike.IsCoordMetric gc (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    gM.toNondegMetric.isCoordMetric_coordMetric x₀
  set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := chartH gM Γ zS x₀ with hH
  have hjac : ∀ i : Fin m, ∃ δ > 0,
      (∀ s ∈ Ioo (t - δ) (t + δ), ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W) ∧
      ∃ P, Lightlike.Geodesic.IsJacobiOn gc (fun s => H (s, σ)) (fun s => fderiv ℝ H (s, σ) (1, 0))
        (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P (Ioo (t - δ) (t + δ)) :=
    fun i => isJacobiOn_of_chartFamily hg hCF hW0 (Pi.single i 1)
  choose δ hδ hWδ P hP using hjac
  obtain ⟨δ0, hδ0, hle⟩ := exists_pos_le_all hm δ hδ
  have hsub : ∀ i, Ioo (t - δ0) (t + δ0) ⊆ Ioo (t - δ i) (t + δ i) := fun i s hs =>
    ⟨by linarith [hs.1, hle i], by linarith [hs.2, hle i]⟩
  have hIW : ∀ s ∈ Ioo (t - δ0) (t + δ0), ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W :=
    fun s hs => hWδ ⟨0, hm⟩ s (hsub _ hs)
  have hω : ∀ q ∈ W, ∀ j : Fin m,
      gpairAt gc (H q) (fderiv ℝ H q (1, 0)) (fderiv ℝ H q (0, Pi.single j 1)) = 0 := by
    intro q hq j
    obtain ⟨hσq, hqJ, hsrc, hv, hJid⟩ := hid q hq
    have h0 := hF.omega_zero hk hperp q.2 hσq j q.1 hqJ
    have := g_eq_gpair gM x₀ (Γ (zS q.2) q.1) hsrc (phase (n := n) (Γ (zS q.2)) q.1).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') q.1) q.2 (Pi.single j 1))
    have hv' : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS q.2)) q.1)).2 =
        fderiv ℝ H q (1, 0) := hv
    have hJid' : fderiv ℝ H q (0, Pi.single j 1) =
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ ⟨Γ (zS q.2) q.1,
          mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') q.1) q.2 (Pi.single j 1)⟩).2 :=
      hJid (Pi.single j 1)
    rw [← hv', hJid']
    exact this.symm.trans h0
  exact ⟨⟨W, Ioo (t - δ0) (t + δ0), P, isOpen_Ioo, ⟨by linarith, by linarith⟩, hW0, hCF, hIW,
    fun i => IsJacobiOn.mono' (hP i) (hsub i), hω, fun s hs => hQeq s (hIW s hs),
    fun q hq => by
      obtain ⟨hσq, hqJ, hsrc, hv, -⟩ := hid q hq
      exact ⟨hσq, hqJ, hsrc, hv⟩⟩⟩

/-- On the interval of the chart Jacobi data, the intrinsic `C = ½ Q'` is the chart matrix `g(P_i, J_j)`. -/
theorem ChartJac.Cg_eq {σ : Fin m → ℝ} {t : ℝ} (cj : ChartJac gM Γ zS J Sg σ t) :
    ∀ s ∈ cj.I, Cg gM Γ zS σ s = gramC (gM.coordMetric (Γ (zS σ) t))
      (fun s => chartH gM Γ zS (Γ (zS σ) t) (s, σ))
      (fun i s => fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) (s, σ) (0, Pi.single i 1)) cj.P s := by
  classical
  have hg : Lightlike.IsCoordMetric (gM.coordMetric (Γ (zS σ) t))
      (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).target :=
    gM.toNondegMetric.isCoordMetric_coordMetric _
  have hγU : ∀ s ∈ cj.I, chartH gM Γ zS (Γ (zS σ) t) (s, σ) ∈
      (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).target := fun s hs => cj.hCF.mem _ (cj.hIW s hs)
  have hCs := chart_C_symm hg cj.hCF cj.hIW cj.hω cj.hJ
  intro s hs
  have hQev : ∀ i j, (fun s' => Qg gM Γ zS σ s' i j) =ᶠ[nhds s]
      (fun s' => gramQ (gM.coordMetric (Γ (zS σ) t)) (fun s => chartH gM Γ zS (Γ (zS σ) t) (s, σ))
        (fun i s => fderiv ℝ (chartH gM Γ zS (Γ (zS σ) t)) (s, σ) (0, Pi.single i 1)) s' i j) :=
    fun i j => Filter.eventually_of_mem (cj.isOpen_I.mem_nhds hs) fun s' hs' => by
      show Qg gM Γ zS σ s' i j = _
      rw [cj.hQeq s' hs']
  ext i j
  have hd : deriv (fun s' => Qg gM Γ zS σ s' i j) s = _ :=
    (((jacobi_gram_derivs hg cj.hJ hγU hs).1 i j).congr_of_eventuallyEq (hQev i j)).deriv
  have hs' := hCs s hs
  simp only [Cg, Matrix.smul_apply, Matrix.of_apply, hd, Matrix.add_apply]
  rw [hs']
  simp only [smul_eq_mul]
  ring

/-- **Pointwise Riccati data of a flow family**: at a time `t` where `Q` is positive definite, the
identities that `gram_focusing_local` needs hold for `Qg` and `Cg`. -/
theorem FlowFamily.focusing_point (hF : FlowFamily gM Γ zS Nz J Sg) (hm : 0 < m) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, gM.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, gM.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    (hw0 : ∀ σ ∈ Sg, ∀ t ∈ J, (phase (n := n) (Γ (zS σ)) t).snd ≠ 0)
    (hric : ∀ σ ∈ Sg, ∀ t ∈ J, ∀ x₀ : M, Γ (zS σ) t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source →
      0 ≤ ∑ a, ∑ b, Lightlike.ricci (gM.coordMetric x₀) a b (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS σ) t)) *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 a *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 b)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) {t : ℝ} (ht : t ∈ J) (hpd : (Qg gM Γ zS σ t).PosDef) :
    ∃ ρ : Matrix (Fin m) (Fin m) ℝ,
      (∀ i j, HasDerivAt (fun s => Qg gM Γ zS σ s i j)
        ((Cg gM Γ zS σ t + (Cg gM Γ zS σ t)ᵀ) i j) t) ∧
      (∀ i j, HasDerivAt (fun s => Cg gM Γ zS σ s i j)
        ((-ρ + Cg gM Γ zS σ t * (Qg gM Γ zS σ t)⁻¹ * (Cg gM Γ zS σ t)ᵀ) i j) t) ∧
      (Cg gM Γ zS σ t)ᵀ = Cg gM Γ zS σ t ∧ ρᵀ = ρ ∧ 0 ≤ Matrix.trace ((Qg gM Γ zS σ t)⁻¹ * ρ) := by
  classical
  obtain ⟨cj⟩ := hF.exists_chartJac hm hk hperp hσ ht
  obtain ⟨W, I, P, hIo, htI, hW0, hCF, hIW, hJ, hω, hQeqI, hid⟩ := cj
  set x₀ : M := Γ (zS σ) t with hx₀
  set gc := gM.coordMetric x₀ with hgc
  have hg : Lightlike.IsCoordMetric gc (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    gM.toNondegMetric.isCoordMetric_coordMetric x₀
  set H : ℝ × (Fin m → ℝ) → Fin n → ℝ := chartH gM Γ zS x₀ with hH
  have hw0' : ∀ s ∈ I, fderiv ℝ H (s, σ) (1, 0) ≠ 0 := by
    intro s hs hz
    obtain ⟨-, hsJ, hsrc, hv⟩ := hid _ (hIW s hs)
    set z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M := phase (n := n) (Γ (zS σ)) s with hz'
    have hb : z.proj ∈ (chartTriv n x₀).baseSet := by
      rw [chartTriv_baseSet_eq]; exact hsrc
    have hzero : (chartTriv n x₀ z).2 = 0 := by rw [← hz]; exact hv
    apply hw0 σ hσ s hsJ
    have hdec : z.snd = (chartTriv n x₀).symmL ℝ z.proj ((chartTriv n x₀ z).2) := by
      rw [Bundle.Trivialization.symmL_apply (chartTriv n x₀) (R := ℝ) hb]
      exact (Bundle.Trivialization.symm_apply_apply_mk (chartTriv n x₀) hb z.snd).symm
    rw [hdec, hzero, map_zero]
  have hric' : ∀ s ∈ I, 0 ≤ ∑ a, ∑ b, Lightlike.ricci gc a b (H (s, σ)) *
      fderiv ℝ H (s, σ) (1, 0) a * fderiv ℝ H (s, σ) (1, 0) b := by
    intro s hs
    obtain ⟨-, hsJ, hsrc, hv⟩ := hid _ (hIW s hs)
    rw [← hv]
    exact hric σ hσ s hsJ x₀ hsrc
  have hpd' : (gramQ gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) t).PosDef := by
    rw [← hQeqI t htI]; exact hpd
  obtain ⟨hCs, ρ, hQd, hCd, hρs, hρt⟩ :=
    chart_point hg hnm hCF hIo htI hIW hω hJ hw0' hric' hpd'
  have hQev : ∀ s ∈ I, ∀ i j, (fun s' => Qg gM Γ zS σ s' i j) =ᶠ[nhds s]
      (fun s' => gramQ gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) s' i j) :=
    fun s hs i j => Filter.eventually_of_mem (hIo.mem_nhds hs) fun s' hs' => by
      show Qg gM Γ zS σ s' i j = _
      rw [hQeqI s' hs']
  have hdQ : ∀ s ∈ I, ∀ i j, deriv (fun s' => Qg gM Γ zS σ s' i j) s =
      (gramC gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s +
        (gramC gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s)ᵀ) i j :=
    fun s hs i j => ((hQd s hs i j).congr_of_eventuallyEq (hQev s hs i j)).deriv
  have hCgI : ∀ s ∈ I, Cg gM Γ zS σ s =
      gramC gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s := by
    intro s hs
    ext i j
    have hs' := hCs s hs
    simp only [Cg, Matrix.smul_apply, Matrix.of_apply, hdQ s hs i j, Matrix.add_apply]
    rw [hs']
    simp only [smul_eq_mul]
    ring
  have hCev : ∀ i j, (fun s' => Cg gM Γ zS σ s' i j) =ᶠ[nhds t]
      (fun s' => gramC gc (fun s => H (s, σ)) (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P s' i j) :=
    fun i j => Filter.eventually_of_mem (hIo.mem_nhds htI) fun s' hs' => by
      show Cg gM Γ zS σ s' i j = _
      rw [hCgI s' hs']
  refine ⟨ρ, fun i j => ?_, fun i j => ?_, ?_, hρs, ?_⟩
  · rw [hCgI t htI]
    exact (hQd t htI i j).congr_of_eventuallyEq (hQev t htI i j)
  · rw [hCgI t htI, hQeqI t htI]
    exact (hCd i j).congr_of_eventuallyEq (hCev i j)
  · rw [hCgI t htI]; exact hCs t htI
  · rw [hQeqI t htI]; exact hρt

/-- **Focusing along a flow family**: if the Gram matrix of the `σ`-derivatives stays positive definite on
`[0, T)` and the initial expansion `θ(0) = tr (Q⁻¹ Cᵀ)(0)` is negative, then `T ≤ m / |θ(0)|`. -/
theorem FlowFamily.focusing (hF : FlowFamily gM Γ zS Nz J Sg) (hm : 0 < m) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, gM.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, gM.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    (hw0 : ∀ σ ∈ Sg, ∀ t ∈ J, (phase (n := n) (Γ (zS σ)) t).snd ≠ 0)
    (hric : ∀ σ ∈ Sg, ∀ t ∈ J, ∀ x₀ : M, Γ (zS σ) t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source →
      0 ≤ ∑ a, ∑ b, Lightlike.ricci (gM.coordMetric x₀) a b (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS σ) t)) *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 a *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 b)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) {T : ℝ} (hT : Ico 0 T ⊆ J)
    (hpd : ∀ t ∈ Ico 0 T, (Qg gM Γ zS σ t).PosDef)
    (h0 : Matrix.trace ((Qg gM Γ zS σ 0)⁻¹ * (Cg gM Γ zS σ 0)ᵀ) < 0) :
    T ≤ m / |Matrix.trace ((Qg gM Γ zS σ 0)⁻¹ * (Cg gM Γ zS σ 0)ᵀ)| :=
  gram_focusing_local hm (fun t ht => by
    obtain ⟨ρ, a, b, c, d, e⟩ := hF.focusing_point hm hnm hk hperp hw0 hric hσ (hT ht) (hpd t ht)
    exact ⟨ρ, a, b, hpd t ht, c, d, e⟩) h0

/-- **A flow family from a flow germ**: a smooth family `zS` of initial phases through `z₀` gives a
`FlowFamily` on `(-ε, L + ε)` from the flow germ at `z₀` along `[0, L]`. -/
theorem exists_flowFamily_of_sflow {z₀ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {L : ℝ} (hL : 0 ≤ L)
    (hz : SFlowGerm gM z₀ L) {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M}
    {Sg₀ : Set (Fin m → ℝ)} (hSg₀ : IsOpen Sg₀)
    (hzS : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg₀)
    {σ₀ : Fin m → ℝ} (hσ₀ : σ₀ ∈ Sg₀) (hz0 : zS σ₀ = z₀) :
    ∃ (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M) (Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
      (J : Set ℝ) (Sg : Set (Fin m → ℝ)), FlowFamily gM Γ zS Nz J Sg ∧ σ₀ ∈ Sg ∧ Icc 0 L ⊆ J ∧
      Sg ⊆ Sg₀ := by
  obtain ⟨N, ε, Γ, hNo, hz₀N, hε, hgeo, hsm⟩ := hz
  have hcont : ContinuousOn zS Sg₀ := hzS.continuousOn
  have hSgo : IsOpen (Sg₀ ∩ zS ⁻¹' N) := hcont.isOpen_inter_preimage hSg₀ hNo
  refine ⟨Γ, N, Ioo (-ε) (L + ε), Sg₀ ∩ zS ⁻¹' N, ?_, ⟨hσ₀, by rw [mem_preimage, hz0]; exact hz₀N⟩,
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩, inter_subset_left⟩
  exact ⟨isOpen_Ioo, convex_Ioo _ _, ⟨by linarith, by linarith⟩, hSgo, fun z hz => (hgeo z hz).1, hsm,
    hzS.mono inter_subset_left, fun σ hσ => hσ.2, fun z hz => (hgeo z hz).2⟩

end Global

end Lightlike.Penrose
