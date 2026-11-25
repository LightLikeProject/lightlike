import Lightlike.Spacetime.PenroseSingularity.NormalFamily
import Lightlike.Spacetime.PenroseSingularity.FocalChron
import Lightlike.Spacetime.PenroseSingularity.FamilyTheta
import Lightlike.Spacetime.PenroseSingularity.GeodesicNonzero
import Lightlike.Spacetime.PenroseSingularity.TrappedSpacelike

/-!
# The affine length of a generator (G1-012, step D3b wiring)

Along a future null geodesic `γ` from a point `x` of a closed trapped spacelike surface with initial velocity
`μ • k x` for a smooth future null normal field `k`, if the endpoint `γ L` is not in `I⁺(S)`, then
`L ≤ (n - 2) / |θ|` for the expansion `θ` of `μ • k` over an orthonormal frame of `T_x S`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The derivative of the parametrisation of a level set lies in the kernel of `df`. -/
theorem mfderiv_mem_ker {m : ℕ} {f : M → Fin 2 → ℝ} {xS : (Fin m → ℝ) → M} {σ : Fin m → ℝ}
    (hfd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ))
    (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ)
    (hfx : ∀ᶠ σ' in nhds σ, f (xS σ') = 0) (e : Fin m → ℝ) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ)
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ e) = 0 := by
  have hc := fderiv_comp_mfderiv hfd hxS e
  have hev : (fun σ' => f (xS σ')) =ᶠ[nhds σ] fun _ => (0 : Fin 2 → ℝ) := hfx
  rw [hev.fderiv_eq] at hc
  have h0 : fderiv ℝ (fun _ : Fin m → ℝ => (0 : Fin 2 → ℝ)) σ e = 0 := by simp
  exact hc.symm.trans h0

/-- **The affine length of a generator is bounded by the inverse expansion.** -/
theorem generator_focal_bound (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g) {S : Set M} (hn : 3 ≤ n)
    {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (hS : S = f ⁻¹' {0})
    (hsurj : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hspace : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    (hexp : ∀ k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) →
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) →
      ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
        (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) → frameExpansion g cov k x e < 0)
    {k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hkN : ∀ x ∈ S, IsFutureNullNormalAt g T f x (k x))
    (hChron : FocalImpliesChron g T S) (hNEC : ChartNEC g)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L) (hγ : IsFutureNullGeodesicOn T γ (Icc 0 L)) (hx : γ 0 ∈ S)
    (hfar : γ L ∉ Causal.chronFutureSet T S) {μ : ℝ} (hμ : 0 < μ)
    (hv : (phase (n := n) γ 0).snd = μ • k (γ 0)) :
    ∃ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ 0),
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (γ 0) (e i) = 0) ∧
      (∀ i j, g.g (γ 0) (e i) (e j) = if i = j then 1 else 0) ∧
      frameExpansion g cov (fun y => μ • k y) (γ 0) e < 0 ∧
      L ≤ ((n - 2 : ℕ) : ℝ) / |frameExpansion g cov (fun y => μ • k y) (γ 0) e| := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hmpos : 0 < n - 2 := by omega
  have hfγ0 : f (γ 0) = 0 := by rw [hS] at hx; exact hx
  obtain ⟨xS, Γ, zS, Nz, J, Sg, hF, h0, hJ, hΓ, hzdef, hfx, hxSm, hx0, hinj, hker⟩ :=
    exists_normal_family g hn2 hf hk hL.le hγ.1 hfγ0 (hsurj _ hx) hv
  set k' : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p := fun y => μ • k y with hk'
  have hkμ : ∀ q : M, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k' q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := fun q =>
    ContMDiffAt.smul_section contMDiffAt_const hk.contMDiffAt
  have hk'sm : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k' q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := fun q => hkμ q
  have hxSS : ∀ σ ∈ Sg, xS σ ∈ S := fun σ hσ => by rw [hS]; exact hfx σ hσ
  have hk'N : ∀ x ∈ S, IsFutureNullNormalAt g T f x (k' x) := by
    intro x hx'
    obtain ⟨h1, h2, h3, h4⟩ := hkN x hx'
    refine ⟨smul_ne_zero hμ.ne' h1, ?_, ?_, ?_⟩
    · simp [hk', h2]
    · intro v hv0; simp [hk', h3 v hv0]
    · simp only [hk', map_smul, ContinuousLinearMap.smul_apply]
      exact mul_neg_of_pos_of_neg hμ h4
  have hk0 : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0 := fun σ hσ => by
    rw [hzdef σ hσ]; exact (hk'N _ (hxSS σ hσ)).2.1
  have hfut : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (T.X (zS σ).proj) < 0 := fun σ hσ => by
    rw [hzdef σ hσ]; exact (hk'N _ (hxSS σ hσ)).2.2.2
  have hxSd : ∀ σ ∈ Sg, MDifferentiableAt 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ := fun σ hσ =>
    (hxSm.contMDiffAt (hF.isOpen_Sg.mem_nhds hσ)).mdifferentiableAt (by simp)
  have hfd : ∀ σ ∈ Sg, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) := fun σ _ =>
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hfxe : ∀ σ ∈ Sg, ∀ᶠ σ' in nhds σ, f (xS σ') = 0 := fun σ hσ =>
    Filter.eventually_of_mem (hF.isOpen_Sg.mem_nhds hσ) fun σ' h => hfx σ' h
  have hph : ∀ σ ∈ Sg, phase (n := n) (Γ (zS σ)) 0 = zS σ := fun σ hσ => hF.phase_zero _ (hF.mem_Nz σ hσ)
  have hΓ0 : ∀ σ ∈ Sg, Γ (zS σ) 0 = xS σ := fun σ hσ => by
    have h := congrArg Bundle.TotalSpace.proj (hph σ hσ)
    exact (h : Γ (zS σ) 0 = (zS σ).proj).trans (by rw [hzdef σ hσ])
  have hperp : ∀ σ ∈ Sg, ∀ j : Fin (n - 2), g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0 := by
    intro σ hσ j
    have hev : (fun σ' => Γ (zS σ') 0) =ᶠ[nhds σ] xS :=
      Filter.eventually_of_mem (hF.isOpen_Sg.mem_nhds hσ) fun σ' h => hΓ0 σ' h
    have hB : mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1) =
        (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1) : Fin n → ℝ) := by
      rw [hev.mfderiv_eq]; rfl
    have hA : (phase (n := n) (Γ (zS σ)) 0).snd = (μ • k (xS σ) : Fin n → ℝ) := by
      rw [hph σ hσ, hzdef σ hσ]
    have hker0 := mfderiv_mem_ker (hfd σ hσ) (hxSd σ hσ) (hfxe σ hσ) (Pi.single j 1)
    have hgeq : g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
        (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) =
        g.g (xS σ) (μ • k (xS σ) : Fin n → ℝ)
          (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1) : Fin n → ℝ) := by
      rw [hB, hA]
      exact congrArg (fun y => g.g y (μ • k (xS σ) : Fin n → ℝ)
        (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single j 1) : Fin n → ℝ)) (hΓ0 σ hσ)
    rw [hgeq]
    exact (hk'N _ (hxSS σ hσ)).2.2.1 _ hker0
  have hw0 : ∀ σ ∈ Sg, ∀ t ∈ J, (phase (n := n) (Γ (zS σ)) t).snd ≠ 0 := by
    intro σ hσ t ht
    refine phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ))
      hF.zero_mem ht ?_
    rw [hph σ hσ, hzdef σ hσ]
    exact (hk'N _ (hxSS σ hσ)).1
  have hric : ∀ σ ∈ Sg, ∀ t ∈ J, ∀ x₀ : M, Γ (zS σ) t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source →
      0 ≤ ∑ a, ∑ b, Lightlike.ricci (g.coordMetric x₀) a b (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (Γ (zS σ) t)) *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 a *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ (phase (n := n) (Γ (zS σ)) t)).2 b :=
    fun σ hσ t ht x₀ hsrc => hNEC x₀ (phase (n := n) (Γ (zS σ)) t) hsrc (hF.null_of_zero hk0 σ hσ t ht)
  have hk'md : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k' q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS 0) :=
    (hkμ (xS 0)).mdifferentiableAt (by simp)
  obtain ⟨hpd0, e, heK, hortho, htr, hneg⟩ := hF.theta0_neg hLC hmpos hk0 hperp (xS := xS) (k := k')
    hzdef h0 hk'md (hxSd 0 h0) hinj f (hfd 0 h0) (hfxe 0 h0) (hspace (xS 0) (hxSS 0 h0))
    (hexp k' hk'sm hk'N (xS 0) (hxSS 0 h0)) rfl
  have hSproj : ∀ σ ∈ Sg, (zS σ).proj ∈ S := fun σ hσ => by rw [hzdef σ hσ]; exact hxSS σ hσ
  have hT : Ico 0 L ⊆ J := fun t ht => hJ ⟨ht.1, ht.2.le⟩
  have hpdt : ∀ t ∈ Ico 0 L, (Qg g Γ zS 0 t).PosDef := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0]; exact hpd0
    · by_contra hnot
      have hlt : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hch := hChron Γ zS Nz J Sg hF hSproj (fun σ hσ => ⟨hk0 σ hσ, hfut σ hσ⟩) hperp 0 h0 hpd0
        hlt ht.2 (hJ ⟨hL.le, le_rfl⟩) hnot
      rw [hΓ L ⟨hL.le, le_rfl⟩] at hch
      exact hfar hch
  have hbound := hF.focusing hmpos (by omega) hk0 hperp hw0 hric h0 hT hpdt (by rw [htr]; exact hneg)
  rw [← hx0]
  exact ⟨e, heK, hortho, hneg, by rw [htr] at hbound; exact hbound⟩

end Lightlike.Penrose
