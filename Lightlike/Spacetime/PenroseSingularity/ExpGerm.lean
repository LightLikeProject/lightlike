import Lightlike.Spacetime.PenroseSingularity.FlowSmooth
import Lightlike.Spacetime.PenroseSingularity.ExpMap

/-!
# The exponential germ at a zero vector (G1-012, step D4)

The flow germ of the geodesic flow along the constant geodesic at `p₀` gives a smooth map
`Ξ z = Γ z 1` on a neighbourhood of the zero vector at `p₀`, with `Ξ ⟨p, λ v⟩ = Γ ⟨p, v⟩ λ`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The phase of a constant curve is the zero vector. -/
theorem phase_const (p : M) (t : ℝ) : phase (n := n) (fun _ : ℝ => p) t = ⟨p, 0⟩ := by
  unfold phase
  congr 1
  have : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun _ : ℝ => p) t = 0 := mfderiv_const
  rw [this]; rfl

/-- **The flow germ at a zero vector, up to time `1`.** -/
theorem expGerm_exists (p₀ : M) : SFlowGerm g (⟨p₀, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) 1 := by
  have h := sflowGerm_along (g := g) (z₀ := (⟨p₀, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (γ₀ := fun _ : ℝ => p₀) (I₀ := Ioo (-1) 2) isOpen_Ioo ordConnected_Ioo
    (isGeodesicCurveOn_const g p₀ _) (phase_const p₀ 0) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) 1 ⟨by norm_num, le_rfl⟩
  exact h

/-- **Homogeneity of the flow germ**: `Γ ⟨p, λ v⟩ 1 = Γ ⟨p, v⟩ λ` for `0 < λ ≤ 1`. -/
theorem flow_smul {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (1 + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    {p : M} {v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ N)
    (hz' : (⟨p, c • v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ N) :
    Γ ⟨p, c • v⟩ 1 = Γ ⟨p, v⟩ c := by
  obtain ⟨hγ, hph⟩ := hgeo _ hz
  obtain ⟨hγ', hph'⟩ := hgeo _ hz'
  have h0 : Γ ⟨p, v⟩ 0 = p := congrArg Bundle.TotalSpace.proj hph
  have h0' : Γ ⟨p, c • v⟩ 0 = p := congrArg Bundle.TotalSpace.proj hph'
  have hnb : IsOpen (Ioo (-ε) (1 + ε)) := isOpen_Ioo
  have hmem : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hd := deriv_chart_eq_phase g hnb hγ hmem
  have hd' := deriv_chart_eq_phase g hnb hγ' hmem
  rw [hph, h0] at hd
  rw [hph', h0'] at hd'
  have hb : p ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p).baseSet := mem_baseSet_trivializationAt _ _ _
  have hlin : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p ⟨p, c • v⟩).2 =
      c • (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p ⟨p, v⟩).2 :=
    ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p).linear ℝ hb).map_smul c v
  have e1 := expMap_smul_of g (a := -ε) (b := 1 + ε) (γ := Γ ⟨p, v⟩) (by linarith) (by linarith) hγ hc0 hc1
  have e2 := expMap_eq_of g (q := (p, (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p ⟨p, c • v⟩).2))
    (a := -ε) (b := 1 + ε) (γ := Γ ⟨p, c • v⟩) (by linarith) (by linarith) hγ' h0' (by simpa using hd')
  rw [h0] at e1
  rw [hd] at e1
  rw [← hlin] at e1
  exact e2.symm.trans (by rw [← e1])

/-- The zero vector gives the constant geodesic: `Γ ⟨p, 0⟩ 1 = p`. -/
theorem flow_zero {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (1 + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    {p : M} (hz : (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) ∈ N) : Γ ⟨p, 0⟩ 1 = p := by
  obtain ⟨hγ, hph⟩ := hgeo _ hz
  have hmem : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  have hc := isGeodesicCurveOn_const g p (Ioo (-ε) (1 + ε))
  have := eqOn_of_phase_eq' g isOpen_Ioo isPreconnected_Ioo hγ hc hmem
    (by rw [hph, phase_const])
  have h1 : (1 : ℝ) ∈ Ioo (-ε) (1 + ε) := ⟨by linarith, by linarith⟩
  exact this h1

/-- The smooth parametrisation of the tangent bundle over the chart at `p₀`: `(q, w) ↦ ⟨ψ⁻¹ q, e⁻¹ w⟩`. -/
def zetaMap (p₀ : M) (x : (Fin n → ℝ) × (Fin n → ℝ)) : TangentBundle 𝓘(ℝ, Fin n → ℝ) M :=
  (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).toOpenPartialHomeomorph.symm
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1, x.2)

/-- `zetaMap` in terms of the inverse trivialization map `symmL`. -/
theorem zetaMap_eq (p₀ : M) (x : (Fin n → ℝ) × (Fin n → ℝ))
    (hb : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet) :
    zetaMap p₀ x = (⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1,
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1) x.2⟩ :
        TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := by
  unfold zetaMap
  rw [Bundle.Trivialization.symmL_apply _ hb]
  exact (Bundle.Trivialization.mk_symm _ hb _).symm

/-- `zetaMap` is homogeneous in the vector. -/
theorem zetaMap_smul (p₀ : M) (q w : Fin n → ℝ) (c : ℝ)
    (hb : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm q ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet) :
    zetaMap p₀ (q, c • w) = (⟨(zetaMap p₀ (q, w)).proj, c • (zetaMap p₀ (q, w)).snd⟩ :
      TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := by
  rw [zetaMap_eq p₀ (q, c • w) hb, zetaMap_eq p₀ (q, w) hb]
  show (⟨_, _⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) = ⟨_, c • _⟩
  rw [map_smul]

/-- The components of `zetaMap` in the trivialization at `p₀` are the vector. -/
theorem tTriv_zetaMap (p₀ : M) (q w : Fin n → ℝ)
    (hb : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm q ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet) :
    (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ (zetaMap p₀ (q, w))).2 = w := by
  rw [zetaMap_eq p₀ (q, w) hb, Bundle.Trivialization.symmL_apply _ hb]
  exact congrArg Prod.snd ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).apply_mk_symm hb w)

/-- `zetaMap` is smooth on the chart target times the vector space. -/
theorem contMDiffOn_zetaMap (p₀ : M) :
    ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ (zetaMap p₀)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target ×ˢ univ) := by
  have h1 : ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
      (fun x : (Fin n → ℝ) × (Fin n → ℝ) => (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target ×ˢ univ) := by
    have hfst : ContMDiff 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun x : (Fin n → ℝ) × (Fin n → ℝ) => x.1) := contDiff_fst.contMDiff
    exact (contMDiffOn_extChartAt_symm p₀).comp hfst.contMDiffOn (fun x hx => hx.1)
  have h2 : ContMDiffOn 𝓘(ℝ, (Fin n → ℝ) × (Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1, x.2))
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target ×ˢ univ) :=
    h1.prodMk (contDiff_snd.contMDiff.contMDiffOn)
  have h3 := (Bundle.Trivialization.contMDiffOn_symm (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀)
    (IB := 𝓘(ℝ, Fin n → ℝ)) (n := ∞)).comp h2 ?_
  · exact h3
  · intro x hx
    have hxs : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := by
      have hs : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).symm x.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source :=
        (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_target hx.1
      rw [extChartAt_source] at hs
      simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet] using hs
    exact ⟨hxs, mem_univ _⟩

end Lightlike.Penrose
