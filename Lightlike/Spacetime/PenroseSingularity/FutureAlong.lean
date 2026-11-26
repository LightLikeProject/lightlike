import Lightlike.Spacetime.PenroseSingularity.FutureChart
import Lightlike.Spacetime.PenroseSingularity.NullParallel
import Lightlike.Spacetime.PenroseSingularity.FocalVector
import Lightlike.Spacetime.PenroseSingularity.FamilyChart

/-!
# A future null geodesic stays future directed (G1-012, step D4)

The pairing `z ↦ g(z, X(proj z))` of a tangent vector with the time-orientation field is continuous on the tangent
bundle, and does not vanish on null non-zero vectors; hence along a null geodesic that is future directed at one
time it is future directed at all times.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : Causal.TimeOrientation g)

/-- **The pairing with the time-orientation field is continuous on the tangent bundle.** -/
theorem continuous_pairX : Continuous (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M =>
    g.g z.proj z.snd (T.X z.proj)) := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  set p₀ := z₀.proj with hp₀
  have hs : p₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source := mem_extChartAt_source p₀
  have hsrc : ∀ᶠ z in 𝓝 z₀, z.proj ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source :=
    (FiberBundle.continuous_proj (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p₀).mem_nhds hs)
  have hb : p₀ ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet := by
    simp [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source]
  have hz0 : z₀ ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).source := by
    rw [(Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).mem_source]; exact hb
  have hch : ContinuousAt (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M =>
      gpairAt (g.coordMetric p₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ z.proj)
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ z).2 (orientChart T p₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ z.proj))) z₀ := by
    have hcz : ContinuousAt (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ z.proj) z₀ :=
      (continuousAt_extChartAt' (I := 𝓘(ℝ, Fin n → ℝ)) (x := p₀) hs).comp
        (FiberBundle.continuous_proj (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)).continuousAt
    have hvz : ContinuousAt (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M => (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ z).2) z₀ :=
      continuous_snd.continuousAt.comp
        ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).continuousOn.continuousAt
          ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).open_source.mem_nhds hz0))
    have hxy : extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ z₀.proj ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).target :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_source hs
    have hX : ContinuousAt (fun z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M =>
        orientChart T p₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ z.proj)) z₀ :=
      ContinuousAt.comp (g := orientChart T p₀) (continuousAt_orientChart T p₀ hxy) hcz
    exact continuousAt_gpairAt_fun (g.toNondegMetric.isCoordMetric_coordMetric p₀)
      (by exact (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).map_source hs) hcz hvz hX
  refine hch.congr ?_
  filter_upwards [hsrc] with z hz
  rw [g_eq_gpair g p₀ z.proj hz]
  unfold orientChart comp
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).left_inv hz]

variable {m : ℕ} {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- **A future null geodesic of a flow family stays future directed.** -/
theorem FlowFamily.future_along (hF : FlowFamily g Γ zS Nz J Sg) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (hfut : g.g (zS σ).proj (zS σ).snd (T.X (zS σ).proj) < 0)
    {t : ℝ} (ht : t ∈ J) :
    g.g (Γ (zS σ) t) (phase (n := n) (Γ (zS σ)) t).snd (T.X (Γ (zS σ) t)) < 0 := by
  have hphase0 : phase (n := n) (Γ (zS σ)) 0 = zS σ := hF.phase_zero _ (hF.mem_Nz σ hσ)
  have hw0 : (phase (n := n) (Γ (zS σ)) 0).snd ≠ 0 := by
    intro h
    rw [hphase0] at h
    rw [h] at hfut
    simp at hfut
  set f : ℝ → ℝ := fun s => g.g (phase (n := n) (Γ (zS σ)) s).proj (phase (n := n) (Γ (zS σ)) s).snd
    (T.X (phase (n := n) (Γ (zS σ)) s).proj) with hf
  have hproj : ∀ s, (phase (n := n) (Γ (zS σ)) s).proj = Γ (zS σ) s := fun s => rfl
  have hcont : ContinuousOn f J := by
    have h1 : ContinuousOn (fun s : ℝ => phase (n := n) (Γ (zS σ)) s) J := by
      have hsm := hF.smooth_flow.continuousOn
      have hc : Continuous (fun s : ℝ => ((zS σ, s) : TangentBundle 𝓘(ℝ, Fin n → ℝ) M × ℝ)) :=
        continuous_const.prodMk continuous_id
      exact hsm.comp hc.continuousOn (fun s hs => ⟨hF.mem_Nz σ hσ, hs⟩)
    exact (continuous_pairX T).comp_continuousOn h1
  have hne : ∀ s ∈ J, f s ≠ 0 := by
    intro s hs h0
    subst hnm
    have hnull := hF.null_of_zero hk σ hσ s hs
    have hw := phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ))
      hF.zero_mem hs hw0
    exact hw (eq_zero_of_null_orth_timelike (g.lorentzian _) (X := T.X (Γ (zS σ) s)) (T.timelike _) h0 hnull)
  have hf0 : f 0 < 0 := by
    show g.g (phase (n := n) (Γ (zS σ)) 0).proj (phase (n := n) (Γ (zS σ)) 0).snd
      (T.X (phase (n := n) (Γ (zS σ)) 0).proj) < 0
    rw [hphase0]; exact hfut
  by_contra hcon
  have hft : 0 ≤ f t := not_lt.1 hcon
  obtain ⟨s, hsJ, hs0⟩ := hF.convex_J.isPreconnected.intermediate_value hF.zero_mem ht hcont
    (show (0 : ℝ) ∈ Icc (f 0) (f t) from ⟨hf0.le, hft⟩)
  exact hne s hsJ hs0

/-- **A future null geodesic pairs negatively with any field future timelike for `T`.** -/
theorem FlowFamily.pair_field_neg (hF : FlowFamily g Γ zS Nz J Sg) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (hfut : g.g (zS σ).proj (zS σ).snd (T.X (zS σ).proj) < 0)
    (X' : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
    (hX' : ∀ x, g.g x (X' x) (X' x) < 0 ∧ g.g x (X' x) (T.X x) < 0)
    {t : ℝ} (ht : t ∈ J) :
    g.g (Γ (zS σ) t) (phase (n := n) (Γ (zS σ)) t).snd (X' (Γ (zS σ) t)) < 0 := by
  have hfa := hF.future_along T hnm hk hσ hfut ht
  have hphase0 : phase (n := n) (Γ (zS σ)) 0 = zS σ := hF.phase_zero _ (hF.mem_Nz σ hσ)
  have hw0 : (phase (n := n) (Γ (zS σ)) 0).snd ≠ 0 := by
    intro h
    rw [hphase0] at h
    rw [h] at hfut
    simp at hfut
  subst hnm
  have hnull := hF.null_of_zero hk σ hσ t ht
  have hw := phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ))
    hF.zero_mem ht hw0
  exact neg_of_future_null (g.lorentzian _) (T.timelike _) (hX' _).1 (hX' _).2 hnull hfa hw

end Lightlike.Penrose
