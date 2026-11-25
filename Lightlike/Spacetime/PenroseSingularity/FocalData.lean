import Lightlike.Spacetime.PenroseSingularity.QgContinuity
import Lightlike.Spacetime.PenroseSingularity.ChartFocal
import Lightlike.Spacetime.PenroseSingularity.ChartLorentz
import Lightlike.Spacetime.PenroseSingularity.FutureAlong
import Lightlike.Spacetime.PenroseSingularity.StartIdentity

/-!
# Focal data at the first degenerate time (G1-012, step D4)

At the first time `ts` at which the Gram matrix of a null normal flow family degenerates there are a non-zero vector
`v` and a number `c` with `jacV v ts = c w`, and the corrected covariant derivative has positive norm.
-/

open Set Filter Topology Manifold Bundle Matrix
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- **A null Jacobi field orthogonal to the velocity is a multiple of it.** -/
theorem FlowFamily.jacV_parallel (hF : FlowFamily g Γ zS Nz J Sg) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (hw0 : (phase (n := n) (Γ (zS σ)) 0).snd ≠ 0) {t : ℝ} (ht : t ∈ J)
    (v : Fin m → ℝ) (hnull : g.g (Γ (zS σ) t) (jacV g Γ zS σ v t) (jacV g Γ zS σ v t) = 0) :
    ∃ c : ℝ, jacV g Γ zS σ v t = c • (phase (n := n) (Γ (zS σ)) t).snd := by
  have hwnull := hF.null_of_zero hk σ hσ t ht
  have hne : (phase (n := n) (Γ (zS σ)) t).snd ≠ 0 :=
    phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ)) hF.zero_mem ht hw0
  have horth := hF.jacV_orth hk hperp hσ v ht
  have hsymm := g.symm (Γ (zS σ) t) (jacV g Γ zS σ v t) (phase (n := n) (Γ (zS σ)) t).snd
  subst hnm
  exact eq_smul_of_null_orth (g.lorentzian (Γ (zS σ) t)) hwnull hne (by rw [hsymm]; exact horth) hnull

/-- The quadratic form of the chart Gram matrix is the norm of the combination. -/
theorem gram_quadratic {g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Lightlike.IsCoordMetric g' U) {γ : ℝ → Fin n → ℝ} {Jf : Fin m → ℝ → Fin n → ℝ} {t : ℝ}
    (ht : γ t ∈ U) (v : Fin m → ℝ) :
    v ⬝ᵥ (gramQ g' γ Jf t *ᵥ v) = gpairAt g' (γ t) (∑ i, v i • Jf i t) (∑ i, v i • Jf i t) := by
  rw [gpairAt_sum_smul_left]
  have hinner : ∀ i, gpairAt g' (γ t) (Jf i t) (∑ j, v j • Jf j t) = ∑ j, v j * gpairAt g' (γ t) (Jf j t) (Jf i t) := by
    intro i
    rw [gpairAt_symm hg ht (Jf i t) (∑ j, v j • Jf j t), gpairAt_sum_smul_left]
  simp only [hinner]
  simp only [Matrix.mulVec, dotProduct, gramQ, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gpairAt_symm hg ht (Jf i t) (Jf j t)]
  ring

/-- A non-zero tangent vector has non-zero components. -/
theorem comp_ne_zero (p₀ : M) {x : M} (hb : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    {v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x} (hv : v ≠ 0) : comp p₀ v ≠ 0 := by
  intro h
  apply hv
  have h1 := (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symm_apply_apply_mk hb v
  have h2 : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ (⟨x, v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)).2 = comp p₀ v := rfl
  rw [h2, h] at h1
  rw [← h1]
  have := (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symmL ℝ x |>.map_zero
  rw [Bundle.Trivialization.symmL_apply _ hb] at this
  exact this

/-- **Focal data at the first degenerate time, in the chart there.** -/
theorem FlowFamily.focal_chart (hF : FlowFamily g Γ zS Nz J Sg) (hm : 0 < m) (hnm : n = m + 2)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (hw0 : (phase (n := n) (Γ (zS σ)) 0).snd ≠ 0)
    (h0 : (Qg g Γ zS σ 0).PosDef) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hpos : 0 < t₀)
    (hdeg : ¬ (Qg g Γ zS σ t₀).PosDef) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ts ∈ J ∧ ∃ cj : ChartJac g Γ zS J Sg σ ts, ∃ (v : Fin m → ℝ) (c : ℝ),
      v ≠ 0 ∧
      (∑ i, v i • fderiv ℝ (chartH g Γ zS (Γ (zS σ) ts)) (ts, σ) (0, Pi.single i 1) =
        c • fderiv ℝ (chartH g Γ zS (Γ (zS σ) ts)) (ts, σ) (1, 0)) ∧
      0 < gpairAt (g.coordMetric (Γ (zS σ) ts)) (chartH g Γ zS (Γ (zS σ) ts) (ts, σ))
        (∑ i, v i • cj.P i ts - (c / ts) • fderiv ℝ (chartH g Γ zS (Γ (zS σ) ts)) (ts, σ) (1, 0))
        (∑ i, v i • cj.P i ts - (c / ts) • fderiv ℝ (chartH g Γ zS (Γ (zS σ) ts)) (ts, σ) (1, 0)) := by
  obtain ⟨ts, hts0, htsle, hdegs, hbefore⟩ := hF.exists_first_degenerate hm hk hperp hσ h0 ht₀ hpos hdeg
  have hIcc : Icc (0 : ℝ) t₀ ⊆ J := hF.convex_J.ordConnected.out hF.zero_mem ht₀
  have htsJ : ts ∈ J := hIcc ⟨hts0.le, htsle⟩
  obtain ⟨cj⟩ := hF.exists_chartJac hm hk hperp hσ htsJ
  obtain ⟨v, hv0, hvnull⟩ := hF.exists_degenerate_vector hnm hk hperp hσ hw0 htsJ hdegs
  set x₀ : M := Γ (zS σ) ts with hx₀
  set gc := g.coordMetric x₀ with hgc
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  set H := chartH g Γ zS x₀ with hH
  have hgU : Lightlike.IsCoordMetric gc ψ.target := g.toNondegMetric.isCoordMetric_coordMetric x₀
  set Jf : Fin m → ℝ → Fin n → ℝ := fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1) with hJf
  set wf : ℝ → Fin n → ℝ := fun s => fderiv ℝ H (s, σ) (1, 0) with hwf
  have hγU : ∀ t ∈ cj.I, H (t, σ) ∈ ψ.target := fun t ht => cj.hCF.mem _ (cj.hIW t ht)
  have hgq : ∀ t ∈ cj.I, v ⬝ᵥ (gramQ gc (fun s => H (s, σ)) Jf t *ᵥ v) =
      gpairAt gc (H (t, σ)) (∑ i, v i • Jf i t) (∑ i, v i • Jf i t) := fun t ht =>
    gram_quadratic (γ := fun s => H (s, σ)) (Jf := Jf) (t := t) hgU (hγU t ht) v
  have hQts : v ⬝ᵥ (gramQ gc (fun s => H (s, σ)) Jf ts *ᵥ v) = 0 := by
    rw [← cj.hQeq ts cj.t_mem, qg_quadratic]; exact hvnull
  have hnullS : gpairAt gc (H (ts, σ)) (∑ i, v i • Jf i ts) (∑ i, v i • Jf i ts) = 0 := by
    rw [← hgq ts cj.t_mem]; exact hQts
  have hperpJ : ∀ t ∈ cj.I, ∀ i, gpairAt gc (H (t, σ)) (wf t) (Jf i t) = 0 := fun t ht i =>
    cj.hω (t, σ) (cj.hIW t ht) i
  have hnullw : ∀ t ∈ cj.I, gpairAt gc (H (t, σ)) (wf t) (wf t) = 0 := fun t ht =>
    cj.hCF.null (t, σ) (cj.hIW t ht)
  have hsrc : x₀ ∈ ψ.source := mem_extChartAt_source x₀
  have hwne : wf ts ≠ 0 := by
    have hid := (cj.hid (ts, σ) cj.hW0).2.2.2
    have hb : x₀ ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀).baseSet := by
      simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hsrc
    have hne : (phase (n := n) (Γ (zS σ)) ts).snd ≠ 0 :=
      phase_snd_ne_zero g hF.isOpen_J hF.convex_J.isPreconnected (hF.geo _ (hF.mem_Nz σ hσ)) hF.zero_mem htsJ hw0
    have := comp_ne_zero x₀ hb hne
    intro h
    exact this (hid.trans h)
  have hperpS : ∀ t ∈ cj.I, gpairAt gc (H (t, σ)) (∑ i, v i • Jf i t) (wf t) = 0 := by
    intro t ht
    rw [gpairAt_sum_smul_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [gpairAt_symm hgU (hγU t ht), hperpJ t ht i]; ring
  have hHts : H (ts, σ) = ψ x₀ := rfl
  have hnn : ∀ z, gpairAt gc (H (ts, σ)) z (wf ts) = 0 → 0 ≤ gpairAt gc (H (ts, σ)) z z := fun z hz => by
    rw [hHts] at hz ⊢
    exact chart_null_orth_nonneg g hnm x₀ x₀ hsrc (by rw [← hHts]; exact hnullw ts cj.t_mem) hwne hz
  have hpar : ∀ z, gpairAt gc (H (ts, σ)) z (wf ts) = 0 → gpairAt gc (H (ts, σ)) z z = 0 →
      ∃ c' : ℝ, z = c' • wf ts := fun z hz hzz => by
    rw [hHts] at hz hzz
    exact chart_null_orth_parallel g hnm x₀ x₀ hsrc (by rw [← hHts]; exact hnullw ts cj.t_mem) hwne hz hzz
  obtain ⟨c, hc⟩ := hpar _ (hperpS ts cj.t_mem) hnullS
  refine ⟨ts, hts0, htsle, htsJ, cj, v, c, hv0, hc, ?_⟩
  have hQpos : ∀ᶠ t in 𝓝[<] ts, 0 < gpairAt gc (H (t, σ)) (∑ i, v i • Jf i t) (∑ i, v i • Jf i t) := by
    have h1 : ∀ᶠ t in 𝓝[<] ts, t ∈ cj.I :=
      eventually_nhdsWithin_of_eventually_nhds (cj.isOpen_I.mem_nhds cj.t_mem)
    have h2 : ∀ᶠ t in 𝓝[<] ts, 0 < t := by
      have : Ioo (0 : ℝ) ts ∈ 𝓝[<] ts := Ioo_mem_nhdsLT hts0
      filter_upwards [this] with t ht using ht.1
    have h3 : ∀ᶠ t in 𝓝[<] ts, t < ts := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
    have hpd := hbefore t ht2.le ht3
    have := hpd.dotProduct_mulVec_pos hv0
    rw [star_trivial, cj.hQeq t ht1, hgq t ht1] at this
    exact this
  exact chart_focal_pos hgU cj.isOpen_I cj.t_mem hts0 hγU
    (hγ := (cj.hJ ⟨0, hm⟩).geodesic) cj.hJ hnullw hperpJ hnn hpar v hc hQpos

end Lightlike.Penrose
