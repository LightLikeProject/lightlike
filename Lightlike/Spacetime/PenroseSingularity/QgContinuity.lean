import Lightlike.Spacetime.PenroseSingularity.FocalVector
import Lightlike.Spacetime.PenroseSingularity.PosDefOpen
import Lightlike.Spacetime.PenroseSingularity.ChartSegment
import Lightlike.Spacetime.PenroseSingularity.JacobiUnique

/-!
# Continuity of the Gram matrix of a flow family in `t` (G1-012, step D4)

`Qg σ t` is locally the Gram matrix of smooth chart Jacobi fields, hence continuous in `t`; positive definiteness
therefore persists near a time at which it holds.
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

/-- **`Qg σ ·` is continuous at every time of `J`.** -/
theorem FlowFamily.continuousAt_Qg (hF : FlowFamily g Γ zS Nz J Sg) (hm : 0 < m)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) {t : ℝ} (ht : t ∈ J) : ContinuousAt (Qg g Γ zS σ) t := by
  obtain ⟨cj⟩ := hF.exists_chartJac hm hk hperp hσ ht
  set x₀ := Γ (zS σ) t with hx₀
  have hgc : Lightlike.IsCoordMetric (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    g.toNondegMetric.isCoordMetric_coordMetric x₀
  have hHs := cj.hCF.smooth
  have hWo := cj.hCF.isOpen
  set H := chartH g Γ zS x₀ with hH
  have hmem : ∀ s ∈ cj.I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ cj.W := cj.hIW
  have hcurve : Continuous (fun s : ℝ => ((s, σ) : ℝ × (Fin m → ℝ))) := by fun_prop
  have hgam : ContinuousAt (fun s => H (s, σ)) t :=
    ((hHs.continuousOn.continuousAt (hWo.mem_nhds cj.hW0)).comp_of_eq hcurve.continuousAt rfl)
  have hJi : ∀ i, ContinuousAt (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) t := by
    intro i
    have h1 : ContDiffOn ℝ 2 (fderiv ℝ H) cj.W := hHs.fderiv_of_isOpen hWo (by norm_num)
    have h2 : ContinuousAt (fderiv ℝ H) (t, σ) := h1.continuousOn.continuousAt (hWo.mem_nhds cj.hW0)
    have h3 : ContinuousAt (fun s : ℝ => fderiv ℝ H (s, σ)) t :=
      h2.comp_of_eq hcurve.continuousAt rfl
    exact h3.clm_apply continuousAt_const
  have hU : H (t, σ) ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := cj.hCF.mem _ cj.hW0
  have hgram : ContinuousAt (fun s => gramQ (g.coordMetric x₀) (fun s => H (s, σ))
      (fun i s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) s) t := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact continuousAt_gpairAt_fun (y := fun s => H (s, σ)) (u := fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1))
      (v := fun s => fderiv ℝ H (s, σ) (0, Pi.single j 1)) hgc hU hgam (hJi i) (hJi j)
  refine hgram.congr ?_
  filter_upwards [cj.isOpen_I.mem_nhds cj.t_mem] with s hs
  exact (cj.hQeq s hs).symm

/-- The set of times at which the Gram matrix is positive definite is open (inside `J`). -/
theorem FlowFamily.isOpen_posDef (hF : FlowFamily g Γ zS Nz J Sg) (hm : 0 < m)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) : IsOpen {t | t ∈ J ∧ (Qg g Γ zS σ t).PosDef} := by
  refine isOpen_iff_mem_nhds.2 fun t ⟨ht, hp⟩ => ?_
  have hc := hF.continuousAt_Qg hm hk hperp hσ ht
  have hev := eventually_posDef hc (fun s => qg_isHermitian σ s) hp
  filter_upwards [hF.isOpen_J.mem_nhds ht, hev] with s hsJ hsp using ⟨hsJ, hsp⟩

/-- **The first time at which the Gram matrix degenerates.** -/
theorem FlowFamily.exists_first_degenerate (hF : FlowFamily g Γ zS Nz J Sg) (hm : 0 < m)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {σ : Fin m → ℝ} (hσ : σ ∈ Sg) (h0 : (Qg g Γ zS σ 0).PosDef) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (hpos : 0 < t₀)
    (hdeg : ¬ (Qg g Γ zS σ t₀).PosDef) :
    ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ¬ (Qg g Γ zS σ ts).PosDef ∧
      ∀ t, 0 ≤ t → t < ts → (Qg g Γ zS σ t).PosDef := by
  have hIcc : Icc (0 : ℝ) t₀ ⊆ J := hF.convex_J.ordConnected.out hF.zero_mem ht₀
  set S : Set ℝ := Icc 0 t₀ \ {t | t ∈ J ∧ (Qg g Γ zS σ t).PosDef} with hS
  have hSc : IsClosed S := isClosed_Icc.sdiff (hF.isOpen_posDef hm hk hperp hσ)
  have ht₀S : t₀ ∈ S := ⟨⟨hpos.le, le_rfl⟩, fun h => hdeg h.2⟩
  have hne : S.Nonempty := ⟨t₀, ht₀S⟩
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hne hbdd
  have hle : sInf S ≤ t₀ := csInf_le hbdd ht₀S
  have hge : 0 ≤ sInf S := hmem.1.1
  have hnot : ¬ (Qg g Γ zS σ (sInf S)).PosDef := fun h => hmem.2 ⟨hIcc hmem.1, h⟩
  refine ⟨sInf S, ?_, hle, hnot, fun t ht0 htl => ?_⟩
  · rcases hge.eq_or_lt with h | h
    · exact absurd (by rw [← h]; exact h0) hnot
    · exact h
  · by_contra hcon
    have : t ∈ S := ⟨⟨ht0, htl.le.trans hle⟩, fun h => hcon h.2⟩
    exact absurd (csInf_le hbdd this) (not_le.2 htl)

end Lightlike.Penrose
