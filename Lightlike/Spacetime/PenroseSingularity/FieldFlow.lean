import Lightlike.Spacetime.Causal.IntegralCurves
import Lightlike.ODE.LocalFlow
import Lightlike.ODE.FlowDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# Continuity of the flow of a `C¹` vector field on a manifold (G1-012, hproj / hopen)

For a `C¹` vector field `Y` on a Hausdorff manifold without boundary, the maximal integral curves
`curveMax Y y` depend continuously on `(y, t)` on the (open) set of `(y, t)` with `t ∈ domMax Y y`.
The local statement is the flow box of the chart expression of `Y`
(`exists_local_field_flow`); it is propagated along the integral curve by continuous induction.
-/

open Bundle Manifold Set Filter Topology Metric
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
  {Y : (x : M) → TangentSpace I x}

set_option backward.isDefEq.respectTransparency false in
/-- **A chart curve with the chart expression of `Y` as derivative is an integral curve.** -/
theorem hasMFDerivAt_symm_comp {x₀ : M} {f : ℝ → E} {t : ℝ}
    (hf3 : f t ∈ interior (extChartAt I x₀).target)
    (h : HasDerivAt f (fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
      (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t)))
      (Y ((extChartAt I x₀).symm (f t)))) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ((extChartAt I x₀).symm (f t)))) := by
  set xₜ : M := (extChartAt I x₀).symm (f t) with hxₜ
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  rw [← tangentCoordChange_def] at h
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (Y xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := Y xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- The chart expression of `Y` in the chart at `x₀` (the vector field of the ODE for integral curves). -/
def chartField (x₀ : M) (Y : (x : M) → TangentSpace I x) (y : E) : E :=
  fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I ((extChartAt I x₀).symm y)).symm) (range I)
    (extChartAt I ((extChartAt I x₀).symm y) ((extChartAt I x₀).symm y))
    (Y ((extChartAt I x₀).symm y))

theorem contDiffAt_chartField (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (x₀ : M) :
    ContDiffAt ℝ 1 (chartField x₀ Y) (extChartAt I x₀ x₀) := by
  have hv := hY.contMDiffAt (x := x₀)
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  exact (hv.contDiffAt (range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I)))).snd

end Causal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The flow of a flow box is jointly continuous.** -/
theorem IsFlowBox.continuousOn_uncurry {V : E → E} {x₀ : E} {a r T : ℝ} {K : NNReal}
    {Φ : ℝ → E → E} (h : IsFlowBox V x₀ a r T K Φ) :
    ContinuousOn (fun q : ℝ × E => Φ q.1 q.2) (Ioo (-T) T ×ˢ ball x₀ r) := by
  intro q hq
  have hqo : Ioo (-T) T ×ˢ ball x₀ r ∈ 𝓝 q := (isOpen_Ioo.prod isOpen_ball).mem_nhds hq
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × E => ‖p.2 - q.2‖ * Real.exp (K * T)) (𝓝 q) (𝓝 0) := by
    have : Tendsto (fun p : ℝ × E => ‖p.2 - q.2‖) (𝓝 q) (𝓝 0) := by
      have := (continuous_snd.tendsto q).sub_const q.2 |>.norm
      simpa using this
    simpa using this.mul_const (Real.exp (K * T))
  have h2 : Tendsto (fun p : ℝ × E => ‖Φ p.1 q.2 - Φ q.1 q.2‖) (𝓝 q) (𝓝 0) := by
    have hc : ContinuousAt (fun s => Φ s q.2) q.1 :=
      (h.hasDerivAt q.2 hq.2 q.1 (Ioo_subset_Icc_self hq.1)).continuousAt
    have := ((hc.tendsto).comp (continuous_fst.tendsto q)).sub_const (Φ q.1 q.2) |>.norm
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa using h1.add h2)
  filter_upwards [hqo] with p hp
  calc ‖Φ p.1 p.2 - Φ q.1 q.2‖
      ≤ ‖Φ p.1 p.2 - Φ p.1 q.2‖ + ‖Φ p.1 q.2 - Φ q.1 q.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖p.2 - q.2‖ * Real.exp (K * T) + ‖Φ p.1 q.2 - Φ q.1 q.2‖ := by
        gcongr
        exact h.norm_flow_sub_le hp.2 hq.2 (Ioo_subset_Icc_self hp.1)

end ODE

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]
  {Y : (x : M) → TangentSpace I x}

/-- **The local flow of a `C¹` vector field**: integral curves through the points of a neighbourhood
of `y₀` exist on a common interval `(-δ, δ)`, and the maximal integral curve is jointly continuous
in `(y, t)` there. -/
theorem exists_local_field_flow (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y₀ : M) :
    ∃ (N : Set M) (δ : ℝ), IsOpen N ∧ y₀ ∈ N ∧ 0 < δ ∧ (∀ y ∈ N, Ioo (-δ) δ ⊆ domMax Y y) ∧
      ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N ×ˢ Ioo (-δ) δ) := by
  set ψ := extChartAt I y₀ with hψ
  have hxt : ψ y₀ ∈ interior ψ.target :=
    (I.isInteriorPoint_iff).1 (BoundarylessManifold.isInteriorPoint (I := I))
  obtain ⟨aU, haU, hballU⟩ := Metric.isOpen_iff.mp isOpen_interior (ψ y₀) hxt
  obtain ⟨A, hA, Hb⟩ := Lightlike.ODE.exists_isFlowBox (contDiffAt_chartField hY y₀)
  set a : ℝ := min A aU with ha
  have ha0 : 0 < a := lt_min hA haU
  obtain ⟨r, T, K, Φ, h⟩ := Hb a ha0 (min_le_left _ _)
  set N : Set M := ψ.source ∩ ψ ⁻¹' (ball (ψ y₀) r) with hN
  have hNo : IsOpen N := (continuousOn_extChartAt (I := I) y₀).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) y₀) isOpen_ball
  have hy₀N : y₀ ∈ N := ⟨mem_extChartAt_source y₀, mem_ball_self h.r_pos⟩
  have hIC : ∀ y ∈ N, IsIC Y y (-T) T (fun t => ψ.symm (Φ t (ψ y))) := by
    intro y hy
    refine ⟨by linarith [h.T_pos], h.T_pos, ?_, ?_⟩
    · show ψ.symm (Φ 0 (ψ y)) = y
      rw [h.flow_zero _ hy.2]
      exact ψ.left_inv hy.1
    · intro t ht
      have htI : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
      have hf3 : Φ t (ψ y) ∈ interior ψ.target :=
        hballU ((ball_subset_ball (min_le_right _ _)) (h.flow_mem _ hy.2 t htI))
      have hd := h.hasDerivAt _ hy.2 t htI
      have := hasMFDerivAt_symm_comp (I := I) (Y := Y) (x₀ := y₀) (f := fun s => Φ s (ψ y)) hf3 hd
      exact this.hasMFDerivWithinAt
  have hcm : ∀ y ∈ N, ∀ t ∈ Ioo (-T) T, curveMax Y y t = ψ.symm (Φ t (ψ y)) :=
    fun y hy t ht => curveMax_eq hY (hIC y hy) ht
  refine ⟨N, T, hNo, hy₀N, h.T_pos, fun y hy t ht => ⟨-T, T, _, hIC y hy, ht⟩, ?_⟩
  have hΦc := ODE.IsFlowBox.continuousOn_uncurry h
  have hmaps : MapsTo (fun p : M × ℝ => (p.2, ψ p.1)) (N ×ˢ Ioo (-T) T)
      (Ioo (-T) T ×ˢ ball (ψ y₀) r) := fun p hp => ⟨hp.2, hp.1.2⟩
  have hc1 : ContinuousOn (fun p : M × ℝ => (p.2, ψ p.1)) (N ×ˢ Ioo (-T) T) :=
    continuousOn_snd.prodMk (((continuousOn_extChartAt (I := I) y₀).mono
      (fun y hy => hy.1)).comp continuousOn_fst (fun p hp => hp.1))
  have hc2 := hΦc.comp hc1 hmaps
  have hsymm := continuousOn_extChartAt_symm (I := I) y₀
  have hc3 : ContinuousOn (fun p : M × ℝ => ψ.symm (Φ p.2 (ψ p.1))) (N ×ˢ Ioo (-T) T) :=
    hsymm.comp hc2 (fun p hp => (interior_subset (hballU ((ball_subset_ball (min_le_right _ _))
      (h.flow_mem _ hp.1.2 p.2 (Ioo_subset_Icc_self hp.2))))))
  exact hc3.congr fun p hp => hcm p.1 hp.1 p.2 hp.2

open Classical in
/-- **Extending a maximal integral curve by the local flow at a later point.** -/
theorem extend_curveMax (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y : M}
    {ε δ t : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (hJ₁ : Ioo (-ε) (t + ε) ⊆ domMax Y y) (hδ : 0 < δ)
    (hJ₂ : Ioo (-δ) δ ⊆ domMax Y (curveMax Y y t)) :
    ∀ u ∈ Ioo (t - δ) (t + δ),
      u ∈ domMax Y y ∧ curveMax Y y u = curveMax Y (curveMax Y y t) (u - t) := by
  set yt := curveMax Y y t with hyt
  set J₁ : Set ℝ := Ioo (-ε) (t + ε) with hJ₁d
  set J₂ : Set ℝ := Ioo (t - δ) (t + δ) with hJ₂d
  have htJ₁ : t ∈ J₁ := ⟨by linarith, by linarith⟩
  have htJ₂ : t ∈ J₂ := ⟨by linarith, by linarith⟩
  have hA : IsMIntegralCurveOn (curveMax Y y) Y J₁ :=
    (isMIntegralCurveOn_curveMax hY y).mono hJ₁
  have hB : IsMIntegralCurveOn (fun u => curveMax Y yt (u - t)) Y J₂ := by
    have := (isMIntegralCurveOn_comp_sub (γ := curveMax Y yt) (v := Y) (s := domMax Y yt)
      (dt := t)).2 (isMIntegralCurveOn_curveMax hY yt)
    refine this.mono ?_
    intro u hu
    exact hJ₂ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- agreement on the overlap
  have hov : t ∈ Ioo (max (-ε) (t - δ)) (min (t + ε) (t + δ)) :=
    ⟨max_lt htJ₁.1 htJ₂.1, lt_min htJ₁.2 htJ₂.2⟩
  have hagr : EqOn (curveMax Y y) (fun u => curveMax Y yt (u - t))
      (Ioo (max (-ε) (t - δ)) (min (t + ε) (t + δ))) :=
    isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hov hY
      (hA.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
      (hB.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
      (by simp [hyt, curveMax_zero hY])
  set c : ℝ → M := fun u => if u ∈ J₁ then curveMax Y y u else curveMax Y yt (u - t) with hc
  have hcJ₁ : ∀ u ∈ J₁, c u = curveMax Y y u := fun u hu => if_pos hu
  have hcJ₂ : ∀ u ∈ J₂, c u = curveMax Y yt (u - t) := fun u hu => by
    by_cases h1 : u ∈ J₁
    · rw [hcJ₁ u h1]
      exact hagr ⟨max_lt h1.1 hu.1, lt_min h1.2 hu.2⟩
    · exact if_neg h1
  set a : ℝ := min (-ε) (t - δ) with ha
  set b : ℝ := max (t + ε) (t + δ) with hb
  have hint : IsMIntegralCurveOn c Y (Ioo a b) := by
    intro u hu
    have hu12 : u ∈ J₁ ∨ u ∈ J₂ := by
      by_cases h1 : -ε < u
      · by_cases h2 : u < t + ε
        · exact Or.inl ⟨h1, h2⟩
        · right
          rcases lt_max_iff.1 hu.2 with h | h
          · exact absurd h h2
          · exact ⟨by linarith [not_lt.1 h2], h⟩
      · right
        rcases min_lt_iff.1 hu.1 with h | h
        · exact absurd h (by simpa using h1)
        · exact ⟨h, by linarith [not_lt.1 h1]⟩
    rcases hu12 with hu1 | hu2
    · have h1 := (hA u hu1).hasMFDerivAt (isOpen_Ioo.mem_nhds hu1)
      have hev : c =ᶠ[𝓝 u] curveMax Y y :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu1) fun r hr => hcJ₁ r hr
      have h2 := h1.congr_of_eventuallyEq hev
      rw [← hcJ₁ u hu1] at h2
      exact h2.hasMFDerivWithinAt
    · have h1 := (hB u hu2).hasMFDerivAt (isOpen_Ioo.mem_nhds hu2)
      have hev : c =ᶠ[𝓝 u] fun r => curveMax Y yt (r - t) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu2) fun r hr => hcJ₂ r hr
      have h2 := h1.congr_of_eventuallyEq hev
      refine (h2.congr_mfderiv ?_).hasMFDerivWithinAt
      have key : ∀ p q : M, p = q → ((tangentSpaceCast I p q : TangentSpace I p →L[ℝ] TangentSpace I q).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y p)) : ℝ →L[ℝ] TangentSpace I q) =
          (1 : ℝ →L[ℝ] ℝ).smulRight (Y q) := by
        rintro p q rfl
        rfl
      exact key _ _ (hcJ₂ u hu2).symm
  have hIC : IsIC Y y a b c := by
    refine ⟨lt_of_le_of_lt (min_le_left _ _) (by linarith), lt_of_lt_of_le (by linarith) (le_max_left _ _),
      ?_, hint⟩
    rw [hcJ₁ 0 ⟨by linarith, by linarith⟩]
    exact curveMax_zero hY y
  intro u hu
  have huab : u ∈ Ioo a b :=
    ⟨lt_of_le_of_lt (min_le_right _ _) hu.1, lt_of_lt_of_le hu.2 (le_max_right _ _)⟩
  refine ⟨⟨a, b, c, hIC, huab⟩, ?_⟩
  rw [curveMax_eq hY hIC huab]
  exact hcJ₂ u hu

/-- **The germ of the flow along `[0, t]` at `y₀`**: a neighbourhood `N` of `y₀` whose maximal
integral curves exist on `(-ε, t + ε)` and are jointly continuous in `(y, s)` there. -/
def FFlowGerm (Y : (x : M) → TangentSpace I x) (y₀ : M) (t : ℝ) : Prop :=
  ∃ (N : Set M) (ε : ℝ), IsOpen N ∧ y₀ ∈ N ∧ 0 < ε ∧ (∀ y ∈ N, Ioo (-ε) (t + ε) ⊆ domMax Y y) ∧
    ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N ×ˢ Ioo (-ε) (t + ε))

/-- **Extending a flow germ by a local flow box.** -/
theorem fflowGerm_step (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y₀ : M} {t : ℝ}
    (ht : 0 ≤ t) {N : Set M} {ε : ℝ} (hNo : IsOpen N) (hy₀ : y₀ ∈ N) (hε : 0 < ε)
    (hdom : ∀ y ∈ N, Ioo (-ε) (t + ε) ⊆ domMax Y y)
    (hcont : ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N ×ˢ Ioo (-ε) (t + ε)))
    {N' : Set M} {δ' : ℝ} (hN'o : IsOpen N') (hδ' : 0 < δ')
    (hdom' : ∀ y ∈ N', Ioo (-δ') δ' ⊆ domMax Y y)
    (hcont' : ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N' ×ˢ Ioo (-δ') δ'))
    (hF : curveMax Y y₀ t ∈ N') {t₂ : ℝ} (h1 : t ≤ t₂) (h2 : t₂ < t + δ') :
    FFlowGerm Y y₀ t₂ := by
  set J₁ : Set ℝ := Ioo (-ε) (t + ε) with hJ₁
  set J₂ : Set ℝ := Ioo (t - δ') (t + δ') with hJ₂
  have htJ₁ : t ∈ J₁ := ⟨by linarith, by linarith⟩
  set F : M → M := fun y => curveMax Y y t with hFdef
  have hFc : ContinuousOn F N :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) (fun y hy => ⟨hy, htJ₁⟩)
  set N₁ := N ∩ F ⁻¹' N' with hN₁
  have hN₁o : IsOpen N₁ := hFc.isOpen_inter_preimage hNo hN'o
  have hy₀N₁ : y₀ ∈ N₁ := ⟨hy₀, hF⟩
  have hext : ∀ y ∈ N₁, ∀ u ∈ J₂, u ∈ domMax Y y ∧ curveMax Y y u = curveMax Y (F y) (u - t) :=
    fun y hy => extend_curveMax hY hε ht (hdom y hy.1) hδ' (hdom' _ hy.2)
  set ε₂ : ℝ := min ε (t + δ' - t₂) with hε₂
  have hε₂pos : 0 < ε₂ := lt_min hε (by linarith)
  have hsub : Ioo (-ε₂) (t₂ + ε₂) ⊆ J₁ ∪ J₂ := by
    intro σ hσ
    by_cases h : σ < t + ε
    · exact Or.inl ⟨by linarith [hσ.1, min_le_left ε (t + δ' - t₂)], h⟩
    · exact Or.inr ⟨by linarith [not_lt.1 h], by linarith [hσ.2, min_le_right ε (t + δ' - t₂)]⟩
  refine ⟨N₁, ε₂, hN₁o, hy₀N₁, hε₂pos, fun y hy σ hσ => ?_, ?_⟩
  · rcases hsub hσ with h | h
    · exact hdom y hy.1 h
    · exact (hext y hy σ h).1
  · have hA1 : ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N₁ ×ˢ J₁) :=
      hcont.mono (prod_mono inter_subset_left subset_rfl)
    have hA2 : ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) (N₁ ×ˢ J₂) := by
      have hmap : MapsTo (fun p : M × ℝ => (F p.1, p.2 - t)) (N₁ ×ˢ J₂) (N' ×ˢ Ioo (-δ') δ') :=
        fun p hp => ⟨hp.1.2, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
      have hc2 : ContinuousOn (fun p : M × ℝ => (F p.1, p.2 - t)) (N₁ ×ˢ J₂) :=
        ((hFc.mono inter_subset_left).comp continuousOn_fst (fun p hp => hp.1)).prodMk
          (continuousOn_snd.sub continuousOn_const)
      refine (hcont'.comp hc2 hmap).congr fun p hp => ?_
      exact (hext p.1 hp.1 p.2 hp.2).2
    intro p hp
    by_cases h1 : p.2 ∈ J₁
    · exact ((hA1.continuousAt ((hN₁o.prod isOpen_Ioo).mem_nhds ⟨hp.1, h1⟩))).continuousWithinAt
    · have h2 : p.2 ∈ J₂ := by
        rcases hsub hp.2 with h | h
        · exact absurd h h1
        · exact h
      exact ((hA2.continuousAt ((hN₁o.prod isOpen_Ioo).mem_nhds ⟨hp.1, h2⟩))).continuousWithinAt

/-- A flow germ restricts to earlier times. -/
theorem FFlowGerm.mono {y₀ : M} {t t' : ℝ} (h : FFlowGerm Y y₀ t) (htt : t' ≤ t) :
    FFlowGerm Y y₀ t' := by
  obtain ⟨N, ε, hNo, hy₀, hε, hdom, hcont⟩ := h
  have hsub : Ioo (-ε) (t' + ε) ⊆ Ioo (-ε) (t + ε) := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨N, ε, hNo, hy₀, hε, fun y hy => hsub.trans (hdom y hy), hcont.mono (prod_mono subset_rfl hsub)⟩

/-- **The flow of a `C¹` vector field is continuous along an integral curve**: if `[0, Λ]` lies in the
interval of the maximal integral curve through `y₀`, then the maximal integral curves through points near
`y₀` exist on `(-ε, Λ + ε)` and depend continuously on `(y, s)`. -/
theorem fflowGerm_along (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y₀ : M} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hsub : Icc 0 Λ ⊆ domMax Y y₀) : ∀ t ∈ Icc 0 Λ, FFlowGerm Y y₀ t := by
  set s : Set ℝ := {t | FFlowGerm Y y₀ t} with hs
  have hbox := fun t => exists_local_field_flow hY (curveMax Y y₀ t)
  have hcc : ∀ t ∈ Icc 0 Λ, ContinuousAt (curveMax Y y₀) t := fun t ht =>
    ((isMIntegralCurveOn_curveMax hY y₀).continuousOn.continuousAt
      ((isOpen_domMax hY y₀).mem_nhds (hsub ht)))
  have hmain : Icc 0 Λ ⊆ s := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · refine isClosed_of_closure_subset fun t' ht' => ?_
      have ht'I : t' ∈ Icc 0 Λ := isClosed_Icc.closure_subset_iff.2 inter_subset_right ht'
      refine ⟨?_, ht'I⟩
      obtain ⟨N', δ', hN'o, hw, hδ', hdom', hcont'⟩ := hbox t'
      obtain ⟨η, hη, hηN⟩ := Metric.eventually_nhds_iff.1 ((hcc t' ht'I).eventually
        (hN'o.mem_nhds hw))
      set m : ℝ := min η δ' with hm
      have hmpos : 0 < m := lt_min hη hδ'
      obtain ⟨t, htm, hts⟩ := mem_closure_iff.1 ht' (Ioo (t' - m) (t' + m)) isOpen_Ioo
        ⟨by linarith, by linarith⟩
      have htI : t ∈ Icc 0 Λ := hts.2
      by_cases hle : t' ≤ t
      · exact FFlowGerm.mono hts.1 hle
      · have hlt : t < t' := not_le.1 hle
        obtain ⟨N, ε, hNo, hz₀, hε, hdom, hcont⟩ := hts.1
        have hF : curveMax Y y₀ t ∈ N' := by
          refine hηN ?_
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [htm.1, htm.2, min_le_left η δ']
        exact fflowGerm_step hY htI.1 hNo hz₀ hε hdom hcont hN'o hδ' hdom' hcont' hF hlt.le
          (by linarith [htm.1, min_le_right η δ'])
    · obtain ⟨N, δ, hNo, hz₀, hδ, hdom, hcont⟩ := exists_local_field_flow hY y₀
      exact ⟨N, δ, hNo, hz₀, hδ, fun y hy => by simpa using hdom y hy, by simpa using hcont⟩
    · rintro x ⟨hxs, hx0, hxΛ⟩
      have hxI : x ∈ Icc 0 Λ := ⟨hx0, hxΛ.le⟩
      obtain ⟨N', δ', hN'o, hw, hδ', hdom', hcont'⟩ := hbox x
      obtain ⟨N, ε, hNo, hz₀, hε, hdom, hcont⟩ := hxs
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show x < x + δ' by linarith)) ?_
      intro t₂ ht₂
      exact fflowGerm_step hY hx0 hNo hz₀ hε hdom hcont hN'o hδ' hdom' hcont' hw ht₂.1.le
        (by linarith [ht₂.2])
  exact fun t ht => hmain ht

/-- Time reversal of an integral curve through `y`. -/
theorem IsIC.neg {y : M} {a b : ℝ} {c : ℝ → M} (h : IsIC Y y a b c) :
    IsIC (-Y) y (-b) (-a) (fun t => c (-t)) := by
  refine ⟨by linarith [h.2.1], by linarith [h.1], by simpa using h.2.2.1, ?_⟩
  have h1 := h.2.2.2.comp_mul (-1)
  have e : ((-1 : ℝ) • Y : (x : M) → TangentSpace I x) = -Y := by
    ext x; simp
  rw [e] at h1
  have e2 : (fun t => c (-t)) = c ∘ (· * (-1 : ℝ)) := by ext t; simp
  rw [e2]
  refine h1.mono fun t ht => ?_
  simp only [mem_setOf_eq, mem_Ioo] at ht ⊢
  constructor <;> linarith [ht.1, ht.2]

theorem domMax_neg (y : M) (t : ℝ) : t ∈ domMax (-Y) y ↔ -t ∈ domMax Y y := by
  constructor
  · rintro ⟨a, b, c, h, ht⟩
    have h' := IsIC.neg h
    rw [show (-(-Y) : (x : M) → TangentSpace I x) = Y by ext x; simp] at h'
    exact ⟨-b, -a, _, h', by constructor <;> linarith [ht.1, ht.2]⟩
  · rintro ⟨a, b, c, h, ht⟩
    exact ⟨-b, -a, _, IsIC.neg h, by constructor <;> linarith [ht.1, ht.2]⟩

theorem curveMax_neg (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y : M) {t : ℝ}
    (ht : t ∈ domMax Y y) : curveMax (-Y) y (-t) = curveMax Y y t := by
  obtain ⟨a, b, c, h, hab⟩ := ht
  rw [curveMax_eq hY h hab]
  have hY' : CMDiff 1 (fun x ↦ (⟨x, (-Y) x⟩ : TangentBundle I M)) := hY.neg_section
  rw [curveMax_eq hY' (IsIC.neg h) (t := -t) ⟨by linarith [hab.2], by linarith [hab.1]⟩]
  simp

/-- **The domain of the flow is open and the flow is continuous on it.** -/
theorem isOpen_flowDomain_continuousOn (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) :
    IsOpen {p : M × ℝ | p.2 ∈ domMax Y p.1} ∧
      ContinuousOn (fun p : M × ℝ => curveMax Y p.1 p.2) {p : M × ℝ | p.2 ∈ domMax Y p.1} := by
  have hY' : CMDiff 1 (fun x ↦ (⟨x, (-Y) x⟩ : TangentBundle I M)) := hY.neg_section
  -- the local statement at each point
  have loc : ∀ p : M × ℝ, p.2 ∈ domMax Y p.1 → ∃ (U : Set (M × ℝ)), IsOpen U ∧ p ∈ U ∧
      U ⊆ {q : M × ℝ | q.2 ∈ domMax Y q.1} ∧
      ContinuousOn (fun q : M × ℝ => curveMax Y q.1 q.2) U := by
    rintro ⟨y₀, t₀⟩ ht₀
    rcases le_total 0 t₀ with h0 | h0
    · have hsub : Icc 0 t₀ ⊆ domMax Y y₀ := fun s hs =>
        (ordConnected_domMax (Y := Y) y₀).out (zero_mem_domMax hY y₀) ht₀ hs
      obtain ⟨N, ε, hNo, hy₀, hε, hdom, hcont⟩ := fflowGerm_along hY h0 hsub t₀ ⟨h0, le_rfl⟩
      exact ⟨N ×ˢ Ioo (-ε) (t₀ + ε), hNo.prod isOpen_Ioo, ⟨hy₀, by constructor <;> linarith⟩,
        fun q hq => hdom q.1 hq.1 hq.2, hcont⟩
    · have ht₀' : -t₀ ∈ domMax (-Y) y₀ := (domMax_neg y₀ (-t₀)).2 (by simpa using ht₀)
      have hsub : Icc 0 (-t₀) ⊆ domMax (-Y) y₀ := fun s hs =>
        (ordConnected_domMax (Y := -Y) y₀).out (zero_mem_domMax hY' y₀) ht₀' hs
      obtain ⟨N, ε, hNo, hy₀, hε, hdom, hcont⟩ :=
        fflowGerm_along hY' (by linarith) hsub (-t₀) ⟨by linarith, le_rfl⟩
      refine ⟨N ×ˢ Ioo (t₀ - ε) ε, hNo.prod isOpen_Ioo, ⟨hy₀, by constructor <;> linarith⟩,
        fun q hq => ?_, ?_⟩
      · have := hdom q.1 hq.1 (show -q.2 ∈ Ioo (-ε) (-t₀ + ε) from
          ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩)
        have h2 := (domMax_neg (Y := Y) q.1 (-q.2)).1 this
        simpa using h2
      · have hneg : ContinuousOn (fun q : M × ℝ => curveMax (-Y) q.1 (-q.2))
            (N ×ˢ Ioo (t₀ - ε) ε) :=
          hcont.comp (continuousOn_fst.prodMk continuousOn_snd.neg) (fun q hq =>
            ⟨hq.1, show -q.2 ∈ Ioo (-ε) (-t₀ + ε) from
              ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩⟩)
        refine hneg.congr fun q hq => ?_
        have := hdom q.1 hq.1 (show -q.2 ∈ Ioo (-ε) (-t₀ + ε) from
          ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩)
        have h2 := (domMax_neg (Y := Y) q.1 (-q.2)).1 this
        have h3 : q.2 ∈ domMax Y q.1 := by simpa using h2
        exact (curveMax_neg hY q.1 h3).symm
  refine ⟨?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hUo, hpU, hUsub, -⟩ := loc p hp
    exact Filter.mem_of_superset (hUo.mem_nhds hpU) hUsub
  · intro p hp
    obtain ⟨U, hUo, hpU, -, hUc⟩ := loc p hp
    exact (hUc.continuousAt (hUo.mem_nhds hpU)).continuousWithinAt

/-- **Shifting an integral curve to start at a later point.** -/
theorem IsIC.shift {y : M} {a b : ℝ} {c : ℝ → M} (h : IsIC Y y a b c) {t : ℝ} (ht : t ∈ Ioo a b) :
    IsIC Y (c t) (a - t) (b - t) (fun u => c (u + t)) := by
  refine ⟨by linarith [ht.1], by linarith [ht.2], by simp, ?_⟩
  have := h.2.2.2.comp_add t
  refine this.mono fun u hu => ?_
  exact (show u + t ∈ Ioo a b from ⟨by linarith [hu.1], by linarith [hu.2]⟩)

/-- **A maximal integral curve passes back through its starting point.** -/
theorem curveMax_shift (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y : M} {s : ℝ}
    (hs : s ∈ domMax Y y) :
    -s ∈ domMax Y (curveMax Y y s) ∧ curveMax Y (curveMax Y y s) (-s) = y := by
  obtain ⟨a, b, c, hIC, hsab⟩ := hs
  have hsh := hIC.shift hsab
  rw [← curveMax_eq hY hIC hsab] at hsh
  have hmem : -s ∈ Ioo (a - s) (b - s) := ⟨by linarith [hIC.1], by linarith [hIC.2.1]⟩
  refine ⟨⟨_, _, _, hsh, hmem⟩, ?_⟩
  rw [curveMax_eq hY hsh hmem]
  simpa using hIC.2.2.1

end Causal

end Lightlike
