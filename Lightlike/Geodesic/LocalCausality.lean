import Lightlike.Geodesic.TimeBall
import Lightlike.Geodesic.ConeTrap

/-!
# Local causality in a time ball (Chruściel, Proposition 2.4.5)

In a time ball (`IsTimeBall`: a normal chart `φ` at `p` with a timelike gradient `-N` of the time
function `x⁰ = -g_p(e, φ⁻¹ ·)`), a future causal curve from `p` stays in `σ_p ≤ 0`, `x⁰ ≥ 0`, where
`σ_p = g_p(v, v)` in normal coordinates `v` (`IsTimeBall.causal_cone`). The method (no perturbed
metrics): along the curve `f = σ_p` and `h = x⁰` satisfy `f' h ≤ f h'` where `f > 0` (the Gauss
lemma and the cone inequality `IsLorentzianForm.two_mul_le_of_spacelike`) and `f' ≤ 0` where
`f ≤ 0`, and `f ≤ C h²` by a uniform cone estimate; `nonpos_of_cone_inequality` concludes.

## Main results

* `exists_uniform_cone_estimate`, `norm_sub_le_of_ae_cone`: a cone estimate, uniform on a compact
  set, and its integral along a Lipschitz curve.
* `IsTimeBall.exists_cone_estimate`: `‖w‖ ≤ C x⁰(w)` for causal `Dφ(u) w`, `u` in a compact set.
* `exists_isTimeBall`: time balls exist at every point, for every timelike `e`.
* `IsTimeBall.causal_cone`: the `J⁺` line of (2.4.7), "⇒", in normal coordinates.

Source read (pdftotext): P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1, section 2.4,
Proposition 2.4.5 and (2.4.6)–(2.4.7), p. 20; Lemma 2.4.8, p. 21; Lemma 2.4.9, p. 22. See
`docs/notes/local-causality-plan.md`.
-/

open Set Metric Filter Topology Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- **A uniform cone estimate.** Let `Q u w` be continuous in `(u, w)` on `K × ℝⁿ`, `K` compact, and
homogeneous of degree two in `w`, and let `ℓ` be a linear functional which is positive on every nonzero
`w` with `Q u w ≤ 0` and `ℓ w ≥ 0`, for every `u ∈ K`. Then there is `C` with `‖w‖ ≤ C ℓ(w)` for all
such `w` and `u`. -/
theorem exists_uniform_cone_estimate {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {Q : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hQc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => Q q.1 q.2) (K ×ˢ univ))
    (hhom : ∀ u ∈ K, ∀ c : ℝ, 0 < c → ∀ w, Q u (c • w) = c ^ 2 * Q u w)
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ) (hpos : ∀ u ∈ K, ∀ w : Fin n → ℝ, w ≠ 0 → Q u w ≤ 0 → 0 ≤ ℓ w → 0 < ℓ w) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ K, ∀ w : Fin n → ℝ, Q u w ≤ 0 → 0 ≤ ℓ w → ‖w‖ ≤ C * ℓ w := by
  set Q' : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => Q q.1 q.2 with hQ
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (K ×ˢ sphere (0 : Fin n → ℝ) 1) ∩ (Q' ⁻¹' Iic 0 ∩ (fun p => ℓ p.2) ⁻¹' Ici 0) with hS
  have hcomp0 : IsCompact (K ×ˢ sphere (0 : Fin n → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  have hcl : IsClosed S := by
    have hQc' : ContinuousOn Q' (K ×ˢ sphere (0 : Fin n → ℝ) 1) :=
      hQc.mono (prod_mono subset_rfl (subset_univ _))
    have h1 := hQc'.preimage_isClosed_of_isClosed hcomp0.isClosed (isClosed_Iic (a := (0 : ℝ)))
    have h2 : IsClosed ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => ℓ p.2) ⁻¹' Ici 0) :=
      isClosed_Ici.preimage (ℓ.continuous.comp continuous_snd)
    have : S = ((K ×ˢ sphere (0 : Fin n → ℝ) 1) ∩ Q' ⁻¹' Iic 0) ∩
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ℓ p.2) ⁻¹' Ici 0 := by
      rw [hS, inter_assoc]
    rw [this]
    exact h1.inter h2
  have hcomp : IsCompact S := hcomp0.of_isClosed_subset hcl inter_subset_left
  by_cases hne : S.Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := hcomp.exists_isMinOn hne (ℓ.continuous.comp continuous_snd).continuousOn
    have hp0' := hp0
    obtain ⟨⟨hu0, hw0⟩, hq0, hl0⟩ := hp0'
    have hw0ne : p0.2 ≠ 0 := by
      intro h; rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw0; exact zero_ne_one hw0
    have hm : 0 < ℓ p0.2 := hpos p0.1 hu0 p0.2 hw0ne hq0 hl0
    refine ⟨1 / ℓ p0.2, by positivity, fun u hu w hw hlw => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set w1 : Fin n → ℝ := ‖w‖⁻¹ • w with hw1
    have hmem : (u, w1) ∈ S := by
      refine ⟨⟨hu, ?_⟩, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, hw1, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
      · show Q u w1 ≤ 0
        rw [hw1, hhom u hu _ (inv_pos.2 hwn)]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hw
      · show 0 ≤ ℓ w1
        rw [hw1, map_smul, smul_eq_mul]
        positivity
    have h1 : ℓ p0.2 ≤ ℓ w1 := hmin hmem
    rw [hw1, map_smul, smul_eq_mul] at h1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
    calc ‖w‖ * ℓ p0.2 ≤ ‖w‖ * (‖w‖⁻¹ * ℓ w) := mul_le_mul_of_nonneg_left h1 hwn.le
      _ = ℓ w := by field_simp
  · refine ⟨1, one_pos, fun u hu w hw hlw => ?_⟩
    by_contra hcon
    have hw0 : w ≠ 0 := by
      intro h; apply hcon; simp [h]
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    apply hne
    refine ⟨(u, ‖w‖⁻¹ • w), ⟨hu, ?_⟩, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
    · show Q u (‖w‖⁻¹ • w) ≤ 0
      rw [hhom u hu _ (inv_pos.2 hwn)]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hw
    · show 0 ≤ ℓ (‖w‖⁻¹ • w)
      rw [map_smul, smul_eq_mul]
      positivity

/-- **Integrating a cone estimate along a Lipschitz curve**: if almost everywhere `‖F'‖ ≤ C ℓ(F')`,
then `‖F b - F a‖ ≤ C (ℓ (F b) - ℓ (F a))`. -/
theorem norm_sub_le_of_ae_cone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E}
    {a b : ℝ} {K : NNReal} (hab : a ≤ b) (hF : LipschitzOnWith K F (Icc a b)) (ℓ : E →L[ℝ] ℝ) {C : ℝ}
    (hd : ∀ᵐ t, t ∈ Ioo a b → ∃ F' : E, HasDerivAt F F' t ∧ ‖F'‖ ≤ C * ℓ F') :
    ‖F b - F a‖ ≤ C * (ℓ (F b) - ℓ (F a)) := by
  obtain ⟨φ, hφ1, hφx⟩ := exists_dual_vector'' ℝ (F b - F a)
  have h := Lightlike.Causal.sub_le_sub_of_ae_deriv_le (f := fun t => φ (F t))
    (h := fun t => (C • ℓ) (F t)) hab (φ.lipschitzWith.comp_lipschitzOnWith hF)
    ((C • ℓ).lipschitzWith.comp_lipschitzOnWith hF) (by
      filter_upwards [hd] with t ht hmem
      obtain ⟨F', hF', hle⟩ := ht hmem
      have h1 : HasDerivAt (fun t => φ (F t)) (φ F') t := φ.hasFDerivAt.comp_hasDerivAt t hF'
      have h2 : HasDerivAt (fun t => (C • ℓ) (F t)) ((C • ℓ) F') t :=
        (C • ℓ).hasFDerivAt.comp_hasDerivAt t hF'
      refine ⟨h1.differentiableAt, h2.differentiableAt, ?_⟩
      rw [h1.deriv, h2.deriv]
      have : φ F' ≤ ‖F'‖ := (le_abs_self _).trans ((φ.le_opNorm F').trans (by nlinarith [norm_nonneg F']))
      simpa using this.trans hle)
  rw [map_sub] at hφx
  replace hφx : φ (F b) - φ (F a) = ‖F b - F a‖ := by exact_mod_cast hφx
  simp only [_root_.smul_apply, smul_eq_mul] at h
  rw [mul_sub]
  linarith

/-- The derivative of the inverse of a normal chart inverts the derivative of the chart. -/
lemma IsNormalChart.fderiv_symm_apply {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    {p : Fin n → ℝ} {ρ : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
    (h : IsNormalChart g U p ρ φ) {v : Fin n → ℝ} (hv : v ∈ ball (0 : Fin n → ℝ) ρ) (w : Fin n → ℝ) :
    fderiv ℝ φ.symm (φ v) (fderiv ℝ φ v w) = w := by
  have hsrc : v ∈ φ.source := by rw [h.source_eq]; exact hv
  have hφ : HasFDerivAt φ (fderiv ℝ φ v) v :=
    ((h.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)).differentiableAt (by simp)).hasFDerivAt
  have hψ : HasFDerivAt φ.symm (fderiv ℝ φ.symm (φ v)) (φ v) :=
    ((h.contDiffOn_symm.contDiffAt (φ.open_target.mem_nhds (φ.map_source hsrc))).differentiableAt
      (by simp)).hasFDerivAt
  have c1 : HasFDerivAt (φ.symm ∘ φ) ((fderiv ℝ φ.symm (φ v)).comp (fderiv ℝ φ v)) v := hψ.comp v hφ
  have hev : (φ.symm ∘ φ) =ᶠ[𝓝 v] id := φ.eventually_left_inverse hsrc
  have h3 := (hasFDerivAt_id (𝕜 := ℝ) v).unique (c1.congr_of_eventuallyEq hev.symm)
  have h4 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L w) h3
  simpa using h4.symm

/-- **Time balls exist** (the set `O` of Chruściel's Proposition 2.4.5): for `p ∈ U` and a timelike
`e` at `p` there are a normal chart `φ` at `p`, a radius `r > 0` and a field `N`, the gradient of
`-x⁰`, with `IsTimeBall g U p ρ φ e r N`. Here `N v = g(φ v)⁻¹ (Dφ(v)⁻¹)ᵀ g_p e`, `N 0 = e`, and `N`
stays timelike near `0` by continuity. -/
theorem exists_isTimeBall {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) {p e : Fin n → ℝ} (hp : p ∈ U) (he : pairing g p e e < 0) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)) (r : ℝ)
      (N : (Fin n → ℝ) → Fin n → ℝ), IsTimeBall g U p ρ φ e r N := by
  obtain ⟨ρ, φ, hφ⟩ := exists_isNormalChart hg hp
  have hρ := hφ.pos
  have hsrc : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, v ∈ φ.source := fun v hv => by
    rw [hφ.source_eq]; exact hv
  have hmapU : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v ∈ U := fun v hv =>
    hφ.target_subset (φ.map_source (hsrc v hv))
  set L : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun v =>
    LinearMap.toMatrix' ((fderiv ℝ φ.symm (φ v) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
      (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hLdef
  set N : (Fin n → ℝ) → Fin n → ℝ := fun v => (g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e)) with hNdef
  -- `N v` represents `w ↦ g_p (e, w)` through the chart
  have hdual : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∀ w,
      pairing g (φ v) (N v) (fderiv ℝ φ v w) = pairing g p e w := by
    intro v hv w
    have hy := hmapU v hv
    have hLw : L v *ᵥ (fderiv ℝ φ v w) = w := by
      simp only [hLdef]
      rw [LinearMap.toMatrix'_mulVec]
      exact hφ.fderiv_symm_apply hv w
    rw [pairing_eq_dotProduct, pairing_eq_dotProduct]
    calc ((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e))) ⬝ᵥ (g (φ v) *ᵥ fderiv ℝ φ v w)
        = (((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e))) ᵥ* g (φ v)) ⬝ᵥ fderiv ℝ φ v w :=
          dotProduct_mulVec _ _ _
      _ = (g (φ v) *ᵥ ((g (φ v))⁻¹ *ᵥ ((L v)ᵀ *ᵥ (g p *ᵥ e)))) ⬝ᵥ fderiv ℝ φ v w := by
          rw [← mulVec_transpose, hg.symm _ hy]
      _ = ((L v)ᵀ *ᵥ (g p *ᵥ e)) ⬝ᵥ fderiv ℝ φ v w := by
          rw [mulVec_mulVec, mul_nonsing_inv _ (hg.isUnit_det _ hy), one_mulVec]
      _ = ((g p *ᵥ e) ᵥ* L v) ⬝ᵥ fderiv ℝ φ v w := by rw [mulVec_transpose]
      _ = (g p *ᵥ e) ⬝ᵥ (L v *ᵥ fderiv ℝ φ v w) := (dotProduct_mulVec _ _ _).symm
      _ = (g p *ᵥ e) ⬝ᵥ w := by rw [hLw]
      _ = (e ᵥ* g p) ⬝ᵥ w := by rw [← mulVec_transpose, hg.symm _ hp]
      _ = e ⬝ᵥ (g p *ᵥ w) := (dotProduct_mulVec _ _ _).symm
  -- `N 0 = e`
  have hD0 : fderiv ℝ φ.symm (φ 0) = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    ext1 w
    have := hφ.fderiv_symm_apply (mem_ball_self hρ) w
    rwa [hφ.hasFDerivAt_zero.fderiv, ContinuousLinearMap.id_apply] at this
  have hN0 : N 0 = e := by
    have hL0 : L 0 = 1 := by
      simp only [hLdef, hD0, ContinuousLinearMap.coe_id]
      exact LinearMap.toMatrix'_id
    simp only [hNdef]
    rw [hL0, transpose_one, one_mulVec, hφ.map_zero, mulVec_mulVec,
      nonsing_inv_mul _ (hg.isUnit_det _ hp), one_mulVec]
  -- continuity of `N`
  have hφc : ContinuousOn φ (ball 0 ρ) := hφ.source_eq ▸ hφ.contDiffOn.continuousOn
  have hDc : ContinuousOn (fun v => fderiv ℝ φ.symm (φ v)) (ball 0 ρ) :=
    (hφ.contDiffOn_symm.continuousOn_fderiv_of_isOpen φ.open_target (by simp)).comp hφc
      (fun v hv => φ.map_source (hsrc v hv))
  have hLc : ContinuousOn L (ball 0 ρ) := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have h1 : ContinuousOn (fun v => fderiv ℝ φ.symm (φ v) (Pi.single j 1) i)
        (ball 0 ρ) := (continuous_apply i).comp_continuousOn (hDc.clm_apply continuousOn_const)
    refine h1.congr fun v _ => ?_
    simp only [hLdef]
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hGc : ContinuousOn (fun v => g (φ v)) (ball 0 ρ) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
      (hg.smooth i j).continuousOn.comp hφc fun v hv => hmapU v hv
  have hNc : ContinuousOn N (ball 0 ρ) := by
    have hG' := (continuousOn_iff_continuous_domRestrict).1 hGc
    have hL' := (continuousOn_iff_continuous_domRestrict).1 hLc
    rw [continuousOn_iff_continuous_domRestrict]
    have hdet : ∀ v : ball (0 : Fin n → ℝ) ρ, (g (φ v)).det ≠ 0 := fun v =>
      (hg.isUnit_det _ (hmapU v v.2)).ne_zero
    have hinv : Continuous fun v : ball (0 : Fin n → ℝ) ρ => (g (φ v))⁻¹ := by
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (hG'.matrix_det.inv₀ hdet).smul hG'.matrix_adjugate
    exact hinv.matrix_mulVec (hL'.matrix_transpose.matrix_mulVec continuous_const)
  -- `N` is timelike near `0`
  have hfc : ContinuousOn (fun v => pairing g (φ v) (N v) (N v)) (ball 0 ρ) := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hNc).mul
      (((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hGc)).mul
        ((continuous_apply j).comp_continuousOn hNc))
  have hf0 : ContinuousAt (fun v => pairing g (φ v) (N v) (N v)) 0 :=
    hfc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hlt : (fun v => pairing g (φ v) (N v) (N v)) 0 < 0 := by
    simp only [hN0, hφ.map_zero]; exact he
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hf0.eventually (gt_mem_nhds hlt))
  refine ⟨ρ, φ, min ε ρ, N, ⟨hφ, lt_min hε hρ, min_le_right _ _, he, ?_, ?_, ?_⟩⟩
  · exact fun v hv w => hdual v (ball_subset_ball (min_le_right _ _) hv) w
  · exact fun v hv => hball v (ball_subset_ball (min_le_left _ _) hv)
  · exact hNc.mono (ball_subset_ball (min_le_right _ _))

namespace IsTimeBall

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {p e : Fin n → ℝ} {ρ r : ℝ}
  {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}

/-- **A uniform cone estimate in a time ball.** On a compact subset `K` of the ball there is `C`
with `‖w‖ ≤ C x⁰(w)`, `x⁰(w) = -g_p(e, w)`, for every `w` such that `Dφ(u) w` is causal at `φ u`
and `x⁰(w) ≥ 0`. -/
theorem exists_cone_estimate (hL : IsLorentzianCoordMetric g U) (h : IsTimeBall g U p ρ φ e r N)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKr : K ⊆ ball 0 r) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ K, ∀ w : Fin n → ℝ,
      pairing g (φ u) (fderiv ℝ φ u w) (fderiv ℝ φ u w) ≤ 0 →
      0 ≤ -pairing g p e w → ‖w‖ ≤ C * (-pairing g p e w) := by
  have hball : ∀ u ∈ K, u ∈ ball (0 : Fin n → ℝ) ρ := fun u hu => h.mem_ball (hKr hu)
  have hcd : ContDiffOn ℝ ∞ φ (ball 0 ρ) := h.chart.source_eq ▸ h.chart.contDiffOn
  have hfd : ContinuousOn (fun u => fderiv ℝ φ u) (ball (0 : Fin n → ℝ) ρ) :=
    hcd.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have hmapU : ∀ u ∈ ball (0 : Fin n → ℝ) ρ, φ u ∈ U := fun u hu =>
    h.chart.target_subset (φ.map_source (by rw [h.chart.source_eq]; exact hu))
  have hD : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => fderiv ℝ φ q.1 q.2) (K ×ˢ univ) :=
    (hfd.comp continuousOn_fst fun q hq => hball q.1 hq.1).clm_apply continuousOn_snd
  have hG : ∀ i j, ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => g (φ q.1) i j) (K ×ˢ univ) :=
    fun i j => ((hL.1.smooth i j).continuousOn.comp hcd.continuousOn fun u hu => hmapU u hu).comp
      continuousOn_fst fun q hq => hball q.1 hq.1
  have hQc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      pairing g (φ q.1) (fderiv ℝ φ q.1 q.2) (fderiv ℝ φ q.1 q.2)) (K ×ˢ univ) := by
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hD).mul
      ((hG i j).mul ((continuous_apply j).comp_continuousOn hD))
  have hhom : ∀ u ∈ K, ∀ c : ℝ, 0 < c → ∀ w,
      pairing g (φ u) (fderiv ℝ φ u (c • w)) (fderiv ℝ φ u (c • w)) =
        c ^ 2 * pairing g (φ u) (fderiv ℝ φ u w) (fderiv ℝ φ u w) := by
    intro u _ c _ w
    simp only [map_smul, pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  set ℓ : (Fin n → ℝ) →L[ℝ] ℝ := -(matForm (g p) e) with hℓdef
  have hℓ : ∀ w, ℓ w = -pairing g p e w := fun w => by
    rw [hℓdef, _root_.neg_apply, pairing_eq_matForm]
  have hpos : ∀ u ∈ K, ∀ w : Fin n → ℝ, w ≠ 0 →
      pairing g (φ u) (fderiv ℝ φ u w) (fderiv ℝ φ u w) ≤ 0 → 0 ≤ ℓ w → 0 < ℓ w := by
    intro u hu w hw hQ hl
    rw [hℓ] at hl ⊢
    refine lt_of_le_of_ne hl fun h0 => hw ?_
    have hur := hKr hu
    have hy := h.map_mem hur
    have hdual := h.dual u hur w
    have hX : fderiv ℝ φ u w = 0 := by
      refine (isLorentzianForm_matForm hL hy).eq_zero_of_orthogonal_timelike (X := N u) ?_ ?_ ?_
      · rw [← pairing_eq_matForm]; exact h.timelike u hur
      · rw [← pairing_eq_matForm, pairing_comm hL.1 hy, hdual]; linarith
      · rw [← pairing_eq_matForm]; exact hQ
    obtain ⟨D, -, -, hDφ⟩ := h.exists_fderiv_symm hur
    rw [← hDφ w, hX, map_zero]
  obtain ⟨C, hC, hest⟩ := exists_uniform_cone_estimate hK hQc hhom ℓ hpos
  exact ⟨C, hC, fun u hu w hQ hl => by rw [← hℓ] at hl ⊢; exact hest u hu w hQ hl⟩

/-- **Local causality in a time ball, the causal future** (Chruściel, Proposition 2.4.5, the `J⁺`
line of (2.4.7), "⇒"). Let `v` be a Lipschitz curve in the ball of a time ball, in normal
coordinates, from `v a = 0` (the point `p`), such that `φ ∘ v` has future causal velocity:
`Dφ(v) v'` is causal with `g(N, Dφ(v) v') < 0` almost everywhere. Then the end point satisfies
`σ_p = g_p(v, v) ≤ 0` and `x⁰ = -g_p(e, v) ≥ 0`. -/
theorem causal_cone (hL : IsLorentzianCoordMetric g U) (h : IsTimeBall g U p ρ φ e r N)
    {v : ℝ → Fin n → ℝ} {a b : ℝ} {K : NNReal} (hab : a ≤ b) (hv : LipschitzOnWith K v (Icc a b))
    (hmem : ∀ t ∈ Icc a b, v t ∈ ball (0 : Fin n → ℝ) r) (ha : v a = 0)
    (hd : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧
      pairing g (φ (v t)) (fderiv ℝ φ (v t) v') (fderiv ℝ φ (v t) v') ≤ 0 ∧
      pairing g (φ (v t)) (N (v t)) (fderiv ℝ φ (v t) v') < 0) :
    pairing g p (v b) (v b) ≤ 0 ∧ 0 ≤ -pairing g p e (v b) := by
  rcases hab.eq_or_lt with rfl | hab'
  · rw [ha]; simp [pairing]
  have hg := hL.1
  have hp : p ∈ U := by
    have := h.map_mem (v := 0) (mem_ball_self h.pos); rwa [h.chart.map_zero] at this
  set B := matForm (g p) with hB
  have hpB : ∀ x y, pairing g p x y = B x y := fun x y => pairing_eq_matForm g p x y
  have hBsymm : ∀ x y, B x y = B y x := fun x y => by rw [← hpB, ← hpB, pairing_comm hg hp]
  set ℓ : (Fin n → ℝ) →L[ℝ] ℝ := -(B e) with hℓdef
  have hℓ : ∀ w, ℓ w = -pairing g p e w := fun w => by
    rw [hℓdef, _root_.neg_apply, hpB]
  -- the cone estimate on the image of the curve
  have hKc : IsCompact (v '' Icc a b) := isCompact_Icc.image_of_continuousOn hv.continuousOn
  obtain ⟨C₁, hC₁, hest⟩ := h.exists_cone_estimate hL hKc (by rintro _ ⟨t, ht, rfl⟩; exact hmem t ht)
  have hvel : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧ 0 < ℓ v' ∧
      ‖v'‖ ≤ C₁ * ℓ v' ∧ pairing g (φ (v t)) (fderiv ℝ φ (v t) v') (fderiv ℝ φ (v t) v') ≤ 0 ∧
      pairing g (φ (v t)) (N (v t)) (fderiv ℝ φ (v t) v') < 0 := by
    filter_upwards [hd] with t ht hmt
    obtain ⟨v', hv', hc, hf⟩ := ht hmt
    have htr := hmem t (Ioo_subset_Icc_self hmt)
    have hl : 0 < ℓ v' := by rw [hℓ, ← h.dual _ htr v']; linarith
    refine ⟨v', hv', hl, ?_, hc, hf⟩
    rw [hℓ] at hl ⊢
    exact hest _ ⟨t, Ioo_subset_Icc_self hmt, rfl⟩ v' hc hl.le
  -- `x⁰` increases strictly from `0`
  have hpos : ∀ t ∈ Ioc a b, 0 < ℓ (v t) := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have := (Lightlike.Causal.functional_increasing_of_ae_pos ht.1 (hv.mono hsub) ℓ (by
      filter_upwards [hvel] with s hs hsm
      obtain ⟨v', hv', hl, -⟩ := hs ⟨hsm.1, lt_of_lt_of_le hsm.2 ht.2⟩
      rw [hv'.deriv]; exact hl)).2
    rwa [ha, map_zero] at this
  -- the cone bound `σ ≤ C (x⁰)²`
  have hnorm : ∀ t ∈ Icc a b, ‖v t‖ ≤ C₁ * ℓ (v t) := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have := norm_sub_le_of_ae_cone ht.1 (hv.mono hsub) ℓ (by
      filter_upwards [hvel] with s hs hsm
      obtain ⟨v', hv', -, hle, -⟩ := hs ⟨hsm.1, lt_of_lt_of_le hsm.2 ht.2⟩
      exact ⟨v', hv', hle⟩)
    rwa [ha, sub_zero, map_zero, sub_zero] at this
  have hfC : ∀ t ∈ Icc a b, B (v t) (v t) ≤ (‖B‖ * C₁ ^ 2) * ℓ (v t) ^ 2 := by
    intro t ht
    have h1 := B.le_opNorm₂ (v t) (v t)
    rw [Real.norm_eq_abs] at h1
    have h3 : ‖v t‖ ^ 2 ≤ (C₁ * ℓ (v t)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm t ht) 2
    calc B (v t) (v t) ≤ ‖B‖ * ‖v t‖ ^ 2 := by nlinarith [le_abs_self (B (v t) (v t)), norm_nonneg B]
      _ ≤ ‖B‖ * (C₁ * ℓ (v t)) ^ 2 := mul_le_mul_of_nonneg_left h3 (norm_nonneg B)
      _ = (‖B‖ * C₁ ^ 2) * ℓ (v t) ^ 2 := by ring
  -- Lipschitz bounds
  have hbound : ∀ t ∈ Icc a b, ‖v t‖ ≤ r := fun t ht => (mem_ball_zero_iff.1 (hmem t ht)).le
  have hfL : LipschitzOnWith (2 * ‖B‖₊ * ⟨r, h.pos.le⟩ * K) (fun t => B (v t) (v t)) (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    have hst : ‖v s - v t‖ ≤ (K : ℝ) * Dist.dist s t := by
      rw [← dist_eq_norm]; exact hv.dist_le_mul s hs t ht
    have hsplit : B (v s) (v s) - B (v t) (v t) = B (v s - v t) (v s) + B (v t) (v s - v t) := by
      simp only [map_sub, _root_.sub_apply]; ring
    rw [Real.dist_eq, hsplit]
    have e1 := B.le_opNorm₂ (v s - v t) (v s)
    have e2 := B.le_opNorm₂ (v t) (v s - v t)
    rw [Real.norm_eq_abs] at e1 e2
    have hr1 := hbound s hs
    have hr2 := hbound t ht
    have hB0 := norm_nonneg B
    have hd0 := norm_nonneg (v s - v t)
    push_cast
    calc |B (v s - v t) (v s) + B (v t) (v s - v t)|
        ≤ |B (v s - v t) (v s)| + |B (v t) (v s - v t)| := abs_add_le _ _
      _ ≤ ‖B‖ * ‖v s - v t‖ * ‖v s‖ + ‖B‖ * ‖v t‖ * ‖v s - v t‖ := add_le_add e1 e2
      _ ≤ ‖B‖ * ‖v s - v t‖ * r + ‖B‖ * r * ‖v s - v t‖ := by gcongr
      _ = 2 * ‖B‖ * r * ‖v s - v t‖ := by ring
      _ ≤ 2 * ‖B‖ * r * ((K : ℝ) * Dist.dist s t) := by
          have : 0 ≤ 2 * ‖B‖ * r := by have := h.pos; positivity
          exact mul_le_mul_of_nonneg_left hst this
      _ = 2 * ‖B‖ * r * (K : ℝ) * Dist.dist s t := by ring
  have hx0L : LipschitzOnWith (‖ℓ‖₊ * K) (fun t => ℓ (v t)) (Icc a b) :=
    ℓ.lipschitzWith.comp_lipschitzOnWith hv
  -- the differential inequalities
  have hderiv : ∀ᵐ t, t ∈ Ioo a b → DifferentiableAt ℝ (fun t => B (v t) (v t)) t ∧
      DifferentiableAt ℝ (fun t => ℓ (v t)) t ∧ 0 ≤ deriv (fun t => ℓ (v t)) t ∧
      (0 < B (v t) (v t) → deriv (fun t => B (v t) (v t)) t * ℓ (v t) ≤
        B (v t) (v t) * deriv (fun t => ℓ (v t)) t) ∧
      (B (v t) (v t) ≤ 0 → deriv (fun t => B (v t) (v t)) t ≤ 0) := by
    filter_upwards [hvel] with t ht hmt
    obtain ⟨v', hv', hl, -, hc, hfut⟩ := ht hmt
    have htr := hmem t (Ioo_subset_Icc_self hmt)
    have hx0' : HasDerivAt (fun t => ℓ (v t)) (ℓ v') t := ℓ.hasFDerivAt.comp_hasDerivAt t hv'
    have hc' : HasDerivAt (fun s => B (v s)) (B v') t := B.hasFDerivAt.comp_hasDerivAt t hv'
    have hf' : HasDerivAt (fun t => B (v t) (v t)) (B v' (v t) + B (v t) v') t := hc'.clm_apply hv'
    have hf'' : deriv (fun t => B (v t) (v t)) t = 2 * B (v t) v' := by
      rw [hf'.deriv, hBsymm v' (v t)]; ring
    have hy : φ (v t) ∈ U := h.map_mem htr
    have hLf := isLorentzianForm_matForm hL hy
    have hq : ∀ x z, pairing g (φ (v t)) x z = matForm (g (φ (v t))) x z := fun x z =>
      pairing_eq_matForm g _ x z
    have gPX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (fderiv ℝ φ (v t) v') = B (v t) v' := by
      rw [← hq, ← hpB]; exact IsNormalChart.gauss hg h.chart (h.mem_ball htr) v'
    have gPP : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (fderiv ℝ φ (v t) (v t)) =
        B (v t) (v t) := by
      rw [← hq, ← hpB]; exact IsNormalChart.gauss hg h.chart (h.mem_ball htr) (v t)
    have gNP : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (N (v t)) = -ℓ (v t) := by
      rw [← hq, pairing_comm hg hy, h.dual _ htr, hℓ, neg_neg]
    have gNX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) v') (N (v t)) = -ℓ v' := by
      rw [← hq, pairing_comm hg hy, h.dual _ htr, hℓ, neg_neg]
    have hNN : matForm (g (φ (v t))) (N (v t)) (N (v t)) < 0 := by
      rw [← hq]; exact h.timelike _ htr
    have hXX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) v') (fderiv ℝ φ (v t) v') ≤ 0 := by
      rw [← hq]; exact hc
    have hx0pos : 0 < ℓ (v t) := hpos t ⟨hmt.1, hmt.2.le⟩
    refine ⟨hf'.differentiableAt, hx0'.differentiableAt, by rw [hx0'.deriv]; exact hl.le,
      fun hft => ?_, fun hft => ?_⟩
    · have key := hLf.two_mul_le_of_spacelike hNN hXX (by rw [gNX]; linarith) (by rw [gNP]; linarith)
        (by rw [gPP]; exact hft.le)
      rw [gNP, gPX, gPP, gNX, neg_neg, neg_neg] at key
      rw [hf'', hx0'.deriv]
      nlinarith [key]
    · have key := hLf.nonpos_of_futureCausal hNN (by rw [gPP]; exact hft) hXX (by rw [gNP]; linarith)
        (by rw [gNX]; linarith)
      rw [gPX] at key
      rw [hf'']
      linarith
  have hfb := nonpos_of_cone_inequality (f := fun t => B (v t) (v t)) (h := fun t => ℓ (v t)) hab'
    hfL hx0L (by simp only [ha, map_zero]) hpos (by positivity) hfC hderiv
  refine ⟨by rw [hpB]; exact hfb, ?_⟩
  rw [← hℓ]
  exact (hpos b ⟨hab', le_rfl⟩).le

end IsTimeBall

end Lightlike.Geodesic
