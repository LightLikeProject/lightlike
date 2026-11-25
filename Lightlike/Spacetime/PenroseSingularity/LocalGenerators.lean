import Lightlike.Spacetime.PenroseSingularity.Orthogonality
import Lightlike.Geodesic.NullRigidity
import Lightlike.Geodesic.UniformTimeBall
import Lightlike.Spacetime.CausalLadder.ChartVelocity
import Lightlike.Spacetime.CausalLadder.ChartLipschitz

/-!
# Local structure of the generators of `∂J⁺(S)` (G1-012)

A future causal curve `β` that stays in the source of the chart at `x` has, in that chart, a
Lipschitz expression `u = extChartAt x ∘ β` whose derivative is almost everywhere a nonzero causal
vector of the coordinate metric, pointing to the future of the time orientation field in
coordinates (`chart_curve_data`). This is the input of the time-ball estimates of
`Lightlike.Geodesic.IsTimeBall.causal_cone` and `IsTimeBall.null_rigidity`.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **Chart data of a future causal curve.** A future causal curve on `[a, b]` inside the source of
the chart at `x` has a Lipschitz chart expression `u = extChartAt x ∘ β`, with, almost everywhere,
`u'` nonzero, `g_c(u)(u', u') ≤ 0` and `g_c(u)(u', X_c(u)) < 0`, where `g_c` is the coordinate metric
and `X_c = timeCoord T x` the time orientation field in coordinates. -/
theorem chart_curve_data (T : Causal.TimeOrientation g) (x : M) {β : ℝ → M} {a b : ℝ}
    (hβ : Causal.IsFutureCausalCurve T β (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, β t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) :
    ∃ K : NNReal, LipschitzOnWith K (extChartAt 𝓘(ℝ, Fin n → ℝ) x ∘ β) (Icc a b) ∧
      ∀ᵐ t, t ∈ Ioo a b → ∃ u' : Fin n → ℝ,
        HasDerivAt (extChartAt 𝓘(ℝ, Fin n → ℝ) x ∘ β) u' t ∧ u' ≠ 0 ∧
        Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t)) u' u'
          ≤ 0 ∧
        Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t)) u'
          (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t))) < 0 := by
  obtain ⟨K, hK⟩ := Causal.exists_lipschitzOnWith_chart_comp hβ.lipschitz x hsrc
  refine ⟨K, hK, ?_⟩
  have hae := (ae_restrict_iff' measurableSet_Icc).1 hβ.ae_velocity
  filter_upwards [hae] with t ht hmt
  obtain ⟨hmd, hP⟩ := ht ⟨hmt.1.le, hmt.2.le⟩
  have hs := hsrc t ⟨hmt.1.le, hmt.2.le⟩
  have hder := Causal.hasDerivWithinAt_chart_comp (I := 𝓘(ℝ, Fin n → ℝ)) x hmd hs
  refine ⟨_, hder.hasDerivAt (Icc_mem_nhds hmt.1 hmt.2), ?_⟩
  set D := (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨β t, Causal.velocity 𝓘(ℝ, Fin n → ℝ) β (Icc a b) t⟩).2
    with hD
  have hvq := eq_symmL_of_tTriv x (β t) (mem_baseSet_of_mem_source x (β t) hs) _ hD.symm
  have hXq := timeOrientation_eq_symmL T x (β t) hs
  obtain ⟨hne, hle, hfut⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hne
    rw [hvq, h0, map_zero]
  · rw [hvq, metric_eq_bil_at g.toNondegMetric x (β t) hs] at hle
    rw [pairing_eq_bil]
    exact hle
  · rw [hvq, hXq, metric_eq_bil_at g.toNondegMetric x (β t) hs] at hfut
    rw [pairing_eq_bil]
    exact hfut


end Lightlike.Penrose

namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {m : ℕ}
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **A timelike vector with negative product with a future timelike vector is future directed**:
`B V V < 0`, `B N N < 0`, `B N X < 0` and `B V N < 0` give `B V X < 0`. -/
theorem IsLorentzianForm.neg_of_neg_pair (h : IsLorentzianForm m B) {X N W : V}
    (hX : B X X < 0) (hN : B N N < 0) (hNX : B N X < 0) (hW : B W W < 0) (hWN : B W N < 0) :
    B W X < 0 := by
  have hsymm := h.symm
  by_contra hcon
  push_neg at hcon
  rcases hcon.eq_or_lt with h0 | hpos
  · have := h.eq_zero_of_orthogonal_timelike (X := X) hX h0.symm hW.le
    rw [this] at hW
    simp at hW
  · have hnW : B (-W) (-W) < 0 := by simpa using hW
    have h1 : B (-W) X < 0 := by simpa using hpos
    have := h.neg_of_futureTimelike hX hnW hN h1 hNX
    have e : B (-W) N = -B W N := by simp
    linarith

/-- **A future causal nonzero vector has negative product with a future timelike vector**:
`B N N < 0`, `B N X < 0`, `B u u ≤ 0`, `B u X < 0`, `u ≠ 0` give `B u N < 0`. -/
theorem IsLorentzianForm.neg_of_causal_of_timelike (h : IsLorentzianForm m B) {X N u : V}
    (hX : B X X < 0) (hN : B N N < 0) (hNX : B N X < 0) (hu : B u u ≤ 0) (huX : B u X < 0)
    (hne : u ≠ 0) : B u N < 0 := by
  have hle := h.nonpos_of_futureCausal hX hu hN.le huX hNX
  by_contra hcon
  have h0 : B u N = 0 := le_antisymm hle (not_lt.1 hcon)
  exact hne (h.eq_zero_of_orthogonal_timelike (X := N) hN h0 hu)

/-- **A nonzero causal vector with negative product with a future timelike vector is future
directed**: `B N N < 0`, `B N X < 0`, `B u u ≤ 0`, `u ≠ 0`, `B u N < 0` give `B u X < 0`. -/
theorem IsLorentzianForm.neg_of_neg_pair_causal (h : IsLorentzianForm m B) {X N u : V}
    (hX : B X X < 0) (hN : B N N < 0) (hNX : B N X < 0) (hu : B u u ≤ 0) (hne : u ≠ 0)
    (huN : B u N < 0) : B u X < 0 := by
  have hsymm := h.symm
  by_contra hcon
  push_neg at hcon
  rcases hcon.eq_or_lt with h0 | hpos
  · exact hne (h.eq_zero_of_orthogonal_timelike (X := X) hX h0.symm hu)
  · have hnu : B (-u) (-u) ≤ 0 := by simpa using hu
    have h1 : B (-u) X < 0 := by simpa using hpos
    have := h.nonpos_of_futureCausal hX hnu hN.le h1 hNX
    have e : B (-u) N = -B u N := by simp
    linarith

end Lightlike

open Metric

namespace Lightlike.Geodesic

/-- The composition of a `C¹` map on an open set with a Lipschitz curve in it is Lipschitz on a
compact interval. -/
theorem exists_lipschitzOnWith_comp_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {T : Set E}
    (hT : IsOpen T) (hf : ContDiffOn ℝ 1 f T) {u : ℝ → E} {a b : ℝ} {K : NNReal}
    (hu : LipschitzOnWith K u (Icc a b)) (hmaps : ∀ t ∈ Icc a b, u t ∈ T) :
    ∃ K' : NNReal, LipschitzOnWith K' (f ∘ u) (Icc a b) := by
  have hloc : LocallyLipschitzOn (Icc a b) (f ∘ u) := by
    intro t ht
    obtain ⟨K1, W, hW, hlip⟩ := ((hf.contDiffAt (hT.mem_nhds (hmaps t ht)))).exists_lipschitzOnWith
    have hV : u ⁻¹' W ∈ 𝓝[Icc a b] t :=
      (hu.continuousOn.continuousWithinAt ht).preimage_mem_nhdsWithin hW
    refine ⟨K1 * K, u ⁻¹' W ∩ Icc a b, inter_mem hV self_mem_nhdsWithin, ?_⟩
    exact hlip.comp (hu.mono inter_subset_right) (fun s hs => hs.1)
  exact hloc.exists_lipschitzOnWith_of_compact isCompact_Icc

end Lightlike.Geodesic

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **A time ball whose gradient field is future directed.** For a coordinate metric on `U`, a
continuous timelike vector field `X` on `U` and `p ∈ U`, there is a time ball at `p` with
`e = X p` whose field `N` is timelike and satisfies `g(N, X) < 0` on the ball: `N` and `X` lie in the
same half of the timelike cone. -/
theorem exists_future_timeBall (hg : Lightlike.IsCoordMetric g U) {X : (Fin n → ℝ) → Fin n → ℝ}
    (hX : ContinuousOn X U) (hXt : ∀ y ∈ U, pairing g y (X y) (X y) < 0) {p : Fin n → ℝ}
    (hp : p ∈ U) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)) (r : ℝ)
      (N : (Fin n → ℝ) → Fin n → ℝ), IsTimeBall g U p ρ φ (X p) r N ∧
      ∀ v ∈ ball (0 : Fin n → ℝ) r, pairing g (φ v) (N v) (X (φ v)) < 0 := by
  obtain ⟨ρ, φ, hφ⟩ := exists_isNormalChart hg hp
  obtain ⟨hdual, hN0, hNc⟩ := timeField_props (e := X p) hg hφ hp
  have hρ := hφ.pos
  have hsrc : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, v ∈ φ.source := fun v hv => by
    rw [hφ.source_eq]; exact hv
  have hmapU : ∀ v ∈ ball (0 : Fin n → ℝ) ρ, φ v ∈ U := fun v hv =>
    hφ.target_subset (φ.map_source (hsrc v hv))
  have hφc : ContinuousOn φ (ball 0 ρ) := hφ.source_eq ▸ hφ.contDiffOn.continuousOn
  have hGc : ∀ i j, ContinuousOn (fun v => g (φ v) i j) (ball 0 ρ) := fun i j =>
    (hg.smooth i j).continuousOn.comp hφc fun v hv => hmapU v hv
  have hXφ : ContinuousOn (fun v => X (φ v)) (ball 0 ρ) :=
    hX.comp hφc fun v hv => hmapU v hv
  have hF : ∀ (A B : (Fin n → ℝ) → Fin n → ℝ), ContinuousOn A (ball 0 ρ) →
      ContinuousOn B (ball 0 ρ) →
      ContinuousOn (fun v => pairing g (φ v) (A v) (B v)) (ball 0 ρ) := by
    intro A B hA hB
    simp only [pairing]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((continuous_apply i).comp_continuousOn hA).mul
      ((hGc i j).mul ((continuous_apply j).comp_continuousOn hB))
  have hF1 := hF _ _ hNc hNc
  have hF2 := hF _ _ hNc hXφ
  have h0 : (0 : Fin n → ℝ) ∈ ball (0 : Fin n → ℝ) ρ := mem_ball_self hρ
  have hat1 : ContinuousAt (fun v => pairing g (φ v) (timeField g p (X p) φ v)
      (timeField g p (X p) φ v)) 0 := hF1.continuousAt (isOpen_ball.mem_nhds h0)
  have hat2 : ContinuousAt (fun v => pairing g (φ v) (timeField g p (X p) φ v) (X (φ v))) 0 :=
    hF2.continuousAt (isOpen_ball.mem_nhds h0)
  have hv1 : pairing g (φ 0) (timeField g p (X p) φ 0) (timeField g p (X p) φ 0) < 0 := by
    rw [hN0, hφ.map_zero]; exact hXt p hp
  have hv2 : pairing g (φ 0) (timeField g p (X p) φ 0) (X (φ 0)) < 0 := by
    rw [hN0, hφ.map_zero]; exact hXt p hp
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 (hat1.eventually (gt_mem_nhds hv1))
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.eventually_nhds_iff_ball.1 (hat2.eventually (gt_mem_nhds hv2))
  have hρle : min (min ε₁ ε₂) ρ ≤ ρ := min_le_right _ _
  have hsub : ball (0 : Fin n → ℝ) (min (min ε₁ ε₂) ρ) ⊆ ball 0 ρ := ball_subset_ball hρle
  have hsub1 : ball (0 : Fin n → ℝ) (min (min ε₁ ε₂) ρ) ⊆ ball 0 ε₁ :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hsub2 : ball (0 : Fin n → ℝ) (min (min ε₁ ε₂) ρ) ⊆ ball 0 ε₂ :=
    ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  refine ⟨ρ, φ, min (min ε₁ ε₂) ρ, timeField g p (X p) φ,
    ⟨hφ, lt_min (lt_min hε₁ hε₂) hρ, hρle, hXt p hp, fun v hv w => hdual v (hsub hv) w,
      fun v hv => hb₁ v (hsub1 hv), hNc.mono hsub⟩, fun v hv => hb₂ v (hsub2 hv)⟩

end Lightlike.Geodesic

namespace Lightlike.Penrose

open Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- The pairing of the radial velocity `Dφ(s w) w` with itself is `σ_p(w)` (for `s w` in the normal
ball). -/
theorem radial_pairing {gc : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric gc U) {p : Fin n → ℝ} {ρ : ℝ}
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}
    (h : Lightlike.Geodesic.IsNormalChart gc U p ρ φ) {w : Fin n → ℝ} {s : ℝ}
    (hsw : s • w ∈ ball (0 : Fin n → ℝ) ρ) :
    Lightlike.Geodesic.pairing gc (φ (s • w)) (fderiv ℝ φ (s • w) w) (fderiv ℝ φ (s • w) w) =
      Lightlike.Geodesic.pairing gc p w w := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [zero_smul]
    rw [h.hasFDerivAt_zero.fderiv, h.map_zero]
    rfl
  · have := h.gauss hg hsw (s • w)
    rw [map_smul, Lightlike.Geodesic.pairing_smul_left, Lightlike.Geodesic.pairing_smul_right,
      Lightlike.Geodesic.pairing_smul_left, Lightlike.Geodesic.pairing_smul_right] at this
    exact mul_left_cancel₀ hs0 (mul_left_cancel₀ hs0 this)

/-- The time orientation field in chart coordinates is timelike for the coordinate metric. -/
theorem timeCoord_timelike (T : Causal.TimeOrientation g) (x : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target) :
    Lightlike.Geodesic.pairing (g.coordMetric x) y (timeCoord T x y) (timeCoord T x y) < 0 := by
  set q := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y with hq
  have hqs : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_target hy
  have hyq : extChartAt 𝓘(ℝ, Fin n → ℝ) x q = y := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).right_inv hy
  have h1 := T.timelike q
  rw [timeOrientation_eq_symmL T x q hqs, metric_eq_bil_at g.toNondegMetric x q hqs, hyq] at h1
  rw [pairing_eq_bil]
  exact h1

/-- **A radial timelike segment in a future time ball is a timelike curve of `M`.** In the time
ball at `p` (chart coordinates of the chart at `x`), if `σ_p(w) < 0` and `x⁰(w) > 0`, then the point
`φ w` is in the chronological future of the centre. -/
theorem radial_mem_chronFuture (T : Causal.TimeOrientation g) (x : M) {p : Fin n → ℝ} {ρ r : ℝ}
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    (hTB : Lightlike.Geodesic.IsTimeBall (g.coordMetric x)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target p ρ φ (timeCoord T x p) r N)
    (hfutN : ∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0)
    {w : Fin n → ℝ} (hw : w ∈ ball (0 : Fin n → ℝ) r)
    (hσ : Lightlike.Geodesic.pairing (g.coordMetric x) p w w < 0)
    (hx0 : Lightlike.Geodesic.pairing (g.coordMetric x) p (timeCoord T x p) w < 0) :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (φ w) ∈
      Causal.chronFuture T ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm p) := by
  have hL := g.isLorentzianCoordMetric_coordMetric x
  have hg := hL.1
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set c : ℝ → Fin n → ℝ := fun s => φ (s • w) with hc
  set c' : ℝ → Fin n → ℝ := fun s => fderiv ℝ φ (s • w) w with hc'
  have hmemr : ∀ s ∈ Icc (0 : ℝ) 1, s • w ∈ ball (0 : Fin n → ℝ) r := by
    intro s hs
    have hw' := mem_ball_zero_iff.1 hw
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [norm_nonneg w, hs.2, hs.1]
  set O : Set ℝ := (fun s : ℝ => s • w) ⁻¹' ball (0 : Fin n → ℝ) r with hO
  have hOo : IsOpen O := isOpen_ball.preimage (by fun_prop)
  have hIO : Icc (0 : ℝ) 1 ⊆ O := hmemr
  have hφd : ∀ s ∈ O, HasDerivAt c (c' s) s := by
    intro s hs
    have hsrc : s • w ∈ φ.source := hTB.mem_source hs
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (s • w)) (s • w) :=
      ((hTB.chart.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)).differentiableAt
        (by simp)).hasFDerivAt
    have hin : HasDerivAt (fun s : ℝ => s • w) w s := by
      simpa using (hasDerivAt_id s).smul_const w
    exact hdφ.comp_hasDerivAt s hin
  have hcC1 : ContDiffOn ℝ 1 c O := by
    have hφcd : ContDiffOn ℝ ∞ φ (ball 0 r) := by
      have := hTB.chart.contDiffOn
      rw [hTB.chart.source_eq] at this
      exact this.mono (ball_subset_ball hTB.le)
    have h2 : ContDiffOn ℝ ∞ (fun s : ℝ => s • w) O := (by fun_prop : ContDiff ℝ ∞ fun s : ℝ => s • w).contDiffOn
    exact (hφcd.comp h2 (fun s hs => hs)).of_le (by exact_mod_cast le_top)
  have htarget : ∀ s ∈ O, c s ∈ ψ.target := fun s hs =>
    hTB.chart.target_subset (φ.map_source (hTB.mem_source hs))
  set C : ℝ → M := fun s => ψ.symm (c s) with hC
  have hCsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 C (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm x).comp (hcC1.contMDiffOn.mono hIO) (fun s hs => htarget s (hIO hs))
  have hCvel : ∀ s ∈ Icc (0 : ℝ) 1, (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x
      ⟨C s, Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc 0 1) s⟩).2 = c' s := fun s hs =>
    (Causal.mdifferentiableWithinAt_chart_symm (I := 𝓘(ℝ, Fin n → ℝ)) x
      (uniqueDiffOn_Icc zero_lt_one s hs) hs (hφd s (hIO hs)).hasDerivWithinAt
      (fun s hs => htarget s (hIO hs))).2
  have hCsrc : ∀ s ∈ Icc (0 : ℝ) 1, C s ∈ ψ.source := fun s hs => ψ.map_target (htarget s (hIO hs))
  have hψC : ∀ s ∈ Icc (0 : ℝ) 1, ψ (C s) = c s := fun s hs => ψ.right_inv (htarget s (hIO hs))
  have hTL : ∀ s ∈ Icc (0 : ℝ) 1,
      T.IsFutureTimelike (Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc 0 1) s) := by
    intro s hs
    have hvq := eq_symmL_of_tTriv x (C s) (mem_baseSet_of_mem_source _ _ (hCsrc s hs)) _ (hCvel s hs)
    have hXC := timeOrientation_eq_symmL T x (C s) (hCsrc s hs)
    rw [hψC s hs] at hXC
    unfold Causal.TimeOrientation.IsFutureTimelike
    rw [hvq, hXC, metric_eq_bil_at g.toNondegMetric x (C s) (hCsrc s hs),
      metric_eq_bil_at g.toNondegMetric x (C s) (hCsrc s hs), hψC s hs]
    have hy : c s ∈ ψ.target := htarget s (hIO hs)
    have hLf := Lightlike.Geodesic.isLorentzianForm_matForm hL (hTB.chart.target_subset (φ.map_source
      (hTB.mem_source (hIO hs))) : c s ∈ ψ.target)
    have hq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric x) (c s) a b =
        matForm (g.coordMetric x (c s)) a b := fun a b => Lightlike.Geodesic.pairing_eq_matForm _ _ a b
    have hσs : Lightlike.Geodesic.pairing (g.coordMetric x) (c s) (c' s) (c' s) < 0 := by
      rw [← radial_pairing hg hTB.chart (hTB.mem_ball (hmemr s hs))] at hσ
      exact hσ
    have hdual : Lightlike.Geodesic.pairing (g.coordMetric x) (c s) (N (s • w)) (c' s) < 0 := by
      rw [hTB.dual _ (hmemr s hs)]; exact hx0
    have hNN := hTB.timelike _ (hmemr s hs)
    have hNX := hfutN _ (hmemr s hs)
    have hXX := timeCoord_timelike T x hy
    refine ⟨by rw [← pairing_eq_bil]; exact hσs, ?_⟩
    have := hLf.neg_of_neg_pair (X := timeCoord T x (c s)) (N := N (s • w)) (W := c' s)
      (by rw [← hq]; exact hXX) (by rw [← hq]; exact hNN) (by rw [← hq]; exact hNX)
      (by rw [← hq]; exact hσs) (by rw [← hq, Lightlike.Geodesic.pairing_comm hg hy]; exact hdual)
    rw [← pairing_eq_bil, hq]
    exact this
  have hcurve : Causal.IsFutureTimelikeCurve T C (Icc 0 1) :=
    Causal.isFutureTimelikeCurve_of_contMDiffOn T zero_lt_one hCsm hTL
  refine ⟨C, 0, 1, zero_lt_one, hcurve, ?_, ?_⟩
  · simp only [hC, hc, zero_smul]
    rw [hTB.chart.map_zero]
  · simp only [hC, hc, one_smul]

/-- **Local rigidity of a causal curve of `M` that does not enter `I⁺` of its start point.** Let `β`
be a future causal curve on `[a, b]` in the source of the chart at `x`, inside the future time ball
at `ψ (β a)`, with `β b ∉ I⁺(β a)`. Then `β b` is on the null cone of `β a` (`σ_p(v b) = 0`) and
`β` is, in normal coordinates, a monotone reparametrisation of the radial null geodesic:
`ψ (β t) = φ (lam t • vb)` with `lam` monotone from `0` to `1`. -/
theorem local_null_rigidity (T : Causal.TimeOrientation g) (x : M) {β : ℝ → M} {a b : ℝ}
    (hab : a < b) (hβ : Causal.IsFutureCausalCurve T β (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, β t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) {ρ r : ℝ}
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    (hTB : Lightlike.Geodesic.IsTimeBall (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a)) ρ φ
      (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))) r N)
    (hfutN : ∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0)
    (hin : ∀ t ∈ Icc a b, extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t) ∈ φ '' ball (0 : Fin n → ℝ) r)
    (hb : β b ∉ Causal.chronFuture T (β a)) :
    ∃ (lam : ℝ → ℝ) (vb : Fin n → ℝ), vb ∈ ball (0 : Fin n → ℝ) r ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a)) vb vb = 0 ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))) vb ≤ 0 ∧
      lam a = 0 ∧ lam b = 1 ∧ MonotoneOn lam (Icc a b) ∧ ContinuousOn lam (Icc a b) ∧
      ∀ t ∈ Icc a b, extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t) = φ (lam t • vb) := by
  have hL := g.isLorentzianCoordMetric_coordMetric x
  have hg := hL.1
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set p := ψ (β a) with hp
  set u : ℝ → Fin n → ℝ := fun t => ψ (β t) with hu
  obtain ⟨K, hK, hae⟩ := chart_curve_data T x hβ hsrc
  have hpU : p ∈ ψ.target := ψ.map_source (hsrc a ⟨le_rfl, hab.le⟩)
  set v : ℝ → Fin n → ℝ := fun t => φ.symm (u t) with hv
  have hvball : ∀ t ∈ Icc a b, v t ∈ ball (0 : Fin n → ℝ) r ∧ φ (v t) = u t := by
    intro t ht
    obtain ⟨w, hw, hwt⟩ := hin t ht
    have : v t = w := by
      simp only [hv, hu]
      rw [← hwt]
      exact φ.left_inv (hTB.mem_source hw)
    exact ⟨this ▸ hw, by rw [this]; exact hwt⟩
  have hmaps : ∀ t ∈ Icc a b, u t ∈ φ.target := by
    intro t ht
    obtain ⟨hvb, hφv⟩ := hvball t ht
    rw [← hφv]
    exact φ.map_source (hTB.mem_source hvb)
  obtain ⟨K', hvL⟩ := Lightlike.Geodesic.exists_lipschitzOnWith_comp_contDiffOn φ.open_target
    (hTB.chart.contDiffOn_symm.of_le (by exact_mod_cast le_top)) hK hmaps
  have hvL : LipschitzOnWith K' v (Icc a b) := hvL
  have hva : v a = 0 := by
    have : v a = φ.symm p := rfl
    rw [this, ← hTB.chart.map_zero]
    exact φ.left_inv (hTB.mem_source (mem_ball_self hTB.pos))
  have hd : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (φ (v t)) (fderiv ℝ φ (v t) v')
        (fderiv ℝ φ (v t) v') ≤ 0 ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (φ (v t)) (N (v t)) (fderiv ℝ φ (v t) v') < 0 := by
    filter_upwards [hae] with t ht hmt
    obtain ⟨u', hu', hne, hle, hfut⟩ := ht hmt
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self hmt
    obtain ⟨hvb, hφv⟩ := hvball t htI
    obtain ⟨D, hD, hDφ, -⟩ := hTB.exists_fderiv_symm hvb
    have hD' : HasFDerivAt φ.symm D (u t) := by rw [← hφv]; exact hD
    refine ⟨D u', hD'.comp_hasDerivAt t hu', ?_⟩
    rw [hDφ u', hφv]
    have hy : u t ∈ ψ.target := ψ.map_source (hsrc t htI)
    have hLf := Lightlike.Geodesic.isLorentzianForm_matForm hL hy
    have hq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric x) (u t) a b =
        matForm (g.coordMetric x (u t)) a b := fun a b =>
      Lightlike.Geodesic.pairing_eq_matForm _ _ a b
    refine ⟨hle, ?_⟩
    have hNN := hTB.timelike _ hvb
    have hNX := hfutN _ hvb
    rw [hφv] at hNN hNX
    have := hLf.neg_of_causal_of_timelike (X := timeCoord T x (u t)) (N := N (v t)) (u := u')
      (by rw [← hq]; exact timeCoord_timelike T x hy) (by rw [← hq]; exact hNN)
      (by rw [← hq]; exact hNX) (by rw [← hq]; exact hle) (by rw [← hq]; exact hfut) hne
    rw [Lightlike.Geodesic.pairing_comm hg hy, hq]
    exact this
  -- `σ_p ≤ 0` and `x⁰ ≥ 0` at the end
  have hcone := hTB.causal_cone hL hab.le hvL (fun t ht => (hvball t ht).1) hva (by
    filter_upwards [hd] with t ht hmt
    obtain ⟨v', hv', h1, h2⟩ := ht hmt
    exact ⟨v', hv', h1, h2⟩)
  have hvb := (hvball b ⟨hab.le, le_rfl⟩)
  have hnull : Lightlike.Geodesic.pairing (g.coordMetric x) p (v b) (v b) = 0 := by
    by_contra hne
    have hlt : Lightlike.Geodesic.pairing (g.coordMetric x) p (v b) (v b) < 0 :=
      lt_of_le_of_ne hcone.1 hne
    have hx0 : Lightlike.Geodesic.pairing (g.coordMetric x) p (timeCoord T x p) (v b) < 0 := by
      rcases lt_or_eq_of_le hcone.2 with h | h
      · linarith
      · exfalso
        have hLf := Lightlike.Geodesic.isLorentzianForm_matForm hL hpU
        have hq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric x) p a b =
            matForm (g.coordMetric x p) a b := fun a b =>
          Lightlike.Geodesic.pairing_eq_matForm _ _ a b
        have h0 : matForm (g.coordMetric x p) (v b) (timeCoord T x p) = 0 := by
          rw [← hq, Lightlike.Geodesic.pairing_comm hg hpU]; linarith
        have := hLf.eq_zero_of_orthogonal_timelike (X := timeCoord T x p)
          (by rw [← hq]; exact timeCoord_timelike T x hpU) h0 (by rw [← hq]; exact hcone.1)
        rw [this] at hlt
        simp [Lightlike.Geodesic.pairing] at hlt
    have hmem := radial_mem_chronFuture T x hTB hfutN hvb.1 hlt hx0
    rw [hvb.2] at hmem
    have e1 : ψ.symm (u b) = β b := ψ.left_inv (hsrc b ⟨hab.le, le_rfl⟩)
    have e2 : ψ.symm p = β a := ψ.left_inv (hsrc a ⟨le_rfl, hab.le⟩)
    rw [e1, e2] at hmem
    exact hb hmem
  obtain ⟨lam, hl0, hl1, hmono, hcont, hlam⟩ := hTB.null_rigidity hL hab hvL
    (fun t ht => (hvball t ht).1) hva (by
      filter_upwards [hd] with t ht hmt
      obtain ⟨v', hv', h1, h2⟩ := ht hmt
      exact ⟨v', hv', h1, h2⟩) hnull
  refine ⟨lam, v b, hvb.1, hnull, by linarith [hcone.2], hl0, hl1, hmono, hcont, fun t ht => ?_⟩
  rw [← hlam t ht, (hvball t ht).2]

end Lightlike.Penrose
