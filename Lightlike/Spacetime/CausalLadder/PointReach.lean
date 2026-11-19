import Lightlike.Spacetime.CausalLadder.NearFuture
import Lightlike.Spacetime.CausalLadder.LocalLift
import Lightlike.Spacetime.CausalLadder.PerturbTimelike
import Lightlike.Spacetime.CausalLadder.CurveContinuity
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# A curve with a timelike derivative at one point reaches nearby later points

Let `p` be a point of a manifold without boundary and `w₀` the chart coordinates (in the trivialization
at `p`) of a future-directed timelike vector at `p`. For every `w` near `w₀` and every small `τ > 0` the
point `(extChartAt I p).symm (φ p + τ w)` lies in the chronological future of `p` (`exists_segment_reach`):
the chart-straight segment is a `C¹` curve whose velocity `w` is timelike at every point near `p`, by the
continuity of the metric and of the time orientation.

Hence if a curve `γ` is differentiable at `σ` with a timelike velocity, then `γ (σ + τ) ∈ I⁺(γ σ)` for
small `τ > 0` (`reach_of_hasDeriv`): the difference quotient is near the velocity.

Supporting lemmas for the causal structure; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Chart-straight segments in a timelike direction reach the chronological future.** See the module
docstring. -/
theorem exists_segment_reach [BoundarylessManifold I M] (p : M) {v0 : TangentSpace I p}
    (hv0 : T.IsFutureTimelike v0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N ∈ 𝓝 (tTriv I M p ⟨p, v0⟩).2, ∀ w ∈ N, ∀ τ : ℝ, τ ∈ Ioc 0 δ →
      (extChartAt I p).symm (extChartAt I p p + τ • w) ∈ chronFuture T p := by
  obtain ⟨ξ, A, B, hA, hB, h0, hmodel⟩ := exists_chart_model T p
  have hfd : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  set φ := extChartAt I p with hφ
  have hbase : (tTriv I M p).baseSet ∈ 𝓝 p :=
    (tTriv I M p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p)
  have hp : p ∈ (tTriv I M p).baseSet := mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  set w0 : E := (tTriv I M p ⟨p, v0⟩).2 with hw0
  obtain ⟨hm1, hm2⟩ := hmodel p hp v0
  have hQ : quadForm (A p) (fun i => ξ.repr w0 i) < 0 := by rw [← hm1]; exact hv0.1
  have hL : linForm (B p) (fun i => ξ.repr w0 i) < 0 := by rw [← hm2]; exact hv0.2
  -- joint continuity of the two forms
  have hcQ : Continuous (fun x : (Fin n → Fin n → ℝ) × (Fin n → ℝ) => quadForm x.1 x.2) := by
    unfold quadForm; fun_prop
  have hcL : Continuous (fun x : (Fin n → ℝ) × (Fin n → ℝ) => linForm x.1 x.2) := by
    unfold linForm; fun_prop
  have hcrd : Continuous (fun w : E => (fun i => ξ.repr w i : Fin n → ℝ)) := by
    refine continuous_pi fun i => ?_
    have : (fun w : E => ξ.repr w i) = fun w => (ξ.coord i) w := by
      funext w; simp [Module.Basis.coord_apply]
    rw [this]
    exact (ξ.coord i).continuous_of_finiteDimensional
  have hEv : ∀ᶠ x : M × E in 𝓝 (p, w0), quadForm (A x.1) (fun i => ξ.repr x.2 i) < 0 ∧
      linForm (B x.1) (fun i => ξ.repr x.2 i) < 0 := by
    have hAp : ContinuousAt (fun x : M × E => (A x.1, (fun i => ξ.repr x.2 i : Fin n → ℝ))) (p, w0) :=
      (hA.comp continuousAt_fst).prodMk (hcrd.continuousAt.comp continuousAt_snd)
    have hBp : ContinuousAt (fun x : M × E => (B x.1, (fun i => ξ.repr x.2 i : Fin n → ℝ))) (p, w0) :=
      (hB.comp continuousAt_fst).prodMk (hcrd.continuousAt.comp continuousAt_snd)
    exact ((hcQ.continuousAt.comp hAp).eventually (Iio_mem_nhds hQ)).and
      ((hcL.continuousAt.comp hBp).eventually (Iio_mem_nhds hL))
  obtain ⟨W1, hW1, N1, hN1, hprod⟩ := mem_nhds_prod_iff.1 hEv
  -- the radius
  have hS : {x : E | φ p + x ∈ φ.target ∧ φ.symm (φ p + x) ∈ W1 ∩ (tTriv I M p).baseSet} ∈ 𝓝 (0 : E) := by
    have hlim : Tendsto (fun x : E => φ p + x) (𝓝 0) (𝓝 (φ p)) := by
      have := (tendsto_const_nhds (x := φ p) (f := 𝓝 (0 : E))).add (tendsto_id (x := 𝓝 (0 : E)))
      simpa using this
    refine inter_mem (hlim.eventually (extChartAt_target_mem_nhds_of_boundaryless p)) ?_
    have hsymm : ContinuousAt φ.symm (φ p) := continuousAt_extChartAt_symm p
    have : φ.symm (φ p) = p := φ.left_inv (mem_extChartAt_source p)
    exact hlim.eventually (hsymm.preimage_mem_nhds (by rw [this]; exact inter_mem hW1 hbase))
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.1 hS
  set Wn : ℝ := ‖w0‖ + 1 with hWn
  have hWnpos : 0 < Wn := by positivity
  refine ⟨r / (2 * Wn), by positivity, N1 ∩ Metric.ball w0 1, inter_mem hN1 (Metric.ball_mem_nhds _ one_pos),
    ?_⟩
  rintro w ⟨hwN, hwb⟩ τ ⟨hτ0, hτδ⟩
  have hwnorm : ‖w‖ ≤ Wn := by
    have : ‖w - w0‖ < 1 := by simpa [dist_eq_norm] using hwb
    have := norm_le_of_mem_closedBall (le_of_lt (by simpa [dist_eq_norm] using hwb) : dist w w0 ≤ 1)
    calc ‖w‖ = ‖w0 + (w - w0)‖ := by abel_nf
      _ ≤ ‖w0‖ + ‖w - w0‖ := norm_add_le _ _
      _ ≤ Wn := by rw [hWn]; linarith
  have hmem : ∀ u ∈ Icc 0 τ, φ p + u • w ∈ φ.target ∧
      φ.symm (φ p + u • w) ∈ W1 ∩ (tTriv I M p).baseSet := fun u hu => by
    have : u • w ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
      calc u * ‖w‖ ≤ τ * Wn := mul_le_mul hu.2 hwnorm (norm_nonneg _) hτ0.le
        _ ≤ r / (2 * Wn) * Wn := mul_le_mul_of_nonneg_right hτδ hWnpos.le
        _ = r / 2 := by field_simp
        _ < r := by linarith
    exact hrS this
  set c : ℝ → M := fun u => φ.symm (φ p + u • w) with hc
  have hcsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 τ) := by
    have hs : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target := contMDiffOn_extChartAt_symm p
    have hu' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => φ p + t • w) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    have := hs.comp hu'.contMDiffOn (fun t ht => (hmem t ht).1)
    exact this.of_le (by exact_mod_cast le_top)
  have hvel : ∀ u ∈ Icc 0 τ, T.IsFutureTimelike (velocity I c (Icc 0 τ) u) := by
    intro u hu
    have hd : HasDerivWithinAt (fun t : ℝ => φ p + t • w) w (Icc 0 τ) u := by
      have := ((hasDerivAt_id u).smul_const w).const_add (φ p)
      simpa using this.hasDerivWithinAt
    obtain ⟨-, hv⟩ := mdifferentiableWithinAt_chart_symm (I := I) p (uniqueDiffOn_Icc hτ0 u hu) hu hd
      (fun t' ht' => (hmem t' ht').1)
    obtain ⟨hm1', hm2'⟩ := hmodel (c u) (hmem u hu).2.2 (velocity I c (Icc 0 τ) u)
    have hv' : (tTriv I M p ⟨c u, velocity I c (Icc 0 τ) u⟩).2 = w := hv
    rw [hv'] at hm1' hm2'
    obtain ⟨hn1, hn2⟩ := hprod (show ((c u, w) : M × E) ∈ W1 ×ˢ N1 from ⟨(hmem u hu).2.1, hwN⟩)
    exact ⟨by rw [hm1']; exact hn1, by rw [hm2']; exact hn2⟩
  have hcurve := isFutureTimelikeCurve_of_contMDiffOn T hτ0 hcsm hvel
  refine ⟨c, 0, τ, hτ0, hcurve, ?_, rfl⟩
  show φ.symm (φ p + (0 : ℝ) • w) = p
  rw [zero_smul, add_zero]
  exact φ.left_inv (mem_extChartAt_source p)

/-- **A curve with a timelike derivative at a point reaches nearby later points in the chronological
future of that point.** -/
theorem reach_of_hasDeriv [BoundarylessManifold I M] {γ : ℝ → M} {s : Set ℝ} {σ : ℝ} (hs : s ∈ 𝓝 σ)
    (hcont : ContinuousAt γ σ) (hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s σ)
    (hv : T.IsFutureTimelike (velocity I γ s σ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, τ ∈ Ioc 0 δ → γ (σ + τ) ∈ chronFuture T (γ σ) := by
  set p := γ σ with hp
  set φ := extChartAt I p with hφ
  have hsrc : γ σ ∈ φ.source := mem_extChartAt_source p
  have hd : HasDerivAt (φ ∘ γ) (tTriv I M p ⟨γ σ, velocity I γ s σ⟩).2 σ :=
    (hasDerivWithinAt_chart_comp p hmd hsrc).hasDerivAt hs
  obtain ⟨δ₁, hδ₁, N, hN, hreach⟩ := exists_segment_reach T p hv
  have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ⁻¹ • ((φ ∘ γ) (σ + τ) - (φ ∘ γ) σ) ∈ N :=
    hd.tendsto_slope_zero_right.eventually hN
  have h2 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), γ (σ + τ) ∈ φ.source := by
    have hl : Tendsto (fun τ : ℝ => σ + τ) (𝓝[>] 0) (𝓝 σ) := by
      have : Tendsto (fun τ : ℝ => σ + τ) (𝓝 0) (𝓝 (σ + 0)) := (tendsto_const_nhds).add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (hcont.tendsto.comp hl).eventually ((isOpen_extChartAt_source p).mem_nhds hsrc)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 (h1.and h2))
  refine ⟨min δ₁ (ε / 2), lt_min hδ₁ (by positivity), fun τ hτ => ?_⟩
  have hτδ : τ ≤ δ₁ := hτ.2.trans (min_le_left _ _)
  have hτε : dist τ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]
    linarith [hτ.2.trans (min_le_right _ _)]
  obtain ⟨hwN, hsrc'⟩ := hεP hτε hτ.1
  have := hreach _ hwN τ ⟨hτ.1, hτδ⟩
  have hφp : φ p = (φ ∘ γ) σ := rfl
  have hτ0 : τ ≠ 0 := hτ.1.ne'
  rw [smul_inv_smul₀ hτ0, hφp, add_sub_cancel] at this
  have e := φ.left_inv hsrc'
  simp only [Function.comp_apply] at this
  rwa [e] at this

/-- Openness of `I⁺`, in the library (the statement of `T-GE2-P7`). -/
theorem isOpen_chronFuture_aux [BoundarylessManifold I M] (T' : TimeOrientation g) (x : M) :
    IsOpen (chronFuture T' x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨γ, a, b, hab, hγ, rfl, rfl⟩
  obtain ⟨U, hU, hreach⟩ := exists_nhds_reach T' hab hγ
  filter_upwards [hU] with z hz
  obtain ⟨G, e, hae, hG, hG1, hG2⟩ := hreach z hz
  exact ⟨G, a, e, hae, hG, hG1, hG2⟩

/-- **A curve with timelike velocity almost everywhere, without a margin, joins its end points in the
timelike future.** (The statement of `T-GE2-P19` for a manifold without boundary.) The proof uses one point
`σ` of differentiability with a timelike velocity: `γ (σ + τ) ∈ I⁺(γ σ)` for small `τ`
(`reach_of_hasDeriv`), then the push-ups of the two kinds (`T-GE2-P5`, `T-GE2-P6`). -/
theorem mem_chronFuture_of_ae_timelike_lib [BoundarylessManifold I M] {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelike v) γ (Icc a b)) :
    γ b ∈ chronFuture T (γ a) := by
  have hae := hγ.ae_velocity
  have hneZero : (volume.restrict (Icc a b) : Measure ℝ) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    simp [hab]
  haveI : (ae (volume.restrict (Icc a b) : Measure ℝ)).NeBot := ae_neBot.2 hneZero
  have hne2 : ∀ᵐ x ∂(volume.restrict (Icc a b) : Measure ℝ), x ≠ a ∧ x ≠ b := by
    refine ae_restrict_of_ae ?_
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
      simpa using (Set.countable_singleton a).ae_notMem (volume : Measure ℝ)
    have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
      simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
    filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
  obtain ⟨σ, ⟨⟨hmd, hvσ⟩, hσI⟩, hσne⟩ := ((hae.and (ae_restrict_mem measurableSet_Icc)).and hne2).exists
  have hσo : σ ∈ Ioo a b := ⟨lt_of_le_of_ne hσI.1 (Ne.symm hσne.1), lt_of_le_of_ne hσI.2 hσne.2⟩
  have hs : Icc a b ∈ 𝓝 σ := Icc_mem_nhds hσo.1 hσo.2
  have hcont : ContinuousAt γ σ := (hγ.lipschitz.continuousOn σ hσI).continuousAt hs
  obtain ⟨δ, hδ, hreach⟩ := reach_of_hasDeriv T hs hcont hmd hvσ
  set τ : ℝ := min δ (b - σ) with hτ
  have hτpos : 0 < τ := lt_min hδ (by linarith [hσo.2])
  have hy' : γ (σ + τ) ∈ chronFuture T (γ σ) := hreach τ ⟨hτpos, min_le_left _ _⟩
  -- the causal future along the curve
  have hcausal : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → γ v ∈ causalFuture T (γ u) := by
    intro u hu v hv huv
    rcases huv.lt_or_eq with hlt | heq
    · exact ⟨γ, u, v, huv, (IsCurveWith.restrict hγ (fun r hr => ⟨hu.1.trans hr.1, hr.2.trans hv.2⟩) hlt).mono_velocity
        (fun x w hw => T.isFutureCausal_of_isFutureTimelike hw), rfl, rfl⟩
    · subst heq; exact self_mem_causalFuture T _
  have hστ : σ + τ ∈ Icc a b := ⟨by linarith [hσo.1], by
    have := min_le_right δ (b - σ); linarith⟩
  have h5 : γ b ∈ chronFuture T (γ σ) :=
    chronFuture_causalFuture_trans_of_isOpen T (isOpen_chronFuture_aux T) hy'
      (hcausal _ hστ b ⟨hab.le, le_rfl⟩ (by have := min_le_right δ (b - σ); linarith))
  exact causalFuture_chronFuture_trans_of_isOpen T (isOpen_chronFuture_aux T.neg)
    (hcausal a ⟨le_rfl, hab.le⟩ σ hσI hσo.1.le) h5

end Lightlike.Causal
