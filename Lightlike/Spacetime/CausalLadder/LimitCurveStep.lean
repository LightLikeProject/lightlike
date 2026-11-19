import Lightlike.Spacetime.CausalLadder.LimitCurve
import Lightlike.Spacetime.CausalLadder.BoxExit
import Lightlike.Spacetime.CausalLadder.BoundarylessChart
import Lightlike.Spacetime.CausalLadder.AffineCurve
import Lightlike.Spacetime.CausalLadder.GluedLimitCurve
import Lightlike.Spacetime.CausalLadder.UnitArcEndpoint

/-!
# The uniform step of the limit-curve theorem

Step of the proof of the limit-curve theorem (task `T-GE2-P20`, Hawking–Ellis Lemma 6.2.1): near every point `q` of a
manifold without boundary there are `ρ > 0` and a neighbourhood `N`, **independent of the subsequence**, such that from every
point `q' ∈ N` that is a limit point of the curves of a subsequence of future-inextendible future causal curves there is a unit
arc of chart displacement at least `ρ` in the chart of `q`, a limit arc of a subsubsequence (`limit_curve_step`).

The proof: the cone estimate of the chart box at `q`; every curve of the subsequence that passes near `q'` leaves the box
(`exists_exit_of_not_tendsto`); the exit arcs have converging start points (near `q'`) and, by compactness of the sphere, a
subsequence of converging exit points; the one-chart limit-curve theorem
(`limit_curve_points_of_cone_estimate`) gives a limit arc from `q'` to the limit exit point, of chart displacement at least `ρ`,
and an affine reparametrisation brings it to `[0, 1]`.

Supporting lemma for the limit-curve theorem; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory Metric
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)


/-- Positive multiples of a future causal vector are future causal. -/
theorem TimeOrientation.isFutureCausal_smul {x : M} {v : TangentSpace I x} (hv : T.IsFutureCausal v) {c : ℝ}
    (hc : 0 < c) : T.IsFutureCausal (c • v) := by
  obtain ⟨h0, h1, h2⟩ := hv
  refine ⟨smul_ne_zero hc.ne' h0, ?_, ?_⟩
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg (sq_nonneg c) (neg_nonneg.2 h1)]
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hc h2


/-- **The uniform step.** See the module docstring. -/
theorem limit_curve_step [T2Space M] [BoundarylessManifold I M]
    (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ)
    (hγ : ∀ k, IsFutureCausalCurve T (γ k) (s k) ∧
      ∀ q : M, ¬ Tendsto (fun t : s k => γ k t) atTop (𝓝 q)) (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N ∈ 𝓝 q, closure N ⊆ (extChartAt I q).source ∧ StepAt T γ s q ρ N := by
  classical
  -- finite dimensionality of the model space, from the Lorentzian frame at `q`
  have hfin : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian q
    exact Module.Finite.of_basis (e.map ((tTriv I M q).linearEquivAt ℝ q
      (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) q)))
  obtain ⟨W, hW, hWb, ℓ, C, hC, hcone, hest⟩ := exists_cone_estimate_curve T q
  set φ := extChartAt I q with hφ
  have hbox : ConeBox T q W ℓ C := hest
  -- a radius `R` such that the closed ball of radius `R` around `φ q` is in the target with preimage in `W`
  have hA : φ.target ∩ φ.symm ⁻¹' (interior W) ∈ 𝓝 (φ q) := by
    refine inter_mem (extChartAt_target_mem_nhds_of_boundaryless q) ?_
    have hc : ContinuousAt φ.symm (φ q) := continuousAt_extChartAt_symm q
    exact hc.preimage_mem_nhds (by
      rw [φ.left_inv (mem_extChartAt_source q)]; exact interior_mem_nhds.2 hW)
  obtain ⟨ε, hε, hεA⟩ := Metric.mem_nhds_iff.1 hA
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ε / 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hRsub : closedBall (φ q) R ⊆ ball (φ q) ε := closedBall_subset_ball (by rw [hR]; linarith)
  have hr : ∀ y ∈ closedBall (φ q) R, y ∈ φ.target ∧ φ.symm y ∈ W := fun y hy =>
    ⟨(hεA (hRsub hy)).1, interior_subset (hεA (hRsub hy)).2⟩
  -- the compact box `K`
  have hKcomp : ∀ r ≤ R, IsCompact (φ.symm '' closedBall (φ q) r) := fun r hrR =>
    (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm q).mono fun y hy => (hr y (closedBall_subset_closedBall hrR hy)).1)
  have hKW : ∀ r ≤ R, φ.symm '' closedBall (φ q) r ⊆ interior W := by
    rintro r hrR _ ⟨y, hy, rfl⟩
    exact (hεA (hRsub (closedBall_subset_closedBall hrR hy))).2
  have hKsrc : ∀ r ≤ R, φ.symm '' closedBall (φ q) r ⊆ φ.source := by
    rintro r hrR _ ⟨y, hy, rfl⟩
    exact φ.map_target (hr y (closedBall_subset_closedBall hrR hy)).1
  -- the neighbourhood `N`
  obtain ⟨N, hNdef⟩ : ∃ N : Set M, N = φ.source ∩ φ ⁻¹' ball (φ q) (R / 4) := ⟨_, rfl⟩
  have hNopen : IsOpen N := by
    rw [hNdef, hφ, extChartAt_source]
    exact isOpen_extChartAt_preimage (I := I) q isOpen_ball
  have hqN : q ∈ N := by
    rw [hNdef]; exact ⟨mem_extChartAt_source q, mem_ball_self (by positivity)⟩
  have hNsub : N ⊆ φ.symm '' closedBall (φ q) (R / 4) := by
    intro x hx
    rw [hNdef] at hx
    obtain ⟨hxs, hxb⟩ := hx
    exact ⟨φ x, ball_subset_closedBall hxb, φ.left_inv hxs⟩
  have hNcl : closure N ⊆ φ.source :=
    (closure_minimal hNsub (hKcomp (R / 4) (by linarith)).isClosed).trans (hKsrc _ (by linarith))
  refine ⟨R / 2, by positivity, N, hNopen.mem_nhds hqN, hNcl, ?_⟩
  intro ψ0 hψ0 q' hq' hlp
  rw [hNdef] at hq'
  obtain ⟨hq's, hq'b⟩ := hq'
  haveI := hfin
  obtain ⟨y', hy'⟩ : ∃ y' : E, y' = φ q' := ⟨_, rfl⟩
  have hy'b : y' ∈ ball (φ q) (R / 4) := by rw [hy']; exact hq'b
  have hq'K : q' ∈ φ.symm '' closedBall (φ q) R :=
    ⟨y', closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy'b), by rw [hy']; exact φ.left_inv hq's⟩
  -- the sequence of near start points
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun i : ℕ => R / (4 * ((i : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : ∀ i, 0 < δ i := fun i => by rw [hδ]; positivity
  have hδle : ∀ i, δ i ≤ R / 4 := fun i => by
    rw [hδ]
    have : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    rw [hδ]
    have : Tendsto (fun i : ℕ => R / 4 * (1 / ((i : ℝ) + 1))) atTop (𝓝 (R / 4 * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul _
    simpa [mul_zero] using this.congr fun i => by field_simp
  have hNi : ∀ i, φ.source ∩ φ ⁻¹' ball y' (δ i) ∈ 𝓝 q' := fun i => by
    have : IsOpen (φ.source ∩ φ ⁻¹' ball y' (δ i)) := by
      rw [hφ, extChartAt_source]
      exact isOpen_extChartAt_preimage (I := I) q isOpen_ball
    exact this.mem_nhds ⟨hq's, by rw [mem_preimage, ← hy']; exact mem_ball_self (hδpos i)⟩
  have hev : ∀ i, ∀ᶠ k in atTop, ∃ t ∈ s (ψ0 k), γ (ψ0 k) t ∈ φ.source ∩ φ ⁻¹' ball y' (δ i) :=
    fun i => hlp _ (hNi i)
  obtain ⟨kk, hkk, hP⟩ := Filter.extraction_forall_of_eventually hev
  choose tt htts httmem using hP
  -- the exit points
  have hin0 : ∀ i, φ (γ (ψ0 (kk i)) (tt i)) ∈ ball (φ q) R := fun i => by
    have h1 := (httmem i).2
    rw [mem_preimage, mem_ball_iff_norm] at h1
    rw [mem_ball_iff_norm]
    have h2 := mem_ball_iff_norm.1 hy'b
    have h3 := hδle i
    calc ‖φ (γ (ψ0 (kk i)) (tt i)) - φ q‖ ≤ ‖φ (γ (ψ0 (kk i)) (tt i)) - y'‖ + ‖y' - φ q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by linarith
  have hexit : ∀ i, ∃ t₁ ∈ s (ψ0 (kk i)), tt i ≤ t₁ ∧
      (∀ u ∈ Icc (tt i) t₁, γ (ψ0 (kk i)) u ∈ φ.source ∧ φ (γ (ψ0 (kk i)) u) ∈ closedBall (φ q) R) ∧
      ‖φ (γ (ψ0 (kk i)) t₁) - φ q‖ = R := fun i =>
    exists_exit_of_not_tendsto T q hC hbox hr (hγ (ψ0 (kk i))).1 (hγ (ψ0 (kk i))).2 (htts i)
      (httmem i).1 (hin0 i)
  choose t1 ht1s htle hin hnorm using hexit
  have hlt : ∀ i, tt i < t1 i := fun i => by
    refine lt_of_le_of_ne (htle i) fun h => ?_
    have h1 := hnorm i
    rw [← h] at h1
    have h2 := mem_ball_iff_norm.1 (hin0 i)
    linarith
  have hsubs : ∀ i, Icc (tt i) (t1 i) ⊆ s (ψ0 (kk i)) := fun i u hu =>
    (hγ (ψ0 (kk i))).1.ordConnected.out (htts i) (ht1s i) hu
  have harc : ∀ i, IsFutureCausalCurve T (γ (ψ0 (kk i))) (Icc (tt i) (t1 i)) := fun i =>
    IsCurveWith.restrict (hγ (ψ0 (kk i))).1 (hsubs i) (hlt i)
  have hKmem : ∀ i, ∀ t ∈ Icc (tt i) (t1 i), γ (ψ0 (kk i)) t ∈ φ.symm '' closedBall (φ q) R :=
    fun i t ht => ⟨φ (γ (ψ0 (kk i)) t), (hin i t ht).2, φ.left_inv (hin i t ht).1⟩
  have hsph : ∀ i, φ (γ (ψ0 (kk i)) (t1 i)) ∈ sphere (φ q) R := fun i => by
    rw [mem_sphere_iff_norm]; exact hnorm i
  obtain ⟨yE, hyE, ψ1, hψ1, hlim1⟩ := (isCompact_sphere (φ q) R).tendsto_subseq hsph
  have hyEn : ‖yE - φ q‖ = R := mem_sphere_iff_norm.1 hyE
  have hyEt : yE ∈ φ.target := (hr yE (sphere_subset_closedBall hyE)).1
  have hstart : Tendsto (fun i => φ (γ (ψ0 (kk i)) (tt i))) atTop (𝓝 (φ q')) := by
    rw [← hy']
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun i => dist_nonneg) (fun i => ?_) hδlim)
    have := (httmem i).2
    rw [mem_preimage, mem_ball] at this
    exact this.le
  -- the one-chart limit curve
  have hyK : φ.symm yE ∈ φ.symm '' closedBall (φ q) R := ⟨yE, sphere_subset_closedBall hyE, rfl⟩
  obtain ⟨σ, α, β, hαβ, hσ, hσα, hσβ, ⟨ψ2, hψ2, hpts⟩, hσK⟩ :=
    limit_curve_points_of_cone_estimate T q hWb hC hcone hest (φ.symm '' closedBall (φ q) R) (hKcomp R le_rfl)
      (hKW R le_rfl) (fun j => γ (ψ0 (kk (ψ1 j)))) (fun j => tt (ψ1 j)) (fun j => t1 (ψ1 j)) q' (φ.symm yE)
      hq'K hyK (fun j => htle (ψ1 j)) (fun j => harc (ψ1 j)) (fun j => hKmem (ψ1 j))
      (hstart.comp hψ1.tendsto_atTop)
      (by
        have : φ (φ.symm yE) = yE := φ.right_inv hyEt
        rw [this]
        exact hlim1)
  -- the displacement
  have hdisp : R / 2 ≤ ‖φ (φ.symm yE) - φ q'‖ := by
    rw [φ.right_inv hyEt, ← hy']
    have h1 : ‖yE - φ q‖ ≤ ‖yE - y'‖ + ‖y' - φ q‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 := mem_ball_iff_norm.1 hy'b
    linarith
  have hαβ' : α < β := by
    refine lt_of_le_of_ne hαβ fun h => ?_
    have h1 : σ α = σ β := by rw [h]
    rw [hσα, hσβ] at h1
    rw [h1] at hdisp
    simp at hdisp
    linarith
  refine ⟨fun u => σ (α + u * (β - α)), fun j => kk (ψ1 (ψ2 j)), hkk.comp (hψ1.comp hψ2), ?_, ?_, ?_, ?_, ?_⟩
  · exact IsCurveWith.affine (P := fun _ v => T.IsFutureCausal v)
      (fun x v c hc hv => TimeOrientation.isFutureCausal_smul T hv hc) hσ hαβ'
  · simp [hσα]
  · intro u hu U hU
    have hu' : α + u * (β - α) ∈ Icc α β :=
      ⟨by nlinarith [hu.1, hαβ'], by nlinarith [hu.2, hαβ']⟩
    filter_upwards [hpts _ hu' U hU] with j hj
    obtain ⟨t, ht, hUt⟩ := hj
    exact ⟨t, hsubs _ ht, hUt⟩
  · intro u hu
    have hu' : α + u * (β - α) ∈ Icc α β :=
      ⟨by nlinarith [hu.1, hαβ'], by nlinarith [hu.2, hαβ']⟩
    exact hKsrc R le_rfl (hσK _ hu')
  · have : α + (1 : ℝ) * (β - α) = β := by ring
    simp only [this, hσβ]
    exact hdisp


/-- **The limit-curve theorem** (Hawking–Ellis, Lemma 6.2.1): the statement of `T-GE2-P20`, from the uniform step, the
glued curve and the absence of endpoints. -/
theorem exists_inextendible_limit_curve_of_step [T2Space M] [SecondCountableTopology M]
    [BoundarylessManifold I M] (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ)
    (hγ : ∀ k, IsFutureCausalCurve T (γ k) (s k) ∧
      ∀ q : M, ¬ Tendsto (fun t : s k => γ k t) atTop (𝓝 q))
    (p : M) (hp : ∀ U ∈ 𝓝 p, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U) :
    ∃ (σ : ℝ → M) (r : Set ℝ), (IsFutureCausalCurve T σ r ∧
        ∀ q : M, ¬ Tendsto (fun t : r => σ t) atTop (𝓝 q)) ∧ p ∈ σ '' r ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ q ∈ σ '' r, ∀ U ∈ 𝓝 q, ∀ᶠ k in atTop,
        ∃ t ∈ s (φ k), γ (φ k) t ∈ U := by
  obtain ⟨c, ρ, N, σ, φ, hρ, hopen, hcl, hcov, hLC, -, harc⟩ :=
    exists_glued_limit_curve_of_step T γ s p hp (fun q => limit_curve_step T γ s hγ q)
  exact ⟨σ, Ici 0, ⟨hLC.1, not_tendsto_of_unit_arcs c ρ N σ hρ hopen hcl hcov harc⟩, hLC.2.2.2.1, φ,
    hLC.2.2.2.2.1, hLC.2.2.2.2.2⟩

end Lightlike.Causal
