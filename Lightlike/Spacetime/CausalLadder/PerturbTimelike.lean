import Lightlike.Spacetime.CausalLadder.BoundarylessChart
import Lightlike.Spacetime.CausalLadder.ChartModel
import Lightlike.Spacetime.CausalLadder.ConeStability
import Lightlike.Spacetime.CausalLadder.ChartFTC
import Lightlike.Spacetime.CausalLadder.ChartCurve
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Perturbing the end of a timelike curve

Let `γ` be a future-directed timelike curve on `[a, b]` in a manifold without boundary, `y = γ b`.
Then every point `z` near `y` is reached from `γ a` by a future-directed timelike curve. In the chart at
`y` the curve is `F = φ ∘ γ` on `[t₀, b]`, `t₀` close to `b`; let `λ` be the functional given by the
pairing with the time orientation at `y`. Then `λ ∘ F` is increasing, and
`F_z (t) = F (t) + h (t) (φ z - φ y)`, `h = λ (F - F t₀) / λ (F b - F t₀)`, is a Lipschitz curve from `F t₀`
to `φ z` whose velocity is that of `F` plus a vector that is small relative to it. By
`cone_margin_stable` its velocity is future timelike with the margin `ε / 2`, and `φ.symm ∘ F_z` is a
future-directed timelike curve (`IsFutureTimelikeCurve`). Together with `γ` on `[a, t₀]` this gives
the curve from `γ a` to `z`; hence the chronological future of a point is open.

Supporting lemma for the causal structure (the openness of the chronological future).
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Almost everywhere, the chart derivative of a curve is the trivialized velocity.** For a curve with
velocity in `P` on `[a, b]` with values in the chart at `y`, for almost every interior `t` the chart
curve has the derivative `(tTriv y ⟨γ t, v⟩).2` for a velocity `v` satisfying `P`. -/
lemma ae_hasDerivAt_chart {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b : ℝ} (y : M)
    (hγ : IsCurveWith (I := I) P γ (Icc a b)) (hsrc : ∀ t ∈ Icc a b, γ t ∈ (extChartAt I y).source) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → ∃ v : TangentSpace I (γ t), P (γ t) v ∧
      HasDerivAt (extChartAt I y ∘ γ) (tTriv I M y ⟨γ t, v⟩).2 t := by
  have h := hγ.ae_velocity
  rw [ae_restrict_iff' measurableSet_Icc] at h
  filter_upwards [h] with t ht htI
  obtain ⟨hmd, hP⟩ := ht (Ioo_subset_Icc_self htI)
  refine ⟨velocity I γ (Icc a b) t, hP, ?_⟩
  exact (hasDerivWithinAt_chart_comp y hmd (hsrc t (Ioo_subset_Icc_self htI))).hasDerivAt
    (Icc_mem_nhds htI.1 htI.2)

/-- **Choice of a parameter close to the end and of a radius.** For a curve locally Lipschitz on `[a, b]`
and `y = γ b`, and a neighbourhood `W` of `y`, there are a radius `R` with the ball of radius `2 R` around
`φ y` in the target of the chart at `y` and mapped by `φ.symm` into `W`, and `t₀ ∈ (a, b)` such that
`γ t` lies in the chart source with `‖φ (γ t) - φ y‖ < R` for `t ∈ [t₀, b]`. -/
lemma exists_radius_and_start [BoundarylessManifold I M] {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hlip : IsLocallyLipschitzOn (I := I) γ (Icc a b)) {W : Set M} (hW : W ∈ 𝓝 (γ b)) :
    ∃ R > 0, Metric.ball (extChartAt I (γ b) (γ b)) (2 * R) ⊆ (extChartAt I (γ b)).target ∧
      (∀ x ∈ Metric.ball (extChartAt I (γ b) (γ b)) (2 * R), (extChartAt I (γ b)).symm x ∈ W) ∧
      ∃ t0 ∈ Ioo a b, ∀ t ∈ Icc t0 b, γ t ∈ (extChartAt I (γ b)).source ∧
        ‖extChartAt I (γ b) (γ t) - extChartAt I (γ b) (γ b)‖ < R := by
  set y := γ b with hy
  set φ := extChartAt I y with hφ
  have hbmem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  -- the radius
  have h1 : φ.target ∩ φ.symm ⁻¹' W ∈ 𝓝 (φ y) := by
    refine inter_mem (extChartAt_target_mem_nhds_of_boundaryless y) ?_
    have hc : ContinuousAt φ.symm (φ y) := continuousAt_extChartAt_symm y
    have : φ.symm (φ y) = y := φ.left_inv (mem_extChartAt_source y)
    exact hc.preimage_mem_nhds (by rw [this]; exact hW)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 h1
  refine ⟨r / 2, by positivity, ?_, ?_, ?_⟩
  · intro x hx
    exact (hrsub (by rw [Metric.mem_ball] at hx ⊢; linarith)).1
  · intro x hx
    exact (hrsub (by rw [Metric.mem_ball] at hx ⊢; linarith)).2
  · -- the parameter `t₀`
    obtain ⟨K, U, hU, hmaps, hl⟩ := hlip b hbmem
    have hbU : b ∈ U := mem_of_mem_nhdsWithin hbmem hU
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    set η : ℝ := min (δ / 2) (r / 2 / (2 * (K + 1))) with hη
    have hη0 : 0 < η := lt_min (by positivity) (by positivity)
    refine ⟨max ((a + b) / 2) (b - η), ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · refine max_lt (by linarith) (by linarith)
    · intro t ht
      have ht1 : (a + b) / 2 ≤ t := (le_max_left _ _).trans ht.1
      have ht2 : b - η ≤ t := (le_max_right _ _).trans ht.1
      have htI : t ∈ Icc a b := ⟨by linarith, ht.2⟩
      have htU : t ∈ U := hδU ⟨by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have : η ≤ δ / 2 := min_le_left _ _
        constructor <;> linarith [ht.2], htI⟩
      refine ⟨hmaps htU, ?_⟩
      have hlipt := hl.dist_le_mul t htU b hbU
      simp only [Function.comp_apply, dist_eq_norm] at hlipt
      have hbt : |t - b| ≤ η := by
        rw [abs_of_nonpos (by linarith [ht.2])]; linarith
      have hη2 : η ≤ r / 2 / (2 * (K + 1)) := min_le_right _ _
      have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
      calc ‖extChartAt I (γ b) (γ t) - extChartAt I (γ b) (γ b)‖ ≤ K * |t - b| := hlipt
        _ ≤ K * η := mul_le_mul_of_nonneg_left hbt hK0
        _ ≤ K * (r / 2 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hη2 hK0
        _ < r / 2 := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith [hr]

/-- **Every point near the end of a timelike curve is reached from its start by a timelike curve.**
See the module docstring. -/
theorem exists_nhds_reach [BoundarylessManifold I M] {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsFutureTimelikeCurve T γ (Icc a b)) :
    ∃ U ∈ 𝓝 (γ b), ∀ z ∈ U, ∃ (G : ℝ → M) (e : ℝ), a < e ∧ IsFutureTimelikeCurve T G (Icc a e) ∧
      G a = γ a ∧ G e = z := by
  set y := γ b with hy
  obtain ⟨ε, hε, hm⟩ := hγ.2 a b hab subset_rfl
  obtain ⟨ξ, A, B, hA, hB, h0, hmodel⟩ := exists_chart_model T y
  obtain ⟨Wt, hWt, htr⟩ := cone_margin_transfer hA hB h0 hε
  obtain ⟨Ws, hWs, θ, hθ, hstab⟩ := cone_margin_stable hA hB h0 hε
  have hbase : (tTriv I M y).baseSet ∈ 𝓝 y :=
    (tTriv I M y).open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) y)
  have hW : Wt ∩ Ws ∩ (tTriv I M y).baseSet ∈ 𝓝 y := inter_mem (inter_mem hWt hWs) hbase
  obtain ⟨R, hR, hRt, hRW, t0, ht0, ht0s⟩ := exists_radius_and_start hab hm.lipschitz hW
  set φ := extChartAt I y with hφ
  have hm0 : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelikeWith ε v) γ (Icc t0 b) :=
    hm.mono ht0.1.le le_rfl ht0.2
  have hsrc : ∀ t ∈ Icc t0 b, γ t ∈ φ.source := fun t ht => (ht0s t ht).1
  have hγW : ∀ t ∈ Icc t0 b, γ t ∈ Wt ∩ Ws ∩ (tTriv I M y).baseSet := fun t ht => by
    have := hRW (φ (γ t)) (by
      rw [Metric.mem_ball, dist_eq_norm]
      have := (ht0s t ht).2
      linarith)
    rwa [φ.left_inv (hsrc t ht)] at this
  obtain ⟨K, hF⟩ := exists_lipschitzOnWith_chart_comp hm0.lipschitz y hsrc
  have hae := ae_hasDerivAt_chart y hm0 hsrc
  -- the functional `lam`
  have : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  let lamL : E →ₗ[ℝ] ℝ := -(∑ i, B y i • ξ.coord i)
  let lam : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap lamL
  have hlam : ∀ w, lam w = -linForm (B y) (fun i => ξ.repr w i) := by
    intro w
    simp [lam, lamL, linForm, Module.Basis.coord_apply, mul_comm]
  -- the velocity of `γ` has positive `lam`
  have hvel : ∀ t ∈ Ioo t0 b, ∀ v : TangentSpace I (γ t), T.IsFutureTimelikeWith ε v →
      quadForm (A (γ t)) (fun i => ξ.repr (tTriv I M y ⟨γ t, v⟩).2 i) ≤
        -ε * (linForm (B (γ t)) (fun i => ξ.repr (tTriv I M y ⟨γ t, v⟩).2 i)) ^ 2 ∧
      linForm (B (γ t)) (fun i => ξ.repr (tTriv I M y ⟨γ t, v⟩).2 i) < 0 := by
    intro t ht v hv
    have hq := (hγW t (Ioo_subset_Icc_self ht)).2
    obtain ⟨h1, h2⟩ := hmodel (γ t) hq v
    refine ⟨?_, ?_⟩
    · rw [← h1, ← h2]; exact hv.1
    · rw [← h2]; exact hv.2
  have hposlam : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo t0 b → 0 < lam (deriv (extChartAt I y ∘ γ) t) := by
    filter_upwards [hae] with t ht htI
    obtain ⟨v, hv, hd⟩ := ht htI
    rw [hd.deriv, hlam]
    have hc := hvel t htI v hv
    have hqt := (hγW t (Ioo_subset_Icc_self htI)).1.1
    have := htr (γ t) hqt _ hc.1 hc.2
    linarith [this.2]
  obtain ⟨hmono, hΔ⟩ := functional_increasing_of_ae_pos ht0.2 hF lam hposlam
  set F : ℝ → E := extChartAt I y ∘ γ with hFdef
  set Δ : ℝ := lam (F b) - lam (F t0) with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; linarith
  set h : ℝ → ℝ := fun t => (lam (F t) - lam (F t0)) / Δ with hhdef
  have hh0 : h t0 = 0 := by simp [hhdef]
  have hh1 : h b = 1 := by
    show (lam (F b) - lam (F t0)) / Δ = 1
    rw [← hΔdef, div_self hΔpos.ne']
  have hhI : ∀ t ∈ Icc t0 b, 0 ≤ h t ∧ h t ≤ 1 := fun t ht => by
    refine ⟨div_nonneg (by linarith [hmono t0 ⟨le_rfl, ht0.2.le⟩ t ht ht.1]) hΔpos.le, ?_⟩
    rw [hhdef, div_le_one hΔpos]
    linarith [hmono t ht b ⟨ht0.2.le, le_rfl⟩ ht.2]
  -- the bound of the pairing at `y`
  obtain ⟨Bb0, hBb0⟩ := (Set.finite_range (fun i : Fin n => |B y i|)).bddAbove
  set Bb : ℝ := max Bb0 0 with hBb
  have hBb0' : 0 ≤ Bb := le_max_right _ _
  have hBy : ∀ i, |B y i| ≤ Bb := fun i => (hBb0 ⟨i, rfl⟩).trans (le_max_left _ _)
  set r1 : ℝ := θ * Δ / (n * Bb + 1) with hr1
  have hr1pos : 0 < r1 := by positivity
  let crd : E →L[ℝ] (Fin n → ℝ) := LinearMap.toContinuousLinearMap
    (LinearMap.pi fun i => (ξ.coord i : E →ₗ[ℝ] ℝ))
  have hcrd : ∀ w i, crd w i = ξ.repr w i := fun w i => by simp [crd, Module.Basis.coord_apply]
  set U : Set M := {z | z ∈ φ.source ∧ ‖φ z - φ y‖ < R ∧ ‖crd (φ z - φ y)‖ < r1} with hU
  have hUn : U ∈ 𝓝 y := by
    have h1 : φ.source ∈ 𝓝 y := (isOpen_extChartAt_source y).mem_nhds (mem_extChartAt_source y)
    have hc : ContinuousAt φ y := continuousAt_extChartAt y
    have h2 : {z | ‖φ z - φ y‖ < R} ∈ 𝓝 y := by
      have : ContinuousAt (fun z => ‖φ z - φ y‖) y := (hc.sub continuousAt_const).norm
      exact this.preimage_mem_nhds (by simpa using Iio_mem_nhds hR)
    have h3 : {z | ‖crd (φ z - φ y)‖ < r1} ∈ 𝓝 y := by
      have : ContinuousAt (fun z => ‖crd (φ z - φ y)‖) y :=
        (crd.continuous.continuousAt.comp (hc.sub continuousAt_const)).norm
      exact this.preimage_mem_nhds (by simpa using Iio_mem_nhds hr1pos)
    exact inter_mem h1 (inter_mem h2 h3)
  refine ⟨U, hUn, fun z hz => ?_⟩
  obtain ⟨hzs, hzR, hzr⟩ := hz
  set u0 : E := φ z - φ y with hu0
  set Fz : ℝ → E := fun t => F t + h t • u0 with hFz
  -- the perturbed chart curve stays in the ball
  have hFzball : ∀ t ∈ Icc t0 b, Fz t ∈ Metric.ball (φ y) (2 * R) := fun t ht => by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖F t - φ y‖ < R := (ht0s t ht).2
    have h2 : ‖h t • u0‖ ≤ ‖u0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hhI t ht).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hhI t ht).2
    have : Fz t - φ y = (F t - φ y) + h t • u0 := by simp only [hFz]; abel
    rw [this]
    calc ‖(F t - φ y) + h t • u0‖ ≤ ‖F t - φ y‖ + ‖h t • u0‖ := norm_add_le _ _
      _ < 2 * R := by linarith
  have hFztarget : ∀ t ∈ Icc t0 b, Fz t ∈ φ.target := fun t ht => hRt (hFzball t ht)
  have hFzW : ∀ t ∈ Icc t0 b, φ.symm (Fz t) ∈ Wt ∩ Ws ∩ (tTriv I M y).baseSet := fun t ht =>
    hRW _ (hFzball t ht)
  have hhlip : ∃ Kh : NNReal, LipschitzOnWith Kh h (Icc t0 b) := by
    refine ⟨(Δ⁻¹).toNNReal * (‖lam‖₊ * K), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    have h1 := (lam.lipschitzWith.comp_lipschitzOnWith hF).dist_le_mul x hx x' hx'
    simp only [hhdef, Real.dist_eq] at h1 ⊢
    have hΔi : 0 ≤ Δ⁻¹ := inv_nonneg.2 hΔpos.le
    calc |(lam (F x) - lam (F t0)) / Δ - (lam (F x') - lam (F t0)) / Δ|
        = Δ⁻¹ * |lam (F x) - lam (F x')| := by
          rw [← sub_div, div_eq_inv_mul, abs_mul, abs_of_nonneg hΔi]; ring_nf
      _ ≤ Δ⁻¹ * (↑(‖lam‖₊ * K) * |x - x'|) := mul_le_mul_of_nonneg_left h1 hΔi
      _ = ↑((Δ⁻¹).toNNReal * (‖lam‖₊ * K)) * |x - x'| := by
          push_cast; rw [Real.coe_toNNReal _ hΔi]; ring
  have hFzlip : ∃ K', LipschitzOnWith K' Fz (Icc t0 b) := by
    obtain ⟨Kh, hKh⟩ := hhlip
    refine ⟨K + Kh * ‖u0‖₊, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    have h1 := hF.dist_le_mul x hx x' hx'
    have h2 := hKh.dist_le_mul x hx x' hx'
    have h1' : ‖F x - F x'‖ ≤ K * |x - x'| := by simpa [dist_eq_norm, Real.dist_eq] using h1
    have h2' : |h x - h x'| ≤ Kh * |x - x'| := by simpa [Real.dist_eq] using h2
    have e : Fz x - Fz x' = (F x - F x') + (h x - h x') • u0 := by simp only [hFz]; module
    rw [dist_eq_norm, e, Real.dist_eq]
    calc ‖(F x - F x') + (h x - h x') • u0‖ ≤ ‖F x - F x'‖ + ‖(h x - h x') • u0‖ := norm_add_le _ _
      _ = ‖F x - F x'‖ + |h x - h x'| * ‖u0‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ K * |x - x'| + (Kh * |x - x'|) * ‖u0‖ := by gcongr
      _ = ↑(K + Kh * ‖u0‖₊) * |x - x'| := by push_cast; ring
  have hcurve : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelikeWith (ε / 2) v)
      (φ.symm ∘ Fz) (Icc t0 b) := by
    obtain ⟨K', hK'⟩ := hFzlip
    have hne2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t0 ∧ x ≠ b := by
      have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t0 := by
        simpa using (Set.countable_singleton t0).ae_notMem (volume : Measure ℝ)
      have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
        simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
      filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
    refine ⟨ordConnected_Icc, isLocallyLipschitzOn_chart_symm hK' y hFztarget, ?_⟩
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae, hne2] with t ht hne htI
    have htIoo : t ∈ Ioo t0 b := ⟨lt_of_le_of_ne htI.1 (Ne.symm hne.1), lt_of_le_of_ne htI.2 hne.2⟩
    obtain ⟨v, hv, hd⟩ := ht htIoo
    set om : E := (tTriv I M y ⟨γ t, v⟩).2 with hom
    have hdh : HasDerivAt h (lam om / Δ) t :=
      ((lam.hasFDerivAt.comp_hasDerivAt t hd).sub_const (lam (F t0))).div_const Δ
    have hdz : HasDerivAt Fz (om + (lam om / Δ) • u0) t := hd.add (hdh.smul_const u0)
    obtain ⟨hmd, hvel'⟩ := mdifferentiableWithinAt_chart_symm y (uniqueDiffOn_Icc ht0.2 t htI) htI
      hdz.hasDerivWithinAt hFztarget
    refine ⟨hmd, ?_⟩
    set v' := velocity I (φ.symm ∘ Fz) (Icc t0 b) t with hv'
    have hq : γ t ∈ Wt ∩ Ws ∩ (tTriv I M y).baseSet := hγW t htI
    have hq' : (φ.symm ∘ Fz) t ∈ Wt ∩ Ws ∩ (tTriv I M y).baseSet := hFzW t htI
    obtain ⟨hm1, hm2⟩ := hmodel ((φ.symm ∘ Fz) t) hq'.2 v'
    rw [hvel'] at hm1 hm2
    obtain ⟨hv1, hv2⟩ := hvel t htIoo v hv
    -- coordinates
    set w : Fin n → ℝ := fun i => ξ.repr om i with hw
    set u : Fin n → ℝ := (lam om / Δ) • (fun i => ξ.repr u0 i) with hu
    have hwu : (fun i => ξ.repr (om + (lam om / Δ) • u0) i) = w + u := by
      funext i; simp [hw, hu]
    have hlamom : |lam om| ≤ n * Bb * ‖w‖ := by
      rw [hlam]; rw [abs_neg]; exact abs_linForm_le (B y) hBy w
    have hnorm : ‖u‖ ≤ θ * ‖w‖ := by
      have hcu : ‖(fun i => ξ.repr u0 i)‖ ≤ r1 := by
        have : (fun i => ξ.repr u0 i) = crd u0 := funext fun i => (hcrd u0 i).symm
        rw [this]
        have : crd u0 = crd (φ z - φ y) := rfl
        exact (le_of_lt hzr)
      rw [hu, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hΔpos]
      calc |lam om| / Δ * ‖(fun i => ξ.repr u0 i)‖ ≤ (n * Bb * ‖w‖) / Δ * r1 := by gcongr
        _ = θ * ‖w‖ * ((n * Bb) / (n * Bb + 1)) := by rw [hr1]; field_simp
        _ ≤ θ * ‖w‖ * 1 := by
            gcongr
            rw [div_le_one (by positivity)]; linarith
        _ = θ * ‖w‖ := by ring
    have hstab' := hstab (γ t) hq.1.2 ((φ.symm ∘ Fz) t) hq'.1.2 w u hv1 hv2 hnorm
    rw [← hwu] at hstab'
    constructor
    · rw [hm1, hm2]; exact hstab'.1
    · rw [hm2]; exact hstab'.2
  have hend0 : (φ.symm ∘ Fz) t0 = γ t0 := by
    show φ.symm (F t0 + h t0 • u0) = γ t0
    rw [hh0, zero_smul, add_zero]
    exact φ.left_inv (hsrc t0 ⟨le_rfl, ht0.2.le⟩)
  have hendb : (φ.symm ∘ Fz) b = z := by
    show φ.symm (F b + h b • u0) = z
    rw [hh1, one_smul]
    have : F b = φ y := rfl
    rw [this, hu0]
    simpa using φ.left_inv hzs
  -- the curve `γ` on `[a, t₀]`
  have hγ1 : IsFutureTimelikeCurve T γ (Icc a t0) :=
    isFutureTimelikeCurve_of_margin T hε (hm.mono le_rfl ht0.2.le ht0.1)
  have hγ2 : IsFutureTimelikeCurve T (φ.symm ∘ Fz) (Icc t0 b) :=
    isFutureTimelikeCurve_of_margin T (half_pos hε) hcurve
  obtain ⟨G, e, hae', hG, hG1, hG2⟩ := IsFutureTimelikeCurve.trans T hγ1 hγ2 ht0.1 ht0.2 hend0.symm
  exact ⟨G, e, hae', hG, hG1, hG2.trans hendb⟩

end Lightlike.Causal
