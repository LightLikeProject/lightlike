import Lightlike.Spacetime.CausalLadder.LiftData
import Lightlike.Spacetime.CausalLadder.PerturbTimelike
import Lightlike.Spacetime.Causal.PushUp

/-!
# The local push-up property from the openness of the chronological future

In a manifold without boundary the chronological future of every point is open (the task
T-GE2-P7), and then the local lift property `LocalPushUp` holds: a future causal curve `β` from `y` to
`z` inside a small chart ball is lifted to a future timelike curve ending at `z`, by the chart displacement
`-ν (λ(u d) - λ(u t)) e`, where `u` is `β` in the chart, `λ` the time function of the chart and `e` a future
timelike vector. The displacement is proportional to the increase of the time function, so the
velocity of the lift is the velocity of `β` plus a multiple of `e`, future timelike with a margin
(`exists_lift_data`), and for `ν` small the lift starts in the open set `I⁺(x)` that contains `y`.
Hence `z ∈ I⁺(x)`.

The model is a manifold without boundary (`BoundarylessManifold`): this matches the source (Hawking–Ellis:
space-time has no boundary); approved by the maintainers, 18 November 2026.

Supporting lemma for the push-up lemmas of causality theory (Hawking–Ellis, Chapter 6, Proposition
6.4.1 for the local form); no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

set_option maxHeartbeats 4000000 in
/-- **The local push-up property from the openness of `I⁺`.** See the module docstring. -/
theorem localPushUp_of_isOpen [BoundarylessManifold I M]
    (hopen : ∀ x : M, IsOpen (chronFuture T x)) : LocalPushUp T := by
  intro p
  obtain ⟨lam, ē, m₀, r₁, hm₀, hr₁, htarget, hbase, hlift⟩ := exists_lift_data T p
  obtain ⟨ξ, -⟩ := exists_chart_model T p
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis ξ
  set φ := extChartAt I p with hφ
  obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = ‖lam‖ * ‖ē‖ := ⟨_, rfl⟩
  have hLc0 : 0 ≤ Lc := by rw [hLc]; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min (r₁ / (4 * (Lc + 1))) (m₀ / (2 * (Lc + 1))) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact lt_min (by positivity) (by positivity)
  have hr1 : 2 * (Lc + 1) * r ≤ r₁ / 2 := by
    have : r ≤ r₁ / (4 * (Lc + 1)) := by rw [hr]; exact min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hr2 : 2 * Lc * r ≤ m₀ := by
    have : r ≤ m₀ / (2 * (Lc + 1)) := by rw [hr]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hrr : r ≤ r₁ / 2 := by nlinarith
  set U : Set M := {q | q ∈ φ.source ∧ ‖φ q - φ p‖ < r} with hU
  have hUn : U ∈ 𝓝 p := by
    have h1 : φ.source ∈ 𝓝 p := (isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)
    have hc : ContinuousAt φ p := continuousAt_extChartAt p
    have h2 : {z | ‖φ z - φ p‖ < r} ∈ 𝓝 p := by
      have : ContinuousAt (fun z => ‖φ z - φ p‖) p := (hc.sub continuousAt_const).norm
      exact this.preimage_mem_nhds (by simpa using Iio_mem_nhds hrpos)
    exact inter_mem h1 h2
  refine ⟨U, hUn, ?_⟩
  intro α β a b c d hab hcd hα hβ hαβ hαU hβU
  have hO := hopen (α a)
  have hbmem : α b ∈ chronFuture T (α a) := ⟨α, a, b, hab, hα, rfl, rfl⟩
  rcases eq_or_lt_of_le hcd with hcd0 | hcd1
  · subst hcd0; rw [← hαβ]; exact hbmem
  set y := β c with hy
  have hysrc : y ∈ φ.source := (hβU ⟨le_rfl, hcd⟩).1
  obtain ⟨ρ, hρ, hρO⟩ : ∃ ρ > 0, ∀ z ∈ Metric.ball (φ y) ρ, φ.symm z ∈ chronFuture T (α a) := by
    have hc : ContinuousAt φ.symm (φ y) := continuousAt_extChartAt_symm' hysrc
    have h1 : φ.symm ⁻¹' (chronFuture T (α a)) ∈ 𝓝 (φ y) := by
      refine hc.preimage_mem_nhds ?_
      have hy' : y = α b := hαβ.symm
      rw [φ.left_inv hysrc, hy']
      exact hO.mem_nhds hbmem
    obtain ⟨ρ, hρ, h⟩ := Metric.mem_nhds_iff.1 h1
    exact ⟨ρ, hρ, fun z hz => h hz⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = min 1 (ρ / (2 * (2 * Lc * r + 1))) := ⟨_, rfl⟩
  have hν0 : 0 < ν := by rw [hν]; exact lt_min one_pos (by positivity)
  have hν1 : ν ≤ 1 := by rw [hν]; exact min_le_left _ _
  have hν2 : ν * (2 * Lc * r + 1) ≤ ρ / 2 := by
    have : ν ≤ ρ / (2 * (2 * Lc * r + 1)) := by rw [hν]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨ε, hε, hall⟩ := hlift ν hν0 hν1
  have hsrc : ∀ t ∈ Icc c d, β t ∈ φ.source := fun t ht => (hβU ht).1
  have hFr : ∀ t ∈ Icc c d, ‖φ (β t) - φ p‖ < r := fun t ht => (hβU ht).2
  obtain ⟨K, hF⟩ := exists_lipschitzOnWith_chart_comp hβ.lipschitz p hsrc
  have hae := ae_hasDerivAt_chart (P := fun _ v ↦ T.IsFutureCausal v) p hβ hsrc
  have hFball : ∀ t ∈ Icc c d, φ (β t) ∈ Metric.ball (φ p) r₁ := fun t ht => by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [hFr t ht]
  have hbaseβ : ∀ t ∈ Icc c d, β t ∈ (tTriv I M p).baseSet := fun t ht => by
    have := hbase (φ (β t)) (hFball t ht)
    rwa [φ.left_inv (hsrc t ht)] at this
  have hcaus : ∀ t ∈ Ioo c d, ∀ v : TangentSpace I (β t), T.IsFutureCausal v →
      T.IsFutureCausal (localField (I := I) p (tTriv I M p ⟨β t, v⟩).2 (φ.symm (φ (β t)))) := by
    intro t ht v hv
    have hq : φ.symm (φ (β t)) = β t := φ.left_inv (hsrc t (Ioo_subset_Icc_self ht))
    rw [hq]
    have : localField (I := I) p (tTriv I M p ⟨β t, v⟩).2 (β t) = v :=
      (tTriv I M p).symm_apply_apply_mk (hbaseβ t (Ioo_subset_Icc_self ht)) v
    rw [this]; exact hv
  have hposlam : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo c d → 0 < lam (deriv (φ ∘ β) t) := by
    filter_upwards [hae] with t ht htI
    obtain ⟨v, hv, hd⟩ := ht htI
    rw [hd.deriv]
    have hb := hFball t (Ioo_subset_Icc_self htI)
    exact (hall (φ (β t)) hb (φ (β t)) hb (by rw [dist_self]; positivity) _
      (hcaus t htI v hv)).1
  obtain ⟨hmono, hΔ⟩ := functional_increasing_of_ae_pos hcd1 hF lam hposlam
  set F : ℝ → E := φ ∘ β with hFdef
  have hΔ0 : ∀ t ∈ Icc c d, 0 ≤ lam (F d) - lam (F t) ∧
      lam (F d) - lam (F t) ≤ lam (F d) - lam (F c) := fun t ht =>
    ⟨by linarith [hmono t ht d ⟨hcd, le_rfl⟩ ht.2], by linarith [hmono c ⟨le_rfl, hcd⟩ t ht ht.1]⟩
  have hΔb : lam (F d) - lam (F c) ≤ 2 * ‖lam‖ * r := by
    have h2 := lam.le_opNorm (F d - F c)
    have h3 : ‖F d - F c‖ ≤ 2 * r := by
      calc ‖F d - F c‖ = ‖(F d - φ p) - (F c - φ p)‖ := by congr 1; abel
        _ ≤ ‖F d - φ p‖ + ‖F c - φ p‖ := norm_sub_le _ _
        _ ≤ r + r := by
            have := hFr d ⟨hcd, le_rfl⟩
            have := hFr c ⟨le_rfl, hcd⟩
            simp only [hFdef, Function.comp_apply]; linarith
        _ = 2 * r := by ring
    calc lam (F d) - lam (F c) = lam (F d - F c) := by simp
      _ ≤ ‖lam (F d - F c)‖ := Real.le_norm_self _
      _ ≤ ‖lam‖ * ‖F d - F c‖ := h2
      _ ≤ ‖lam‖ * (2 * r) := by gcongr
      _ = 2 * ‖lam‖ * r := by ring
  -- the lifted chart curve
  obtain ⟨sh, hsh⟩ : ∃ sh : ℝ → ℝ, sh = fun t => ν * (lam (F d) - lam (F t)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ → E, u = fun t => F t - sh t • ē := ⟨_, rfl⟩
  have hshn : ∀ t ∈ Icc c d, ‖sh t • ē‖ ≤ ν * (2 * Lc * r) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hΔ0 t ht
    rw [norm_smul, Real.norm_of_nonneg (by rw [hsh]; positivity)]
    have h3 : sh t ≤ ν * (2 * ‖lam‖ * r) := by
      rw [hsh]; exact mul_le_mul_of_nonneg_left (by linarith) hν0.le
    calc sh t * ‖ē‖ ≤ ν * (2 * ‖lam‖ * r) * ‖ē‖ := by gcongr
      _ = ν * (2 * Lc * r) := by rw [hLc]; ring
  have huball : ∀ t ∈ Icc c d, u t ∈ Metric.ball (φ p) r₁ := fun t ht => by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖F t - φ p‖ < r := hFr t ht
    have h2 := hshn t ht
    have : u t - φ p = (F t - φ p) - sh t • ē := by rw [hu]; simp only; module
    rw [this]
    calc ‖(F t - φ p) - sh t • ē‖ ≤ ‖F t - φ p‖ + ‖sh t • ē‖ := norm_sub_le _ _
      _ < r + ν * (2 * Lc * r) := by linarith
      _ ≤ r + 2 * Lc * r := by nlinarith [mul_nonneg hLc0 hrpos.le]
      _ ≤ r₁ := by nlinarith
  have hudist : ∀ t ∈ Icc c d, dist (u t) (F t) ≤ ν * m₀ := fun t ht => by
    rw [dist_eq_norm]
    have : u t - F t = -(sh t • ē) := by rw [hu]; simp only; module
    rw [this, norm_neg]
    exact (hshn t ht).trans (by nlinarith)
  have hulip : ∃ K' : NNReal, LipschitzOnWith K' u (Icc c d) := by
    have hl : LipschitzOnWith (‖lam‖₊ * K) (fun t => lam (F t)) (Icc c d) :=
      lam.lipschitzWith.comp_lipschitzOnWith hF
    refine ⟨K + ν.toNNReal * (‖lam‖₊ * K) * ‖ē‖₊, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    have h1 := hF.dist_le_mul x hx x' hx'
    have h2 := hl.dist_le_mul x hx x' hx'
    have h1' : ‖F x - F x'‖ ≤ K * |x - x'| := by simpa [dist_eq_norm, Real.dist_eq] using h1
    have h2' : |lam (F x) - lam (F x')| ≤ (‖lam‖₊ * K) * |x - x'| := by
      simpa [Real.dist_eq] using h2
    have e : u x - u x' = (F x - F x') + (ν * (lam (F x) - lam (F x'))) • ē := by
      rw [hu, hsh]; simp only; module
    rw [dist_eq_norm, e, Real.dist_eq]
    calc ‖(F x - F x') + (ν * (lam (F x) - lam (F x'))) • ē‖
        ≤ ‖F x - F x'‖ + ‖(ν * (lam (F x) - lam (F x'))) • ē‖ := norm_add_le _ _
      _ = ‖F x - F x'‖ + ν * |lam (F x) - lam (F x')| * ‖ē‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hν0]
      _ ≤ K * |x - x'| + ν * ((‖lam‖₊ * K) * |x - x'|) * ‖ē‖ := by gcongr
      _ = ↑(K + ν.toNNReal * (‖lam‖₊ * K) * ‖ē‖₊) * |x - x'| := by
          push_cast; rw [Real.coe_toNNReal _ hν0.le]; ring
  have hutarget : ∀ t ∈ Icc c d, u t ∈ φ.target := fun t ht => htarget (huball t ht)
  have hcurve : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelikeWith ε v) (φ.symm ∘ u)
      (Icc c d) := by
    obtain ⟨K', hK'⟩ := hulip
    have hne2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c ∧ x ≠ d := by
      have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
        simpa using (Set.countable_singleton c).ae_notMem (volume : Measure ℝ)
      have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ d := by
        simpa using (Set.countable_singleton d).ae_notMem (volume : Measure ℝ)
      filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
    refine ⟨ordConnected_Icc, isLocallyLipschitzOn_chart_symm hK' p hutarget, ?_⟩
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae, hne2] with t ht hne htI
    have htIoo : t ∈ Ioo c d :=
      ⟨lt_of_le_of_ne htI.1 (Ne.symm hne.1), lt_of_le_of_ne htI.2 hne.2⟩
    obtain ⟨v, hv, hd⟩ := ht htIoo
    obtain ⟨D, hD⟩ : ∃ D : E, D = (tTriv I M p ⟨β t, v⟩).2 := ⟨_, rfl⟩
    rw [← hD] at hd
    have hl : HasDerivAt (fun t => lam (F t)) (lam D) t := lam.hasFDerivAt.comp_hasDerivAt t hd
    have hsh' : HasDerivAt sh (-(ν * lam D)) t := by
      rw [hsh]; exact ((hl.const_sub (lam (F d))).const_mul ν).congr_deriv (by ring)
    have hdu : HasDerivAt u (D + (ν * lam D) • ē) t := by
      rw [hu]
      exact (hd.sub (hsh'.smul_const ē)).congr_deriv (by simp)
    obtain ⟨hmd, hvel'⟩ := mdifferentiableWithinAt_chart_symm p (uniqueDiffOn_Icc hcd1 t htI) htI
      hdu.hasDerivWithinAt hutarget
    refine ⟨hmd, ?_⟩
    have hq' : (φ.symm ∘ u) t ∈ (tTriv I M p).baseSet := hbase (u t) (huball t htI)
    have hvv : velocity I (φ.symm ∘ u) (Icc c d) t =
        localField (I := I) p (D + (ν * lam D) • ē) ((φ.symm ∘ u) t) := by
      have := (tTriv I M p).symm_apply_apply_mk hq' (velocity I (φ.symm ∘ u) (Icc c d) t)
      rw [hvel'] at this
      exact this.symm
    rw [hvv]
    have hcs := hcaus t htIoo v hv
    rw [← hD] at hcs
    exact (hall (F t) (hFball t htI) (u t) (huball t htI) (hudist t htI) D hcs).2
  have hudend : u d = F d := by rw [hu, hsh]; simp
  have hz1 : φ.symm (u c) ∈ chronFuture T (α a) := by
    refine hρO _ ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : u c - φ y = -(sh c • ē) := by
      rw [hu]; simp only [hy, hFdef, Function.comp_apply]; module
    rw [h1, norm_neg]
    have := hshn c ⟨le_rfl, hcd⟩
    nlinarith
  obtain ⟨γ₁, a₁, b₁, hab₁, hγ₁, hγ₁a, hγ₁b⟩ := hz1
  have hG : IsFutureTimelikeCurve T (φ.symm ∘ u) (Icc c d) :=
    isFutureTimelikeCurve_of_margin T hε hcurve
  obtain ⟨G, e', he', hG', hGa, hGe⟩ :=
    IsFutureTimelikeCurve.trans T hγ₁ hG hab₁ hcd1 hγ₁b
  refine ⟨G, a₁, e', he', hG', hGa.trans hγ₁a, ?_⟩
  rw [hGe]
  show φ.symm (u d) = β d
  rw [hudend]
  exact φ.left_inv (hsrc d ⟨hcd, le_rfl⟩)


/-- **Push-up, first form, from the openness of `I⁺`**: if the chronological future of every point is
open (the task T-GE2-P7), then `y ∈ I⁺(x)` and `z ∈ J⁺(y)` give `z ∈ I⁺(x)`. -/
theorem chronFuture_causalFuture_trans [BoundarylessManifold I M]
    (hopen : ∀ x : M, IsOpen (chronFuture T x)) {x y z : M} (hxy : y ∈ chronFuture T x)
    (hyz : z ∈ causalFuture T y) : z ∈ chronFuture T x :=
  chronFuture_causalFuture_trans_of T hopen (localPushUp_of_isOpen T hopen) hxy hyz

/-- **Push-up, second form, from the openness of `I⁺` and of `I⁻`**: `y ∈ J⁺(x)` and `z ∈ I⁺(y)`
give `z ∈ I⁺(x)`. -/
theorem causalFuture_chronFuture_trans [BoundarylessManifold I M]
    (hopenNeg : ∀ x : M, IsOpen (chronFuture T.neg x)) {x y z : M} (hxy : y ∈ causalFuture T x)
    (hyz : z ∈ chronFuture T y) : z ∈ chronFuture T x :=
  causalFuture_chronFuture_trans_of T hopenNeg (localPushUp_of_isOpen T.neg hopenNeg) hxy hyz

end Lightlike.Causal
