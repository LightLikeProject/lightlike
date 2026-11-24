import Lightlike.Rows.G1_012.Defs
import Lightlike.Spacetime.CausalLadder.ChartCurve
import Lightlike.Spacetime.Causal.CurveMargin

/-!
# A future null geodesic is a future causal curve (G1-012)

A null geodesic of `Penrose.IsNullGeodesicOn` whose velocity points to the future of a time orientation `T`
(`IsFutureNullGeodesicOn`) is a future-directed causal curve of the library's class (`Causal.IsFutureCausalCurve`):
the chart expression is `C¹` (hence locally Lipschitz, `geodesic_local_lipschitz`), the velocity of the curve has the
chart coordinates `w t` (`geodesic_local_velocity`), and the metric of that vector is the coordinate bilinear form
(`metric_eq_bil`), which vanishes by nullity. The future-pointing condition `g(γ', T.X) < 0` is a hypothesis of the
definition, since `IsNullGeodesicOn` does not fix a time orientation.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The metric on a vector given by its coordinates `D` in the chart at `x₀`, at `x₀` itself, is the coordinate bilinear form. -/
theorem metric_eq_bil (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) (D : Fin n → ℝ) :
    g.g x₀ ((chartTriv n x₀).symmL ℝ x₀ D) ((chartTriv n x₀).symmL ℝ x₀ D) =
      bil (g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀)) D D := by
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (mem_extChartAt_source x₀)
  have hD : (chartTriv n x₀).symmL ℝ x₀ D = ∑ i, D i • (chartTriv n x₀).symmL ℝ x₀ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ D]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hb : ∀ i j, g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) i j =
      g.g x₀ ((chartTriv n x₀).symmL ℝ x₀ (Pi.single i 1)) ((chartTriv n x₀).symmL ℝ x₀ (Pi.single j 1)) := by
    intro i j
    have := g.coordMetric_eq x₀ hy i j
    rw [coordBasis_apply, coordBasis_apply] at this
    have e : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀) = x₀ :=
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv (mem_extChartAt_source x₀)
    rw [e] at this
    exact this
  rw [hD]
  unfold bil
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]
  ring

/-- Local chart data of a geodesic curve: differentiability within `Icc a b` and the coordinates of the velocity. -/
theorem geodesic_local_velocity {γ : ℝ → M} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {w : ℝ → Fin n → ℝ} {O : Set ℝ} (hO : O ∈ 𝓝 t)
    (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source)
    (hpos : ∀ s ∈ O, HasDerivAt (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) (w s) s) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t ∧
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) ⟨γ t, Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t⟩).2 = w t := by
  set p := γ t with hp
  set u : ℝ → Fin n → ℝ := fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) p (γ s) with hu
  have hUD : UniqueDiffWithinAt ℝ (Icc a b ∩ O) t :=
    (uniqueDiffOn_Icc hab t ht).inter hO
  have htarget : ∀ t' ∈ Icc a b ∩ O, u t' ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target :=
    fun t' ht' => (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_source (hsrc t' ht'.2)
  have hder : HasDerivWithinAt u (w t) (Icc a b ∩ O) t :=
    (hpos t (mem_of_mem_nhds hO)).hasDerivWithinAt
  obtain ⟨hmd, hvel⟩ := Causal.mdifferentiableWithinAt_chart_symm (I := 𝓘(ℝ, Fin n → ℝ)) p hUD
    ⟨ht, mem_of_mem_nhds hO⟩ hder htarget
  have heq : γ =ᶠ[𝓝[Icc a b ∩ O] t] (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm ∘ u := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (by simpa using hsrc s hs.2)).symm
  have hγt : γ t = ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm ∘ u) t :=
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (by simpa using hsrc t (mem_of_mem_nhds hO))).symm
  have hmd' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (Icc a b ∩ O) t :=
    hmd.congr_of_eventuallyEq heq hγt
  refine ⟨(mdifferentiableWithinAt_inter hO).1 hmd', ?_⟩
  have hv1 : Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t =
      Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b ∩ O) t := by
    unfold Causal.velocity
    rw [mfderivWithin_inter hO]
  have hv2 : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ (Icc a b ∩ O) t =
      mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm ∘ u) (Icc a b ∩ O) t :=
    heq.mfderivWithin_eq hγt
  have hv3 : Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t =
      Causal.velocity 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm ∘ u) (Icc a b ∩ O) t := by
    rw [hv1]; unfold Causal.velocity; rw [hv2]; rfl
  rw [← hvel]
  have key : ∀ (x y : M) (v : Fin n → ℝ), x = y →
      (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p ⟨x, v⟩).2 = (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p ⟨y, v⟩).2 := by
    intro x y v h; subst h; rfl
  rw [key _ _ (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t) hγt]
  rw [hv3]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- Local Lipschitz bound in the chart at `γ t` for a chart-`C¹` curve with continuous velocity. -/
theorem geodesic_local_lipschitz {γ : ℝ → M} {a b t : ℝ} {w : ℝ → Fin n → ℝ} {O : Set ℝ}
    (hO : O ∈ 𝓝 t) (hsrc : ∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source)
    (hpos : ∀ s ∈ O, HasDerivAt (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) (w s) s)
    (hwc : ∀ s ∈ O, ContinuousAt w s) :
    ∃ (K : NNReal) (U : Set ℝ), U ∈ 𝓝[Icc a b] t ∧
      MapsTo γ U (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source ∧
      LipschitzOnWith K (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) ∘ γ) U := by
  have hwt : ContinuousAt w t := hwc t (mem_of_mem_nhds hO)
  have hb : ∀ᶠ s in 𝓝 t, s ∈ O ∧ ‖w s‖ < ‖w t‖ + 1 := by
    filter_upwards [hO, hwt.norm.eventually (gt_mem_nhds (lt_add_one ‖w t‖))] with s h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  have hcl : Metric.closedBall t (r / 2) ⊆ Metric.ball t r := Metric.closedBall_subset_ball (by linarith)
  refine ⟨⟨‖w t‖ + 1, by positivity⟩, Icc a b ∩ Metric.closedBall t (r / 2), ?_, ?_, ?_⟩
  · have : Metric.closedBall t (r / 2) ∈ 𝓝 t := Metric.closedBall_mem_nhds t (by linarith)
    exact inter_mem_nhdsWithin _ this
  · intro s hs
    exact hsrc s (hball s (hcl hs.2)).1
  · refine LipschitzOnWith.mono (t := Metric.closedBall t (r / 2)) ?_ inter_subset_right
    refine (convex_closedBall t (r / 2)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) ∘ γ) (f' := w) ?_ ?_
    · intro s hs
      exact (hpos s (hball s (hcl hs)).1).hasDerivWithinAt
    · intro s hs
      have := (hball s (hcl hs)).2
      show (‖w s‖₊ : ℝ) ≤ ‖w t‖ + 1
      rw [coe_nnnorm]
      exact this.le

variable {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- A **future-directed null geodesic on `J`**: a null geodesic whose velocity points to the future of the time
orientation `T` (`g(γ', T.X) < 0`). -/
def IsFutureNullGeodesicOn (T : Causal.TimeOrientation g) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  IsNullGeodesicOn g γ J ∧
    ∀ t ∈ J, g.g (γ t) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ J t) (T.X (γ t)) < 0

/-- **A future null geodesic is a future causal curve** (on a compact interval): its chart expression is `C¹`, hence
locally Lipschitz, and its velocity is a non-zero null vector in the future cone. -/
theorem IsFutureNullGeodesicOn.isFutureCausalCurve (T : Causal.TimeOrientation g) {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (h : IsFutureNullGeodesicOn T γ (Icc a b)) :
    Causal.IsFutureCausalCurve T γ (Icc a b) := by
  obtain ⟨hnull, hfut⟩ := h
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, O, hO, hsrc, hg, -⟩ := hnull t ht
    exact geodesic_local_lipschitz hO hsrc hg.pos (fun s hs => (hg.vel s hs).continuousAt)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    obtain ⟨w, O, hO, hsrc, hg, hw0, hbil⟩ := hnull t ht
    obtain ⟨hmd, hvel⟩ := geodesic_local_velocity hab ht hO hsrc hg.pos
    have hb : γ t ∈ (chartTriv n (γ t)).baseSet := FiberBundle.mem_baseSet_trivializationAt' (γ t)
    have hlin : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t),
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) ⟨γ t, v⟩).2 = (chartTriv n (γ t)).linearEquivAt ℝ (γ t) hb v :=
      fun v => by rw [Trivialization.linearEquivAt_apply]
    have hv_eq : Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t = (chartTriv n (γ t)).symmL ℝ (γ t) (w t) := by
      have := (chartTriv n (γ t)).symm_apply_apply_mk hb (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) t)
      rw [hvel] at this
      rw [Trivialization.symmL_apply (chartTriv n (γ t)) hb]
      exact this.symm
    refine ⟨hmd, ?_, ?_, hfut t ht⟩
    · intro hv
      rw [hv, hlin, map_zero] at hvel
      exact hw0 hvel.symm
    · rw [hv_eq]
      have := metric_eq_bil g.toNondegMetric (γ t) (w t)
      exact (this.trans hbil).le

end Lightlike.Penrose
