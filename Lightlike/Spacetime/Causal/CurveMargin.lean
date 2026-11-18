import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Curves of class `C¹` have a margin

A future-directed timelike curve of class `C¹` on `[a, b]` whose velocity is future-directed
timelike at every point has a margin on `[a, b]`: the velocity stays in a closed cone strictly
inside the future timelike cone. This is the bridge from the textbooks' piecewise `C¹` timelike
curves to `Causal.IsFutureTimelikeCurve`. The proof: the quantities `g(γ', γ')` and `g(γ', X)` are
continuous along the curve, so `-g(γ', γ') / g(γ', X)²` is continuous and positive on the compact
interval and has a positive minimum.
-/

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The metric applied to two continuous vector fields along a continuous curve is continuous. -/
theorem continuousWithinAt_metric_along {b : ℝ → M} {v w : ∀ u, TangentSpace I (b u)} {s : Set ℝ}
    {x : ℝ}
    (hb : ContinuousWithinAt b s x)
    (hv : ContinuousWithinAt
      (fun u ↦ TotalSpace.mk' E (E := fun q : M ↦ TangentSpace I q) (b u) (v u)) s x)
    (hw : ContinuousWithinAt
      (fun u ↦ TotalSpace.mk' E (E := fun q : M ↦ TangentSpace I q) (b u) (w u)) s x) :
    ContinuousWithinAt (fun u ↦ g.g (b u) (v u) (w u)) s x := by
  have hg : ContinuousAt (fun q ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) q (g.g q)) (b x) :=
    (g.contMDiff.continuous).continuousAt
  have := ContinuousWithinAt.clm_bundle_apply₂ (E₃ := Bundle.Trivial M ℝ) (F₃ := ℝ) (b := b)
    (hg.comp_continuousWithinAt hb) hv hw
  simp only [FiberBundle.continuousWithinAt_totalSpace] at this
  exact this.2

theorem continuous_unitVector : Continuous fun u : ℝ => (⟨u, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := by
  have := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)))
  exact this

/-- **A `C¹` curve with everywhere future-directed timelike velocity has a margin** on `[a, b]`:
there is `ε > 0` with `g(γ', γ') ≤ -ε g(γ', X)²` at every point. Local Lipschitz continuity is
taken as a hypothesis (it holds for `C¹` curves). -/
theorem exists_margin_of_contMDiffOn {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hv : ∀ t ∈ Icc a b, T.IsFutureTimelike (velocity I γ (Icc a b) t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Icc a b, T.IsFutureTimelikeWith ε (velocity I γ (Icc a b) t) := by
  have hu : UniqueMDiffOn 𝓘(ℝ, ℝ) (Icc a b) := (uniqueDiffOn_Icc hab).uniqueMDiffOn
  have hT := hγ.continuousOn_tangentMapWithin le_rfl hu
  have hV : ContinuousOn (fun u ↦ TotalSpace.mk' E (E := fun q : M ↦ TangentSpace I q) (γ u)
      (velocity I γ (Icc a b) u)) (Icc a b) :=
    hT.comp continuous_unitVector.continuousOn fun u hu' ↦ hu'
  have hX : ContinuousOn (fun u ↦ TotalSpace.mk' E (E := fun q : M ↦ TangentSpace I q) (γ u)
      (T.X (γ u))) (Icc a b) :=
    T.contMDiff.continuous.comp_continuousOn hγ.continuousOn
  have hA : ContinuousOn (fun u ↦ g.g (γ u) (velocity I γ (Icc a b) u)
      (velocity I γ (Icc a b) u)) (Icc a b) := fun u hu' ↦
    continuousWithinAt_metric_along (hγ.continuousOn u hu') (hV u hu') (hV u hu')
  have hB : ContinuousOn (fun u ↦ g.g (γ u) (velocity I γ (Icc a b) u) (T.X (γ u))) (Icc a b) :=
    fun u hu' ↦ continuousWithinAt_metric_along (hγ.continuousOn u hu') (hV u hu') (hX u hu')
  have hf : ContinuousOn (fun u ↦ -g.g (γ u) (velocity I γ (Icc a b) u)
      (velocity I γ (Icc a b) u) / (g.g (γ u) (velocity I γ (Icc a b) u) (T.X (γ u))) ^ 2)
      (Icc a b) :=
    hA.neg.div (hB.pow 2) fun u hu' ↦ (sq_pos_of_neg (hv u hu').2).ne'
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab.le) hf
  have hpos : ∀ u ∈ Icc a b, 0 < -g.g (γ u) (velocity I γ (Icc a b) u)
      (velocity I γ (Icc a b) u) / (g.g (γ u) (velocity I γ (Icc a b) u) (T.X (γ u))) ^ 2 :=
    fun u hu' ↦ div_pos (neg_pos.2 (hv u hu').1) (sq_pos_of_neg (hv u hu').2)
  refine ⟨_, hpos u₀ hu₀, fun u hu' ↦ ⟨?_, (hv u hu').2⟩⟩
  have h1 := hmin hu'
  simp only [mem_ofPred_eq] at h1
  have h2 := sq_pos_of_neg (hv u hu').2
  rw [le_div_iff₀ h2] at h1
  linarith

/-- A curve of class `C¹` on `[a, b]` is locally Lipschitz there. -/
theorem isLocallyLipschitzOn_of_contMDiffOn {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) : IsLocallyLipschitzOn (I := I) γ (Icc a b) := by
  intro t ht
  have hW : γ ⁻¹' (extChartAt I (γ t)).source ∈ 𝓝[Icc a b] t :=
    (hγ.continuousOn t ht).preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (γ t))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hW
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by positivity
  set J : Set ℝ := Icc (max a (t - r)) (min b (t + r)) with hJ
  have hJle : max a (t - r) ≤ min b (t + r) :=
    max_le_iff.2 ⟨le_min hab.le (by linarith [ht.1]), le_min (by linarith [ht.2]) (by linarith)⟩
  have hJlt : max a (t - r) < min b (t + r) :=
    max_lt_iff.2 ⟨lt_min hab (by linarith [ht.1]), lt_min (by linarith [ht.2]) (by linarith)⟩
  have hJsub : J ⊆ Icc a b := fun y hy ↦
    ⟨(le_max_left _ _).trans hy.1, hy.2.trans (min_le_left _ _)⟩
  have hJW : J ⊆ γ ⁻¹' (extChartAt I (γ t)).source := fun y hy ↦ by
    refine hsub ⟨?_, hJsub hy⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [(le_max_right _ _).trans hy.1]
    · linarith [hy.2.trans (min_le_right _ _)]
  have hcd : ContDiffOn ℝ 1 ((extChartAt I (γ t)) ∘ γ) J := by
    have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((extChartAt I (γ t)) ∘ γ) J :=
      (contMDiffOn_extChartAt (I := I) (x := γ t)).comp (hγ.mono hJsub) (by simpa [extChartAt_source] using hJW)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hU := uniqueDiffOn_Icc hJlt
  have hcont := hcd.continuousOn_fderivWithin hU le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := max a (t - r)) (b := min b (t + r))).exists_bound_of_continuousOn
    hcont
  refine ⟨⟨max C 0, le_max_right _ _⟩, J, ?_, hJW, ?_⟩
  · refine mem_nhdsWithin.2 ⟨Ioo (t - r) (t + r), isOpen_Ioo, ⟨by linarith, by linarith⟩,
      fun y hy ↦ ⟨max_le_iff.2 ⟨hy.2.1, hy.1.1.le⟩, le_min hy.2.2 hy.1.2.le⟩⟩
  · refine (convex_Icc _ _).lipschitzOnWith_of_nnnorm_fderivWithin_le
      (hcd.differentiableOn one_ne_zero) ?_
    intro x hx
    have := hC x hx
    show ((‖_‖₊ : NNReal) : ℝ) ≤ max C 0
    rw [coe_nnnorm]
    exact this.trans (le_max_left _ _)

/-- **A `C¹` future-directed timelike curve on `[a, b]` is a future-directed timelike curve in the
sense of `IsFutureTimelikeCurve`** (it has a margin): the textbook curves are included. -/
theorem isFutureTimelikeCurve_of_contMDiffOn {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hv : ∀ t ∈ Icc a b, T.IsFutureTimelike (velocity I γ (Icc a b) t)) :
    IsFutureTimelikeCurve T γ (Icc a b) := by
  obtain ⟨ε, hε, hm⟩ := exists_margin_of_contMDiffOn T hab hγ hv
  refine isFutureTimelikeCurve_of_margin T hε ⟨ordConnected_Icc,
    isLocallyLipschitzOn_of_contMDiffOn hab hγ, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact ⟨(hγ t ht).mdifferentiableWithinAt one_ne_zero, hm t ht⟩

end Causal

end Lightlike
