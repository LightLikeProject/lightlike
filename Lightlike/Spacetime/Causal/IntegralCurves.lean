import Lightlike.Spacetime.Causal.CurveGlobal
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.SmoothOrientation
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform

/-!
# Maximal integral curves have no endpoint

For a `C¹` vector field `Y` without zeros on a Hausdorff manifold without boundary, the maximal
integral curve through a point has no future endpoint (`curveMax_not_hasFutureEndpoint`): a limit
point at a finite end of the interval would let the curve be continued (the chart expression has
the derivative `chartVel`, which is continuous, so the continued curve is an integral curve), and a
limit point at infinity is impossible because the chart expression moves with speed close to
`‖chartVel p Y p‖ > 0`. This is the escape lemma, here in the form needed for causal curves.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The vector `Y q` in the coordinates of the chart at `p`. -/
def chartVel (p : M) (Y : (x : M) → TangentSpace I x) (q : M) : E :=
  mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (Y q)

/-- **An integral curve in a chart** has the derivative `chartVel`. -/
theorem hasDerivAt_chart_comp {p : M} {Y : (x : M) → TangentSpace I x} {c : ℝ → M} {t : ℝ}
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (c t))))
    (hq : c t ∈ (extChartAt I p).source) :
    HasDerivAt (extChartAt I p ∘ c) (chartVel p Y (c t)) t := by
  have hφ : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) (c t) :=
    (contMDiffAt_extChartAt' (I := I) (n := 1)
      (by rw [extChartAt_source] at hq; exact hq)).mdifferentiableAt one_ne_zero
  have h1 := hφ.hasMFDerivAt.comp t hc
  rw [hasMFDerivAt_iff_hasFDerivAt] at h1
  have h2 := (hasFDerivAt_iff_hasDerivAt (𝕜 := ℝ) (F := E)).1 h1
  refine h2.congr_deriv ?_
  unfold chartVel
  refine congrArg (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (c t)) ?_
  simp
  exact one_smul ℝ (Y (c t))

/-- `chartVel` is the coordinate of the trivialization of the tangent bundle at `p`. -/
theorem chartVel_eq {p q : M} (Y : (x : M) → TangentSpace I x) (hq : q ∈ (chartAt H p).source) :
    chartVel p Y q = (tTriv I M p ⟨q, Y q⟩).2 := by
  have h1 := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hq
  have h2 := Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (tTriv I M p) (R := ℝ) (show q ∈ (tTriv I M p).baseSet from hq) (Y q)
  rw [h1] at h2
  exact h2

/-- `chartVel` is continuous on the chart domain for a continuous vector field. -/
theorem continuousOn_chartVel {p : M} {Y : (x : M) → TangentSpace I x}
    (hY : Continuous fun x => (⟨x, Y x⟩ : TangentBundle I M)) :
    ContinuousOn (chartVel p Y) (chartAt H p).source := by
  have h := ((tTriv I M p).continuousOn.comp hY.continuousOn
    (fun x hx => (tTriv I M p).mem_source.2 hx)).snd
  exact h.congr fun q hq => chartVel_eq Y hq

/-- `chartVel` of a nonvanishing field is nonzero. -/
theorem chartVel_ne_zero {p q : M} {Y : (x : M) → TangentSpace I x} (hY0 : Y q ≠ 0)
    (hq : q ∈ (chartAt H p).source) : chartVel p Y q ≠ 0 := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt (I := I) (x := p) (y := q)
    (by rwa [extChartAt_source])
  intro h0
  apply hY0
  apply L.injective
  rw [map_zero]
  have : L (Y q) = mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (Y q) := by rw [← hL]; rfl
  rw [this]
  exact h0

/-- **A curve is an integral curve at `t₀` if it is continuous there and its chart expression has
the chart expression of `Y` as derivative.** -/
theorem hasMFDerivAt_of_chart {G : ℝ → M} {t₀ : ℝ} {Y : (x : M) → TangentSpace I x}
    (hc : ContinuousAt G t₀)
    (hd : HasDerivAt (extChartAt I (G t₀) ∘ G) (chartVel (G t₀) Y (G t₀)) t₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I G t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (G t₀))) := by
  refine ⟨hc, ?_⟩
  simp only [writtenInExtChartAt, mfld_simps]
  have hv : chartVel (G t₀) Y (G t₀) = Y (G t₀) := by
    unfold chartVel
    rw [mfderiv_extChartAt_self]
    rfl
  rw [hv] at hd
  have h2 := (hd.hasFDerivAt).hasFDerivWithinAt (s := (univ : Set ℝ))
  exact h2

/-- **Gluing an integral curve that converges to `p` at `t₀` to an integral curve through `p`**:
the glued curve is an integral curve at `t₀`, since the derivative of its chart expression is
`chartVel p Y`, which is continuous. -/
theorem hasMFDerivAt_glue {Y : (x : M) → TangentSpace I x}
    (hYc : Continuous fun x => (⟨x, Y x⟩ : TangentBundle I M)) {c ψ : ℝ → M} {t₀ ε : ℝ} {p : M}
    (hε : 0 < ε)
    (hc : ∀ t ∈ Ioo (t₀ - ε) t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (c t))))
    (hψ : HasMFDerivAt 𝓘(ℝ, ℝ) I ψ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (ψ 0)))) (hψ0 : ψ 0 = p)
    (hlim : Tendsto c (𝓝[<] t₀) (𝓝 p)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => if t < t₀ then c t else ψ (t - t₀)) t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (Y ((fun t => if t < t₀ then c t else ψ (t - t₀)) t₀))) := by
  set G : ℝ → M := fun t => if t < t₀ then c t else ψ (t - t₀) with hG
  have hGt₀ : G t₀ = p := by simp [hG, hψ0]
  have hGl : ∀ t, t < t₀ → G t = c t := fun t ht => by simp [hG, ht]
  have hGr : ∀ t, t₀ ≤ t → G t = ψ (t - t₀) := fun t ht => by simp [hG, not_lt.2 ht]
  -- continuity
  have hψc : ContinuousAt ψ 0 := hψ.continuousAt
  have hcontR : ContinuousWithinAt G (Ici t₀) t₀ := by
    have : ContinuousWithinAt (fun t => ψ (t - t₀)) (Ici t₀) t₀ :=
      (hψc.comp_of_eq (f := fun t : ℝ => t - t₀) (by fun_prop) (by simp)).continuousWithinAt
    refine this.congr (fun t ht => hGr t ht) (hGr t₀ le_rfl)
  have hcontL : ContinuousWithinAt G (Iio t₀) t₀ := by
    rw [ContinuousWithinAt, hGt₀]
    exact hlim.congr' (eventually_nhdsWithin_of_forall fun t ht => (hGl t ht).symm)
  have hGc : ContinuousAt G t₀ := by
    exact continuousAt_iff_continuous_left_right.2 ⟨continuousWithinAt_Iio_iff_Iic.1 hcontL, hcontR⟩
  have hsrc : ∀ᶠ t in 𝓝[<] t₀, c t ∈ (chartAt H p).source :=
    hlim.eventually ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  have hcv : ContinuousAt (chartVel p Y) p :=
    (continuousOn_chartVel hYc).continuousAt ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  have hdG : HasDerivAt (extChartAt I (G t₀) ∘ G) (chartVel (G t₀) Y (G t₀)) t₀ := by
    rw [hGt₀]
    -- right derivative
    have hpsrc : ψ 0 ∈ (extChartAt I p).source := by rw [hψ0]; exact mem_extChartAt_source p
    have hR : HasDerivWithinAt (extChartAt I p ∘ G) (chartVel p Y p) (Ici t₀) t₀ := by
      have h1 := hasDerivAt_chart_comp (p := p) hψ hpsrc
      rw [hψ0] at h1
      have h2 : HasDerivAt (fun t : ℝ => (extChartAt I p ∘ ψ) (t - t₀)) (chartVel p Y p) t₀ :=
        HasDerivAt.comp_sub_const t₀ t₀ (by simpa using h1)
      refine h2.hasDerivWithinAt.congr (fun t ht => ?_) ?_
      · simp [Function.comp, hGr t ht]
      · simp [Function.comp, hGr t₀ le_rfl]
    -- left derivative
    have hφ : ContinuousAt (extChartAt I p) (G t₀) := by rw [hGt₀]; exact continuousAt_extChartAt p
    have hsmem : {t | t ∈ Ioo (t₀ - ε) t₀ ∧ c t ∈ (chartAt H p).source} ∈ 𝓝[<] t₀ := by
      filter_upwards [Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith), hsrc] with t ht1 ht2
      exact ⟨ht1, ht2⟩
    have hderiv : ∀ t ∈ {t | t ∈ Ioo (t₀ - ε) t₀ ∧ c t ∈ (chartAt H p).source},
        HasDerivAt (extChartAt I p ∘ G) (chartVel p Y (c t)) t := by
      intro t ht
      have h1 := hasDerivAt_chart_comp (p := p) (hc t ht.1) (by rw [extChartAt_source]; exact ht.2)
      have hev : G =ᶠ[𝓝 t] c := Filter.mem_of_superset (Iio_mem_nhds ht.1.2) fun r hr => hGl r hr
      exact h1.congr_of_eventuallyEq (hev.fun_comp _)
    have hL : HasDerivWithinAt (extChartAt I p ∘ G) (chartVel p Y p) (Iic t₀) t₀ := by
      refine hasDerivWithinAt_Iic_of_tendsto_deriv
        (s := {t | t ∈ Ioo (t₀ - ε) t₀ ∧ c t ∈ (chartAt H p).source}) ?_ ?_ hsmem ?_
      · exact fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
      · exact hφ.comp_continuousWithinAt hGc.continuousWithinAt
      · refine (hcv.tendsto.comp hlim).congr' ?_
        filter_upwards [hsmem] with t ht
        exact ((hderiv t ht).deriv).symm
    have hu : Iic t₀ ∪ Ici t₀ = (univ : Set ℝ) := by ext x; simp
    rw [← hasDerivWithinAt_univ, ← hu]
    exact hL.union hR
  exact hasMFDerivAt_of_chart hGc hdG

section Maximal

variable [T2Space M] [BoundarylessManifold I M] [CompleteSpace E]
  {Y : (x : M) → TangentSpace I x}

/-- `c` is an integral curve of `Y` through `y` at time `0`, on `(a, b) ∋ 0`. -/
def IsIC (Y : (x : M) → TangentSpace I x) (y : M) (a b : ℝ) (c : ℝ → M) : Prop :=
  a < 0 ∧ 0 < b ∧ c 0 = y ∧ IsMIntegralCurveOn c Y (Ioo a b)

omit [CompleteSpace E] in
/-- Two integral curves through the same point agree on the common interval. -/
theorem IsIC.eqOn (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y : M} {a b a' b' : ℝ}
    {c c' : ℝ → M} (h : IsIC Y y a b c) (h' : IsIC Y y a' b' c') :
    EqOn c c' (Ioo (max a a') (min b b')) :=
  isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) ⟨max_lt h.1 h'.1, lt_min h.2.1 h'.2.1⟩ hY
    (h.2.2.2.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
    (h'.2.2.2.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
    (h.2.2.1.trans h'.2.2.1.symm)

/-- Every point has an integral curve through it. -/
theorem exists_isIC (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y : M) :
    ∃ a b c, IsIC Y y a b c := by
  obtain ⟨c, hc0, hc⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (t₀ := 0)
    (x₀ := y) (hY.contMDiffAt)
  obtain ⟨ε, hε, hε'⟩ := isMIntegralCurveAt_iff'.1 hc
  have : Ioo (-ε) ε = Metric.ball (0 : ℝ) ε := by rw [Real.ball_eq_Ioo]; simp
  exact ⟨-ε, ε, c, by linarith, hε, hc0, this ▸ hε'⟩

/-- The union of the intervals of all integral curves through `y`. -/
def domMax (Y : (x : M) → TangentSpace I x) (y : M) : Set ℝ :=
  {t | ∃ a b c, IsIC Y y a b c ∧ t ∈ Ioo a b}

open Classical in
/-- The maximal integral curve through `y` (the value of any integral curve through `y` whose
interval contains `t`). -/
def curveMax (Y : (x : M) → TangentSpace I x) (y : M) (t : ℝ) : M :=
  if h : ∃ c a b, IsIC Y y a b c ∧ t ∈ Ioo a b then Classical.choose h t else y

theorem curveMax_eq (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {y : M}
    {a b : ℝ} {c : ℝ → M} (h : IsIC Y y a b c) {t : ℝ} (ht : t ∈ Ioo a b) :
    curveMax Y y t = c t := by
  have hex : ∃ c a b, IsIC Y y a b c ∧ t ∈ Ioo a b := ⟨c, a, b, h, ht⟩
  rw [curveMax, dite_eq_left hex]
  obtain ⟨a', b', h', ht'⟩ := (Classical.choose_spec hex)
  exact (h'.eqOn hY h) ⟨max_lt ht'.1 ht.1, lt_min ht'.2 ht.2⟩

theorem isOpen_domMax (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y : M) :
    IsOpen (domMax Y y) := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a, b, c, h, ht⟩
  exact mem_of_superset (Ioo_mem_nhds ht.1 ht.2) fun r hr => ⟨a, b, c, h, hr⟩

theorem zero_mem_domMax (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y : M) :
    0 ∈ domMax Y y := by
  obtain ⟨a, b, c, h⟩ := exists_isIC hY y
  exact ⟨a, b, c, h, h.1, h.2.1⟩

theorem ordConnected_domMax (y : M) : (domMax Y y).OrdConnected := by
  refine ⟨fun s hs t ht r hr => ?_⟩
  obtain ⟨a, b, c, h, hsab⟩ := hs
  obtain ⟨a', b', c', h', htab⟩ := ht
  rcases le_total r 0 with hr0 | hr0
  · exact ⟨a, b, c, h, ⟨lt_of_lt_of_le hsab.1 hr.1, lt_of_le_of_lt hr0 h.2.1⟩⟩
  · exact ⟨a', b', c', h', ⟨lt_of_lt_of_le h'.1 hr0, lt_of_le_of_lt hr.2 htab.2⟩⟩


theorem isMIntegralCurveOn_curveMax (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (y : M) : IsMIntegralCurveOn (curveMax Y y) Y (domMax Y y) := by
  intro t ⟨a, b, c, h, htab⟩
  have hmem : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds htab.1 htab.2
  have h1 := (h.2.2.2 t htab).hasMFDerivAt hmem
  have hev : curveMax Y y =ᶠ[𝓝 t] c :=
    mem_of_superset hmem fun r hr => curveMax_eq hY h hr
  have h2 := h1.congr_of_eventuallyEq hev
  have e : curveMax Y y t = c t := curveMax_eq hY h htab
  rw [e]
  exact h2.hasMFDerivWithinAt

theorem curveMax_zero (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) (y : M) :
    curveMax Y y 0 = y := by
  obtain ⟨a, b, c, h⟩ := exists_isIC hY y
  rw [curveMax_eq hY h ⟨h.1, h.2.1⟩]
  exact h.2.2.1

omit [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] in
theorem hasMFDerivAt_of_eventuallyEq {c G : ℝ → M} {t : ℝ} (hev : G =ᶠ[𝓝 t] c)
    (h : HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (c t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I G t ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (G t))) := by
  have e : G t = c t := hev.self_of_nhds
  have h2 := h.congr_of_eventuallyEq hev
  rw [e]
  exact h2

/-- **The bounded case of the escape lemma**: a maximal integral curve cannot converge to a point
at a finite end of its interval. -/
theorem false_of_limit_finite (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hYc : Continuous fun x => (⟨x, Y x⟩ : TangentBundle I M)) {y : M} {w₁ : ℝ} (hw₁ : 0 < w₁)
    (hD : Ico 0 w₁ ⊆ domMax Y y) (hw₁D : w₁ ∉ domMax Y y) {p : M}
    (hlim : Tendsto (curveMax Y y) (𝓝[<] w₁) (𝓝 p)) : False := by
  obtain ⟨a0, b0, ψ, hψ⟩ := exists_isIC hY p
  obtain ⟨a1, b1, c1, h1⟩ := exists_isIC hY y
  set G : ℝ → M := fun t => if t < w₁ then curveMax Y y t else ψ (t - w₁) with hG
  have hGl : ∀ t, t < w₁ → G t = curveMax Y y t := fun t ht => by simp [hG, ht]
  have hGr : ∀ t, w₁ ≤ t → G t = ψ (t - w₁) := fun t ht => by simp [hG, not_lt.2 ht]
  have hGIC : IsIC Y y a1 (w₁ + b0) G := by
    refine ⟨h1.1, by linarith [hψ.2.1], ?_, ?_⟩
    · rw [hGl 0 hw₁, curveMax_zero hY]
    · intro t ht
      refine HasMFDerivAt.hasMFDerivWithinAt ?_
      rcases lt_trichotomy t w₁ with htw | htw | htw
      · have htD : t ∈ domMax Y y := by
          by_cases h0 : 0 ≤ t
          · exact hD ⟨h0, htw⟩
          · exact ⟨a1, b1, c1, h1, ht.1, by linarith [h1.2.1]⟩
        have hcm := (isMIntegralCurveOn_curveMax hY y t htD).hasMFDerivAt
          ((isOpen_domMax hY y).mem_nhds htD)
        exact hasMFDerivAt_of_eventuallyEq
          (Filter.mem_of_superset (Iio_mem_nhds htw) fun r hr => hGl r hr) hcm
      · subst htw
        refine hasMFDerivAt_glue hYc (ε := t) hw₁ ?_ ?_ hψ.2.2.1 hlim
        · intro r hr
          have hrD : r ∈ domMax Y y := hD ⟨by linarith [hr.1], hr.2⟩
          exact (isMIntegralCurveOn_curveMax hY y r hrD).hasMFDerivAt
            ((isOpen_domMax hY y).mem_nhds hrD)
        · have := hψ.2.2.2 0 ⟨hψ.1, hψ.2.1⟩
          exact this.hasMFDerivAt (Ioo_mem_nhds hψ.1 hψ.2.1)
      · have hmem : t - w₁ ∈ Ioo a0 b0 := ⟨by linarith [hψ.1], by linarith [ht.2]⟩
        have hsh := (isMIntegralCurveOn_comp_sub (dt := w₁)).2 hψ.2.2.2
        have hopen : IsOpen {r : ℝ | r - w₁ ∈ Ioo a0 b0} :=
          isOpen_Ioo.preimage (continuous_sub_right w₁)
        have h2 := (hsh t hmem).hasMFDerivAt (hopen.mem_nhds hmem)
        exact hasMFDerivAt_of_eventuallyEq
          (Filter.mem_of_superset (Ioi_mem_nhds htw) fun r hr => hGr r hr.le) h2
  exact hw₁D ⟨a1, w₁ + b0, G, hGIC, ⟨by linarith [hGIC.1, hw₁], by linarith [hψ.2.1]⟩⟩


omit [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] in
/-- **The unbounded case of the escape lemma**: an integral curve of a continuous field that does
not vanish at `p` cannot converge to `p` as `t → ∞`: its chart expression moves with speed close to
`‖chartVel p Y p‖ > 0`. -/
theorem false_of_limit_atTop {Y : (x : M) → TangentSpace I x}
    (hYc : Continuous fun x => (⟨x, Y x⟩ : TangentBundle I M)) {p : M} (hY0 : Y p ≠ 0)
    {c : ℝ → M} {T : ℝ}
    (hc : ∀ t, T ≤ t → HasMFDerivAt 𝓘(ℝ, ℝ) I c t ((1 : ℝ →L[ℝ] ℝ).smulRight (Y (c t))))
    (hlim : ∀ U ∈ 𝓝 p, ∃ T₀, T ≤ T₀ ∧ ∀ t, T₀ ≤ t → c t ∈ U) : False := by
  set w : E := chartVel p Y p with hw
  have hw0 : w ≠ 0 := chartVel_ne_zero hY0 (mem_chart_source H p)
  set N : ℝ := ‖w‖ with hN
  have hNpos : 0 < N := norm_pos_iff.2 hw0
  have hsrc : (chartAt H p).source ∈ 𝓝 p := (chartAt H p).open_source.mem_nhds (mem_chart_source H p)
  have hcv : ContinuousAt (chartVel p Y) p := (continuousOn_chartVel hYc).continuousAt hsrc
  have hφ : ContinuousAt (extChartAt I p) p := continuousAt_extChartAt p
  have hev : ∀ᶠ q in 𝓝 p, q ∈ (chartAt H p).source ∧ dist (chartVel p Y q) w < N / 4 ∧
      dist (extChartAt I p q) (extChartAt I p p) < N / 8 :=
    (show ∀ᶠ q in 𝓝 p, q ∈ (chartAt H p).source from hsrc).and ((hcv.tendsto.eventually (Metric.ball_mem_nhds w (by positivity))).and
      (hφ.tendsto.eventually (Metric.ball_mem_nhds _ (by positivity))))
  obtain ⟨T₀, hT₀, hT₀'⟩ := hlim _ hev
  set f : ℝ → E := extChartAt I p ∘ c with hf
  have hder : ∀ t, T₀ ≤ t → HasDerivAt f (chartVel p Y (c t)) t := fun t ht =>
    hasDerivAt_chart_comp (hc t (hT₀.trans ht)) (by rw [extChartAt_source]; exact (hT₀' t ht).1)
  have hg : ∀ x ∈ Icc T₀ (T₀ + 1), HasDerivWithinAt (fun s => f s - s • w)
      (chartVel p Y (c x) - w) (Icc T₀ (T₀ + 1)) x := by
    intro x hx
    have h := (hder x hx.1).sub ((hasDerivAt_id x).smul_const w)
    have h' : HasDerivAt (fun s => f s - s • w) (chartVel p Y (c x) - w) x := by
      convert h using 1 <;> simp [Pi.sub_def]
    exact h'.hasDerivWithinAt
  have hb : ∀ x ∈ Ico T₀ (T₀ + 1), ‖chartVel p Y (c x) - w‖ ≤ N / 4 := fun x hx => by
    have := (hT₀' x hx.1).2.1
    rw [dist_eq_norm] at this
    exact this.le
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' hg hb (T₀ + 1)
    ⟨by linarith, le_rfl⟩
  simp only [add_sub_cancel_left, mul_one] at hmain
  have h1 := (hT₀' (T₀ + 1) (by linarith)).2.2
  have h2 := (hT₀' T₀ le_rfl).2.2
  rw [dist_eq_norm] at h1 h2
  have h3 : ‖f (T₀ + 1) - f T₀‖ < N / 4 := by
    calc ‖f (T₀ + 1) - f T₀‖ = ‖(f (T₀ + 1) - extChartAt I p p) - (f T₀ - extChartAt I p p)‖ := by
          congr 1; abel
      _ ≤ ‖f (T₀ + 1) - extChartAt I p p‖ + ‖f T₀ - extChartAt I p p‖ := norm_sub_le _ _
      _ < N / 8 + N / 8 := add_lt_add h1 h2
      _ = N / 4 := by ring
  have h4 : ‖f (T₀ + 1) - f T₀ - w‖ ≤ N / 4 := by
    have : f (T₀ + 1) - (T₀ + 1) • w - (f T₀ - T₀ • w) = f (T₀ + 1) - f T₀ - w := by
      simp only [add_smul, one_smul]; abel
    rw [← this]; exact hmain
  have h5 : N ≤ ‖f (T₀ + 1) - f T₀‖ + ‖f (T₀ + 1) - f T₀ - w‖ := by
    calc N = ‖w‖ := rfl
      _ = ‖(f (T₀ + 1) - f T₀) - (f (T₀ + 1) - f T₀ - w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- **A maximal integral curve of a nowhere vanishing field has no future endpoint.** -/
theorem curveMax_not_hasFutureEndpoint (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hY0 : ∀ x, Y x ≠ 0) (y : M) (p : M) :
    ¬ HasFutureEndpoint (curveMax Y y) (domMax Y y ∩ Ici 0) p := by
  have hYc : Continuous fun x => (⟨x, Y x⟩ : TangentBundle I M) := hY.continuous
  intro hp
  have h0 := zero_mem_domMax hY y
  have hopen := isOpen_domMax hY y
  by_cases hb : BddAbove (domMax Y y)
  · set w₁ := sSup (domMax Y y) with hw₁
    have hle : ∀ t ∈ domMax Y y, t ≤ w₁ := fun t ht => le_csSup hb ht
    have hwD : w₁ ∉ domMax Y y := by
      intro hmem
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen w₁ hmem
      have : w₁ + ε / 2 ∈ domMax Y y := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      linarith [hle _ this]
    have hw0 : 0 < w₁ := lt_of_le_of_ne (hle 0 h0) (fun h => hwD (h ▸ h0))
    have hsub : Ico 0 w₁ ⊆ domMax Y y := by
      intro t ht
      obtain ⟨d, hd, htd⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ ht.2
      exact (ordConnected_domMax (Y := Y) y).out h0 hd ⟨ht.1, htd.le⟩
    have hlim : Tendsto (curveMax Y y) (𝓝[<] w₁) (𝓝 p) := by
      rw [tendsto_def]
      intro U hU
      obtain ⟨c0, hc0, hc⟩ := hp U hU
      have hc0lt : c0 < w₁ := lt_of_le_of_ne (hle _ hc0.1) (fun h => hwD (h ▸ hc0.1))
      refine mem_of_superset (Ioo_mem_nhdsLT hc0lt) fun t ht => ?_
      exact hc t ⟨hsub ⟨hc0.2.trans ht.1.le, ht.2⟩, hc0.2.trans ht.1.le⟩ ht.1.le
    exact false_of_limit_finite hY hYc hw0 hsub hwD hlim
  · have hall : ∀ t, 0 ≤ t → t ∈ domMax Y y := by
      intro t ht
      obtain ⟨d, hd, htd⟩ := not_bddAbove_iff.1 hb t
      exact (ordConnected_domMax (Y := Y) y).out h0 hd ⟨ht, htd.le⟩
    refine false_of_limit_atTop hYc (hY0 p) (c := curveMax Y y) (T := 0) ?_ ?_
    · intro t ht
      exact (isMIntegralCurveOn_curveMax hY y t (hall t ht)).hasMFDerivAt
        (hopen.mem_nhds (hall t ht))
    · intro U hU
      obtain ⟨c0, hc0, hc⟩ := hp U hU
      exact ⟨c0, hc0.2, fun t ht => hc t ⟨hall t (hc0.2.trans ht), hc0.2.trans ht⟩ ht⟩

end Maximal

end Causal

end Lightlike
