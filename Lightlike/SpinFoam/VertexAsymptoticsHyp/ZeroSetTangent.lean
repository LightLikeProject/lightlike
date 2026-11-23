import Mathlib.Analysis.Calculus.TangentCone.Seq
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Order.IntermediateValue

/-!
# The kernel of the derivative lies in the tangent cone of a zero set (SF10, P2 defect)

If a real function `F` has a nonzero derivative `L` at a zero `a` and is continuous near `a`, then
every direction `u` in `ker L` is a tangent direction of the zero set `{F = 0}` at `a`.  The
proof is an intermediate value argument along the transversal direction `v` (`L v = 1`): the points
`a + t (u + σ v)` change the sign of `F` as `σ` runs over `[-δ, δ]`, for `t` small.

This is the geometric step that makes the branch cut `{Im f = 0, Re f < 0}` of `Complex.log∘f`
a hypersurface with a full hyperplane of tangent directions (used with `CutRank`).
Supporting lemmas only.
-/

open Filter Topology Set

namespace Lightlike.SpinFoam.ZeroSetTangent

/-- A function with positive derivative at a zero is positive just to the right. -/
theorem eventually_pos_of_hasDerivAt {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0) (g0 : g 0 = 0)
    (hd : 0 < d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := by
  have h := (hasDerivWithinAt_iff_tendsto_slope.1 (hg.hasDerivWithinAt (s := Ioi 0)))
  have h' : Tendsto (slope g 0) (𝓝[Ioi 0 \ {0}] (0 : ℝ)) (𝓝 d) := h
  have hs : Ioi (0 : ℝ) \ {0} = Ioi 0 :=
    Set.ext fun x => ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
  rw [hs] at h'
  filter_upwards [h'.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, g0, sub_zero, sub_zero] at ht
  exact (div_pos_iff_of_pos_right (mem_Ioi.1 ht0)).1 ht

/-- Sign of `F` along a ray in a direction on which `L` is positive. -/
theorem eventually_pos_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {L : E →L[ℝ] ℝ} {a : E} (hF : HasFDerivAt F L a) (hFa : F a = 0) {w : E} (hw : 0 < L w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < F (a + t • w) := by
  have hl : HasDerivAt (fun t : ℝ => a + t • w) w 0 := by
    simpa using HasDerivAt.const_add a (HasDerivAt.smul_const (hasDerivAt_id' (0 : ℝ)) w)
  have hF' : HasFDerivAt F L (a + (0 : ℝ) • w) := by simpa using hF
  have := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF' hl
  exact eventually_pos_of_hasDerivAt this (by simpa using hFa) hw

/-- Sign of `F` along a ray in a direction on which `L` is negative. -/
theorem eventually_neg_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {L : E →L[ℝ] ℝ} {a : E} (hF : HasFDerivAt F L a) (hFa : F a = 0) {w : E} (hw : L w < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), F (a + t • w) < 0 := by
  have hF' : HasFDerivAt (fun y => -F y) (-L) a := hF.neg
  have := eventually_pos_ray hF' (by simpa using hFa) (w := w) (by simpa using hw)
  filter_upwards [this] with t ht
  simpa using ht

/-- Intermediate-value step: for each `δ > 0` and small `t > 0` the segment
`σ ↦ a + t (u + σ v)`, `|σ| ≤ δ`, meets `{F = 0}`. -/
theorem eventually_exists_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {L : E →L[ℝ] ℝ} {a : E} (hF : HasFDerivAt F L a) (hFa : F a = 0)
    (hc : ∀ᶠ y in 𝓝 a, ContinuousAt F y) {u v : E} (hu : L u = 0) (hv : L v = 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ σ : ℝ, |σ| ≤ δ ∧ F (a + t • (u + σ • v)) = 0 := by
  have hp : 0 < L (u + δ • v) := by simp [hu, hv, hδ]
  have hn : L (u + (-δ) • v) < 0 := by simp [hu, hv, hδ]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hc
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r / (‖u‖ + δ * ‖v‖ + 1) := by
    apply eventually_nhdsWithin_of_eventually_nhds
    exact (gt_mem_nhds (by positivity))
  filter_upwards [eventually_pos_ray hF hFa hp, eventually_neg_ray hF hFa hn, hsmall,
    self_mem_nhdsWithin] with t h1 h2 h3 h4
  have ht : 0 < t := h4
  have hcont : ContinuousOn (fun σ : ℝ => F (a + t • (u + σ • v))) (Icc (-δ) δ) := by
    intro σ hσ
    have hσ' : |σ| ≤ δ := abs_le.2 ⟨hσ.1, hσ.2⟩
    have hmem : a + t • (u + σ • v) ∈ Metric.ball a r := by
      rw [mem_ball_iff_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hn1 : ‖u + σ • v‖ ≤ ‖u‖ + δ * ‖v‖ := by
        calc ‖u + σ • v‖ ≤ ‖u‖ + ‖σ • v‖ := norm_add_le _ _
          _ ≤ ‖u‖ + δ * ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            gcongr
      have hpos : 0 < ‖u‖ + δ * ‖v‖ + 1 := by positivity
      have : t * (‖u‖ + δ * ‖v‖ + 1) < r := by
        rwa [lt_div_iff₀ hpos] at h3
      calc t * ‖u + σ • v‖ ≤ t * (‖u‖ + δ * ‖v‖) := by gcongr
        _ < t * (‖u‖ + δ * ‖v‖ + 1) := by nlinarith
        _ < r := this
    have hca : ContinuousAt F (a + t • (u + σ • v)) := hball _ hmem
    have hlin : Continuous (fun σ : ℝ => a + t • (u + σ • v)) := by fun_prop
    exact (hca.comp_of_eq hlin.continuousAt rfl).continuousWithinAt
  have hle : (-δ) ≤ δ := by linarith
  have h2' : F (a + t • (u + (-δ) • v)) ≤ 0 := h2.le
  have h1' : 0 ≤ F (a + t • (u + δ • v)) := h1.le
  obtain ⟨σ, hσ, hz⟩ := intermediate_value_Icc hle hcont ⟨by simpa using h2', by simpa using h1'⟩
  exact ⟨σ, abs_le.2 ⟨hσ.1, hσ.2⟩, by simpa using hz⟩

/-- **Kernel in the tangent cone**: if `F a = 0`, `F` has nonzero derivative `L` at `a` and is
continuous near `a`, then `ker L ⊆ tangentConeAt ℝ {F = 0} a`. -/
theorem ker_subset_tangentCone_zeroSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {L : E →L[ℝ] ℝ} {a : E} (hF : HasFDerivAt F L a) (hFa : F a = 0)
    (hc : ∀ᶠ y in 𝓝 a, ContinuousAt F y) (hL : L ≠ 0) {u : E} (hu : L u = 0) :
    u ∈ tangentConeAt ℝ {y | F y = 0} a := by
  obtain ⟨w0, hw0⟩ : ∃ w, L w ≠ 0 := by
    by_contra h
    exact hL (ContinuousLinearMap.ext fun x => not_not.1 (not_exists.1 h x))
  set v : E := (L w0)⁻¹ • w0 with hvdef
  have hv : L v = 1 := by simp [hvdef, hw0]
  -- thresholds for δ = 1/(m+1)
  have hex : ∀ m : ℕ, ∃ T : ℝ, 0 < T ∧ T ≤ 1 / ((m : ℝ) + 1) ∧ ∀ t ∈ Ioo (0 : ℝ) T,
      ∃ σ : ℝ, |σ| ≤ 1 / ((m : ℝ) + 1) ∧ F (a + t • (u + σ • v)) = 0 := by
    intro m
    have hδ : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have := eventually_exists_zero hF hFa hc hu hv hδ
    obtain ⟨T, hT, hTs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 this
    refine ⟨min T (1 / ((m : ℝ) + 1)), lt_min hT hδ, min_le_right _ _, fun t ht => ?_⟩
    exact hTs ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  choose T hT0 hT1 hT2 using hex
  have hpick : ∀ m : ℕ, ∃ σ : ℝ, |σ| ≤ 1 / ((m : ℝ) + 1) ∧
      F (a + (T m / 2) • (u + σ • v)) = 0 := fun m =>
    hT2 m (T m / 2) ⟨by linarith [hT0 m], by linarith [hT0 m]⟩
  choose σ hσ1 hσ2 using hpick
  have hT_tend : Tendsto (fun m : ℕ => T m / 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun m => by linarith [hT0 m]) (fun m => ?_) h1
    linarith [hT1 m, hT0 m]
  have hσ_tend : Tendsto σ atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact squeeze_zero_norm (fun m => by simpa using hσ1 m) h1
  have hw_tend : Tendsto (fun m => u + σ m • v) atTop (𝓝 u) := by
    simpa using tendsto_const_nhds.add (hσ_tend.smul_const v)
  refine mem_tangentConeAt_of_seq atTop (fun m => (T m / 2)⁻¹)
    (fun m => (T m / 2) • (u + σ m • v)) ?_ ?_ ?_
  · simpa using hT_tend.smul hw_tend
  · exact Eventually.of_forall fun m => hσ2 m
  · refine hw_tend.congr fun m => ?_
    have : (T m / 2) ≠ 0 := by linarith [hT0 m]
    exact (inv_smul_smul₀ this (u + σ m • v)).symm

end Lightlike.SpinFoam.ZeroSetTangent
