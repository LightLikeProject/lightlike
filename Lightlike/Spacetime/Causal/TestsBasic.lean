import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.MinkowskiCauchy
import Lightlike.Spacetime.Causal.Extension
import Lightlike.Spacetime.Causal.CauchyCover
import Lightlike.Spacetime.Causal.MinkowskiGH
import Lightlike.Spacetime.Causal.SmoothOrientation
import Lightlike.Spacetime.Causal.TestsMinkowski

/-!
# Checks of the basic causal relations on Minkowski space

Non-vacuity of the transitivity statements of `Lightlike/Spacetime/Causal/BasicRelations.lean`: two
timelike steps of Minkowski space `ℝ^{d+1}` are glued by `chron_trans` into one timelike curve, so
`x + ∂₀ + ∂₀ ∈ I⁺(x)`, and `I⁺(x) ⊆ J⁺(x)` contains it. The hypotheses are satisfied by genuine
curves.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace Lightlike.Causal

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity: two future timelike steps `∂₀` give a point of `I⁺(x)` and of `J⁺(x)`. -/
example (x : Fin (d + 1) → ℝ) :
    x + Pi.single 0 1 + Pi.single 0 1 ∈ chronFuture (minkowskiOrientation d) x ∧
      x + Pi.single 0 1 + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x := by
  have h1 : x + Pi.single 0 1 ∈ chronFuture (minkowskiOrientation d) x :=
    line_mem_chronFuture x _ ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩
  have h2 : x + Pi.single 0 1 + Pi.single 0 1 ∈
      chronFuture (minkowskiOrientation d) (x + Pi.single 0 1) :=
    line_mem_chronFuture (x + Pi.single 0 1) _
      ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩
  have h3 := chron_trans _ h1 h2
  exact ⟨h3, chron_subset_causal _ x h3⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- Trust check of `minkowski_causalFuture_eq`: the point one time unit in the past is not in the
causal future, while the point one time unit ahead and the point itself are. -/
example (x : Fin (d + 1) → ℝ) :
    x - Pi.single 0 1 ∉ causalFuture (minkowskiOrientation d) x ∧
      x + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x := by
  rw [minkowski_causalFuture_eq]
  refine ⟨fun h => ?_, ?_⟩
  · have := h.1
    simp at this
    linarith
  · refine ⟨by simp, ?_⟩
    have := form_e0 (d := d)
    simp only [add_sub_cancel_left]
    linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- Wrong model: a spacelike displacement is not in the causal future (`d + 2` dimensions). -/
example (x : Fin (d + 2) → ℝ) :
    x + Pi.single (Fin.succ 0) 1 ∉ causalFuture (minkowskiOrientation (d + 1)) x := by
  rw [minkowski_causalFuture_eq]
  rintro ⟨-, h⟩
  have := form_e1 (d := d)
  simp only [add_sub_cancel_left] at h
  linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the diamond statement of global hyperbolicity: `x` itself lies in the compact
causal diamond between `x` and `x + ∂₀`. -/
example (x : Fin (d + 1) → ℝ) :
    x ∈ causalFuture (minkowskiOrientation d) x ∩
      causalPast (minkowskiOrientation d) (x + Pi.single 0 1) := by
  refine ⟨self_mem_causalFuture _ x, ?_⟩
  show x + Pi.single 0 1 ∈ causalFuture (minkowskiOrientation d) x
  rw [minkowski_causalFuture_eq]
  refine ⟨by simp, ?_⟩
  have := form_e0 (d := d)
  simp only [add_sub_cancel_left]
  linarith

example : IsCompact (causalFuture (minkowskiOrientation d) 0 ∩
    causalPast (minkowskiOrientation d) (Pi.single 0 1)) := minkowski_globallyHyperbolic.2 _ _

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the smoothing of a time orientation: Minkowski space has a smooth field that is
future timelike for `∂₀`. -/
example : ∃ X' : (x : Fin (d + 1) → ℝ) → TangentSpace 𝓘(ℝ, Fin (d + 1) → ℝ) x,
    ContMDiff 𝓘(ℝ, Fin (d + 1) → ℝ) (𝓘(ℝ, Fin (d + 1) → ℝ).prod 𝓘(ℝ, Fin (d + 1) → ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (Fin (d + 1) → ℝ)
        (E := fun x : Fin (d + 1) → ℝ ↦ TangentSpace 𝓘(ℝ, Fin (d + 1) → ℝ) x) x (X' x)) ∧
    ∀ x, (minkowskiMetric (d + 1)).g x (X' x) (X' x) < 0 ∧
      (minkowskiMetric (d + 1)).g x (X' x) ((minkowskiOrientation d).X x) < 0 :=
  exists_smooth_field (minkowskiOrientation d)

/-- Trust check of the margin: a future-directed null vector (`g(v, v) = 0`, `g(v, X) < 0`) has no
positive margin, so it is not future-directed timelike with any `ε > 0`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g) {x : M}
    (v : TangentSpace I x) (hv : g.g x v v = 0) {ε : ℝ} (hε : 0 < ε) :
    ¬ T.IsFutureTimelikeWith ε v := fun h => by
  have := (T.isFutureTimelike_of_with hε h).1
  linarith

/-- Trust check of the endpoint definition (the textbook one): a curve that is continuous on a
closed interval `[a, b]`, `a < b`, has the future endpoint `γ b`, so it is extendible, hence not
inextendible. -/
example {M : Type*} [TopologicalSpace M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Set.Icc a b)) :
    HasFutureEndpoint γ (Set.Icc a b) (γ b) := by
  intro U hU
  have h1 : γ ⁻¹' U ∈ 𝓝[Set.Icc a b] b := hγ b ⟨hab.le, le_rfl⟩ hU
  rw [nhdsWithin_Icc_eq_nhdsLE hab, mem_nhdsLE_iff_exists_Icc_subset] at h1
  obtain ⟨l, hl, hsub⟩ := h1
  exact ⟨max l a, ⟨le_max_right _ _, (max_le hl.le hab.le)⟩, fun t ht hct =>
    hsub ⟨(le_max_left _ _).trans hct, ht.2⟩⟩

/-- Trust check: the curve `t ↦ eᵗ` of the line has a past endpoint `0`, although its parameter
interval is unbounded below; a definition of "endpoint" that needs a bounded parameter interval
would call it inextendible. -/
example : HasPastEndpoint (fun t : ℝ => Real.exp t) Set.univ 0 := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨Real.log (ε / 2), trivial, fun t _ ht => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos t)]
  calc Real.exp t ≤ Real.exp (Real.log (ε / 2)) := Real.exp_le_exp.2 ht
    _ = ε / 2 := Real.exp_log (by positivity)
    _ < ε := by linarith

/-- Non-vacuity of the bridge: the Minkowski line has the margin on `[0, 1]`. -/
example (v : Fin (d + 1) → ℝ)
    (hv : minkowskiForm (d + 1) v v < 0 ∧ minkowskiForm (d + 1) v (Pi.single 0 1) < 0) :
    ∃ ε : ℝ, 0 < ε ∧ IsCurveWith (I := 𝓘(ℝ, Fin (d + 1) → ℝ))
      (fun _ w ↦ (minkowskiOrientation d).IsFutureTimelikeWith ε w)
      (fun t : ℝ => (0 : Fin (d + 1) → ℝ) + t • v) (Set.Icc 0 1) :=
  (isFutureTimelikeCurve_line 0 v zero_lt_one hv).2 0 1 zero_lt_one subset_rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the Cauchy surface definition: the line `t ↦ x + t ∂₀` on all of `ℝ` is an
inextendible future-directed timelike curve (it has no endpoint: its time is unbounded, so no
neighbourhood of a point contains it from some parameter on), and it meets the slice `t = 0`
exactly once, as `minkowski_slice_isCauchySurface` says. -/
example (x : Fin (d + 1) → ℝ) :
    IsInextendibleFutureTimelike (minkowskiOrientation d)
      (fun t : ℝ => x + t • (Pi.single 0 1 : Fin (d + 1) → ℝ)) Set.univ := by
  set v : Fin (d + 1) → ℝ := Pi.single 0 1 with hv
  have hvt : minkowskiForm (d + 1) v v < 0 ∧ minkowskiForm (d + 1) v (Pi.single 0 1) < 0 :=
    ⟨form_e0.trans_lt (by norm_num), form_e0.trans_lt (by norm_num)⟩
  refine ⟨⟨⟨ordConnected_univ, isLocallyLipschitzOn_line x v _, ?_⟩,
    fun a b hab _ => (isFutureTimelikeCurve_line x v hab hvt).2 a b hab subset_rfl⟩,
    ⟨0, trivial⟩, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    have hd0 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hd : HasDerivWithinAt (fun t : ℝ => x + t • v) v Set.univ t := hd0.hasDerivWithinAt
    refine ⟨?_, ?_⟩
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact hd.differentiableWithinAt
    · have h1 : velocity 𝓘(ℝ, Fin (d + 1) → ℝ) (fun t : ℝ => x + t • v) Set.univ t = v := by
        rw [velocity, mfderivWithin_eq_fderivWithin,
          hd.hasFDerivWithinAt.fderivWithin uniqueDiffWithinAt_univ]
        exact one_smul ℝ v
      rw [h1]
      exact hvt
  · intro p hp
    obtain ⟨c, -, hc⟩ := hp (Metric.ball p 1) (Metric.ball_mem_nhds p one_pos)
    have h1 := hc c trivial le_rfl
    have h2 := hc (c + 3) trivial (by linarith)
    have := dist_triangle_left (x + c • v) (x + (c + 3) • v) p
    have h3 : dist (x + c • v) (x + (c + 3) • v) = 3 := by
      have hn : ‖v‖ = 1 := by
        refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
        · by_cases h : i = 0 <;> simp [hv, h]
        · simpa [hv] using norm_le_pi_norm v 0
      rw [dist_eq_norm, show x + c • v - (x + (c + 3) • v) = (-3 : ℝ) • v by
        rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring, norm_smul, hn]
      norm_num
    simp only [Metric.mem_ball] at h1 h2
    rw [dist_comm] at h1 h2
    linarith
  · intro p hp
    obtain ⟨c, -, hc⟩ := hp (Metric.ball p 1) (Metric.ball_mem_nhds p one_pos)
    have h1 := hc c trivial le_rfl
    have h2 := hc (c - 3) trivial (by linarith)
    have := dist_triangle_left (x + c • v) (x + (c - 3) • v) p
    have h3 : dist (x + c • v) (x + (c - 3) • v) = 3 := by
      have hn : ‖v‖ = 1 := by
        refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
        · by_cases h : i = 0 <;> simp [hv, h]
        · simpa [hv] using norm_le_pi_norm v 0
      rw [dist_eq_norm, show x + c • v - (x + (c - 3) • v) = (3 : ℝ) • v by
        rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring, norm_smul, hn]
      norm_num
    simp only [Metric.mem_ball] at h1 h2
    rw [dist_comm] at h1 h2
    linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the achronality of a Cauchy surface: the slice `t = 0` of Minkowski space is a
Cauchy surface (`minkowski_slice_isCauchySurface`), hence achronal; the hypotheses
(Hausdorff, second countable, without boundary) hold for `ℝ^{d+1}`. -/
example : IsAchronal (minkowskiOrientation d) {y : Fin (d + 1) → ℝ | y 0 = 0} :=
  (minkowski_slice_isCauchySurface (d := d)).isAchronal_of_boundaryless _

set_option synthInstance.maxHeartbeats 200000 in
/-- Non-vacuity of the covering by a Cauchy surface: every point of Minkowski space is in the slice
`t = 0`, in the chronological future of a point of it, or in its chronological past. -/
example (p : Fin (d + 1) → ℝ) :
    p ∈ {y : Fin (d + 1) → ℝ | y 0 = 0} ∨
      (∃ x ∈ {y : Fin (d + 1) → ℝ | y 0 = 0}, p ∈ chronFuture (minkowskiOrientation d) x) ∨
      ∃ x ∈ {y : Fin (d + 1) → ℝ | y 0 = 0}, x ∈ chronFuture (minkowskiOrientation d) p :=
  (minkowski_slice_isCauchySurface (d := d)).cover _ p

end Lightlike.Causal
