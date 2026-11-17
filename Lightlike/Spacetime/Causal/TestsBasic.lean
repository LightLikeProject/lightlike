import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.CurveMargin
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

end Lightlike.Causal
