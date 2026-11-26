import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.TimeReversal
import Lightlike.Spacetime.CausalLadder.ChartVelocity

/-!
# Straight segments in an open subset of `ℝⁿ` as causal curves

On the manifold `↥U` of an open subset of `ℝⁿ` with the Lorentzian metric `openMetric U g hL` and a time
orientation `T`: a segment `t ↦ p + t v`, `t ∈ [0, 1]`, inside `U` is a curve of `↥U` (`segCurve`, with `t` clamped to
`[0, 1]`), smooth with velocity `v` (`velocity_segCurve`); if `v` is future-directed timelike at every point of
the segment, it is a future-directed timelike curve (`isFutureTimelikeCurve_segCurve`), so its end point is in the
chronological future of its start (`segment_mem_chronFuture`).
-/

open Matrix Real Set Filter Topology Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike.Causal

variable {n : ℕ} (U : TopologicalSpace.Opens (Fin n → ℝ)) (p v : Fin n → ℝ)

/-- The segment `t ↦ p + t v`, `t` clamped to `[0, 1]`, as a curve of `↥U`, for a segment inside `U`. -/
def segCurve (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • v ∈ (U : Set (Fin n → ℝ))) : ℝ → U := fun t =>
  ⟨p + (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) • v, hseg _ (projIcc (0 : ℝ) 1 zero_le_one t).2⟩

variable {U p v} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • v ∈ (U : Set (Fin n → ℝ)))

lemma segCurve_apply {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (segCurve U p v hseg t).1 = p + t • v := by
  simp only [segCurve, projIcc_of_mem _ ht]

set_option backward.isDefEq.respectTransparency false in
lemma segCurve_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (segCurve U p v hseg) (Icc 0 1) := by
  intro t ht
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff, contMDiffWithinAt_iff_contDiffWithinAt]
  have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => p + s • v) t :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  exact h1.contDiffWithinAt.congr (fun y hy => segCurve_apply hseg hy) (segCurve_apply hseg ht)

set_option backward.isDefEq.respectTransparency false in
lemma velocity_segCurve {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    velocity 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg) (Icc 0 1) t = v := by
  have hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg) (Icc 0 1) t :=
    ((segCurve_contMDiffOn hseg) t ht).mdifferentiableWithinAt (by simp)
  have hsrc : segCurve U p v hseg t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg t)).source := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have h1 := hasDerivWithinAt_chart_comp (segCurve U p v hseg t) hmd hsrc
  have hchart : (extChartAt 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg t)) ∘ segCurve U p v hseg =
      fun s => (segCurve U p v hseg s).1 := funext fun s => opens_extChartAt_apply U _ _
  rw [hchart] at h1
  have hbase : segCurve U p v hseg t ∈ (tTriv 𝓘(ℝ, Fin n → ℝ) U (segCurve U p v hseg t)).baseSet := by
    simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have htriv : ((tTriv 𝓘(ℝ, Fin n → ℝ) U (segCurve U p v hseg t))
      ⟨segCurve U p v hseg t, velocity 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg) (Icc 0 1) t⟩).2 =
      velocity 𝓘(ℝ, Fin n → ℝ) (segCurve U p v hseg) (Icc 0 1) t := by
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ hbase, opens_continuousLinearMapAt]
    rfl
  rw [htriv] at h1
  have hs : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have h2 : HasDerivWithinAt (fun s => (segCurve U p v hseg s).1) v (Icc 0 1) t :=
    hs.hasDerivWithinAt.congr (fun y hy => segCurve_apply hseg hy) (segCurve_apply hseg ht)
  exact (uniqueDiffOn_Icc zero_lt_one t ht).eq_deriv _ h1 h2

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {hL : IsLorentzianCoordMetric g U}

/-- **A straight segment whose direction is future-directed timelike at every point is a future-directed timelike
curve.** -/
theorem isFutureTimelikeCurve_segCurve (T : TimeOrientation (openMetric U g hL))
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, matForm (g (p + t • v)) v v < 0 ∧
      matForm (g (p + t • v)) v (T.X (segCurve U p v hseg t)) < 0) :
    IsFutureTimelikeCurve T (segCurve U p v hseg) (Icc 0 1) := by
  refine isFutureTimelikeCurve_of_contMDiffOn T zero_lt_one
    ((segCurve_contMDiffOn hseg).of_le (by simp)) fun t ht => ?_
  rw [velocity_segCurve hseg ht]
  have := hv t ht
  rw [← segCurve_apply hseg ht] at this
  exact this

/-- The end `p + v` of a segment that is future-directed timelike at every point is in the chronological future of its
start. -/
theorem segment_mem_chronFuture (T : TimeOrientation (openMetric U g hL))
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, matForm (g (p + t • v)) v v < 0 ∧
      matForm (g (p + t • v)) v (T.X (segCurve U p v hseg t)) < 0) :
    segCurve U p v hseg 1 ∈ chronFuture T (segCurve U p v hseg 0) :=
  ⟨segCurve U p v hseg, 0, 1, zero_lt_one, isFutureTimelikeCurve_segCurve hseg T hv, rfl, rfl⟩

/-- **Chronological future from a segment**: if the segment from `p` to `p + v` lies in `U` and `v` is future-directed
timelike at every point of it, the point `p + v` is in the chronological future of `p`. -/
theorem mem_chronFuture_of_segment (T : TimeOrientation (openMetric U g hL)) {hp : p ∈ (U : Set (Fin n → ℝ))}
    {hq : p + v ∈ (U : Set (Fin n → ℝ))}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, matForm (g (p + t • v)) v v < 0 ∧
      matForm (g (p + t • v)) v (T.X (segCurve U p v hseg t)) < 0) :
    (⟨p + v, hq⟩ : U) ∈ chronFuture T ⟨p, hp⟩ := by
  have h := segment_mem_chronFuture hseg T hv
  have e0 : segCurve U p v hseg 0 = ⟨p, hp⟩ := Subtype.ext (by
    rw [segCurve_apply hseg ⟨le_rfl, zero_le_one⟩, zero_smul, add_zero])
  have e1 : segCurve U p v hseg 1 = ⟨p + v, hq⟩ := Subtype.ext (by
    rw [segCurve_apply hseg ⟨zero_le_one, le_rfl⟩, one_smul])
  rwa [e0, e1] at h

end Lightlike.Causal
