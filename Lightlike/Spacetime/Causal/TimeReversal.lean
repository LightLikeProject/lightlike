import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.CurveOps

/-!
# Time reversal

The time orientation `-X` of a time-oriented Lorentzian manifold is `TimeOrientation.reverse`. A curve
with velocity in `P` on `[a, b]` gives, by `t ↦ γ (-t)`, a curve with velocity `v ↦ P (-v)` on `[-b, -a]`
(`IsCurveWith.reflect`). Hence a future-directed timelike curve for `T.reverse` from `x` to `y` is, run
backwards, a future-directed timelike curve for `T` from `y` to `x`: the chronological future for the
reversed orientation is the chronological past (`chronFuture_reverse`).

## Main definitions

* `Causal.TimeOrientation.reverse`: the time orientation `-X`.
* `Causal.IsCurveWith.reflect`: reflecting the parameter.
* `Causal.chronFuture_reverse`: `I⁺` for `T.reverse` is `I⁻` for `T`.
-/

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n}

/-- **The reversed time orientation**: the timelike vector field `-X`. -/
def TimeOrientation.reverse (T : TimeOrientation g) : TimeOrientation g where
  X x := -T.X x
  contMDiff := by
    exact ContMDiff.neg_section (s := T.X) T.contMDiff
  timelike x := by simpa using T.timelike x

omit [IsManifold I ∞ M] in
/-- **Reflection of the parameter**: if `γ` has its velocity in `P` on `[a, b]`, then `t ↦ γ (-t)` has its
velocity in `fun x v => P x (-v)` on `[-b, -a]`. -/
theorem IsCurveWith.reflect {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b : ℝ}
    (h : IsCurveWith (I := I) P γ (Icc a b)) (hab : a < b) :
    IsCurveWith (I := I) (fun x v => P x (-v)) (fun t => γ (-t)) (Icc (-b) (-a)) := by
  have hmem : ∀ t, t ∈ Icc (-b) (-a) → -t ∈ Icc a b := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz (-t) (hmem t ht)
    refine ⟨K, (fun s => -s) ⁻¹' U, ?_, fun s hs => hm hs, ?_⟩
    · refine (continuous_neg : Continuous fun s : ℝ => -s).continuousWithinAt.preimage_mem_nhdsWithin' ?_
      refine nhdsWithin_mono _ ?_ hU
      rintro _ ⟨s, hs, rfl⟩
      exact hmem s hs
    · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have := hl.dist_le_mul (-x) hx (-y) hy
      simpa [dist_neg_neg] using this
  · have h1 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1] with t ht h2
    obtain ⟨h3, h4⟩ := h2 (hmem t ht)
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (-b) (-a)) t :=
      (uniqueDiffOn_Icc (by linarith) t ht).uniqueMDiffWithinAt
    have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s) (Icc (-b) (-a)) t := by
      rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact differentiableWithinAt_id.neg
    have hmaps : Icc (-b) (-a) ⊆ (fun s : ℝ => -s) ⁻¹' Icc a b := fun s hs => hmem s hs
    refine ⟨h3.comp t hτ hmaps, ?_⟩
    have hc := mfderivWithin_comp t h3 hτ hmaps hu
    have hd : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s) (Icc (-b) (-a)) t 1 = -1 := by
      rw [mfderivWithin_eq_fderivWithin]
      have : HasFDerivWithinAt (fun s : ℝ => -s) (-ContinuousLinearMap.id ℝ ℝ)
          (Icc (-b) (-a)) t := (hasFDerivWithinAt_id t _).neg
      rw [this.fderivWithin (uniqueDiffOn_Icc (by linarith) t ht)]
      rfl
    have hv : velocity I (fun t => γ (-t)) (Icc (-b) (-a)) t =
        -velocity I γ (Icc a b) (-t) := by
      unfold velocity
      rw [show (fun t => γ (-t)) = γ ∘ (fun s : ℝ => -s) from rfl, hc]
      show (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) (-t)) _ = _
      erw [hd]
      exact map_neg _ _
    show P (γ (-t)) (-velocity I (fun t => γ (-t)) (Icc (-b) (-a)) t)
    rw [hv, neg_neg]
    exact h4

variable (T : TimeOrientation g)

/-- Reversing a vector and the time orientation preserves the margin condition. -/
theorem TimeOrientation.isFutureTimelikeWith_reverse_neg {ε : ℝ} {x : M} (v : TangentSpace I x) :
    T.reverse.IsFutureTimelikeWith ε (-v) ↔ T.IsFutureTimelikeWith ε v := by
  simp [TimeOrientation.IsFutureTimelikeWith, TimeOrientation.reverse]

/-- Reversing twice gives back the time orientation. -/
theorem TimeOrientation.reverse_reverse : T.reverse.reverse = T := by
  cases T
  simp [TimeOrientation.reverse]

/-- **A future timelike curve for the reversed orientation, run backwards, is one for `T`.** -/
theorem chronFuture_reverse_subset {x y : M} (h : y ∈ chronFuture T.reverse x) :
    x ∈ chronFuture T y := by
  obtain ⟨γ, a, b, hab, hγ, ha, hb⟩ := h
  obtain ⟨ε, hε, hm⟩ := hγ.2 a b hab subset_rfl
  have hr := (IsCurveWith.reflect hm hab).mono_velocity fun x v hv =>
    (T.isFutureTimelikeWith_reverse_neg v).1 hv
  exact ⟨fun t => γ (-t), -b, -a, by linarith, isFutureTimelikeCurve_of_margin T hε hr,
    by simp [hb], by simp [ha]⟩

/-- **`I⁺` for the reversed orientation is `I⁻`.** -/
theorem chronFuture_reverse (x : M) : chronFuture T.reverse x = chronPast T x := by
  ext y
  constructor
  · exact fun h => chronFuture_reverse_subset T h
  · intro h
    have := chronFuture_reverse_subset T.reverse (x := y) (y := x)
    rw [TimeOrientation.reverse_reverse] at this
    exact this h

/-- Reversing a vector and the time orientation preserves being future causal. -/
theorem TimeOrientation.isFutureCausal_reverse_neg {x : M} (v : TangentSpace I x) :
    T.reverse.IsFutureCausal (-v) ↔ T.IsFutureCausal v := by
  simp [TimeOrientation.IsFutureCausal, TimeOrientation.reverse]

/-- **A future causal curve for the reversed orientation, run backwards, is one for `T`.** -/
theorem causalFuture_reverse_subset {x y : M} (h : y ∈ causalFuture T.reverse x) :
    x ∈ causalFuture T y := by
  obtain ⟨γ, a, b, hab, hγ, ha, hb⟩ := h
  rcases hab.lt_or_eq with hlt | heq
  · have hr := (IsCurveWith.reflect hγ hlt).mono_velocity fun x v hv =>
      (T.isFutureCausal_reverse_neg v).1 hv
    exact ⟨fun t => γ (-t), -b, -a, by linarith, hr, by simp [hb], by simp [ha]⟩
  · subst heq
    have : x = y := by rw [← ha, ← hb]
    rw [← this]; exact self_mem_causalFuture T x

/-- **`J⁺` for the reversed orientation is `J⁻`.** -/
theorem causalFuture_reverse (x : M) : causalFuture T.reverse x = causalPast T x := by
  ext y
  constructor
  · exact fun h => causalFuture_reverse_subset T h
  · intro h
    have := causalFuture_reverse_subset T.reverse (x := y) (y := x)
    rw [TimeOrientation.reverse_reverse] at this
    exact this h

end Lightlike.Causal
