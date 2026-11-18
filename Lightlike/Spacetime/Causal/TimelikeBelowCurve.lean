import Lightlike.Spacetime.Causal.TimelikeAboveCurve
import Lightlike.Spacetime.Causal.TimeReversal

/-!
# The past twin: an inextendible causal curve through `I⁻(S)` that misses `S` in the future

By time reversal. A curve `λ` and its reflection `t ↦ λ (-t)`: a future causal curve for `T` becomes one for
`T.reverse`, a future timelike curve for `T.reverse` becomes one for `T`, the parameter sets are reflected
and past endpoints become future endpoints. So `exists_timelike_missing` for `T.reverse` gives the statement
for the chronological past (`exists_timelike_missing_past`), under the push-up of the other kind
(`I⁺ then J⁺ ⊆ I⁺`, the statement of `T-GE2-P5`) as a hypothesis.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- Future causal for the reversed orientation is future causal for `T` of the negative vector. -/
theorem TimeOrientation.isFutureCausal_reverse_iff {x : M} (v : TangentSpace I x) :
    T.reverse.IsFutureCausal v ↔ T.IsFutureCausal (-v) := by
  have := T.isFutureCausal_reverse_neg (-v)
  rwa [neg_neg] at this

/-- The preimage of an interval under `t ↦ -t` is an interval. -/
lemma ordConnected_neg_preimage {s : Set ℝ} (hs : s.OrdConnected) :
    ((fun t : ℝ => -t) ⁻¹' s).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ?_⟩
  exact hs.out hy hx ⟨by linarith [hz.2], by linarith [hz.1]⟩

/-- **Reflection of the parameter on an open interval.** -/
theorem IsCurveWith.reflect_open {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {s : Set ℝ}
    (hso : IsOpen s) (hsc : s.OrdConnected) (h : IsCurveWith (I := I) P γ s) :
    IsCurveWith (I := I) (fun x v => P x (-v)) (fun t => γ (-t)) ((fun t : ℝ => -t) ⁻¹' s) := by
  refine IsCurveWith.of_Icc (hso.preimage continuous_neg) (ordConnected_neg_preimage hsc) ?_
  intro a b hab hsub
  have hsub' : Icc (-b) (-a) ⊆ s := fun x hx => by
    simpa using hsub (show -x ∈ Icc a b from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have := IsCurveWith.reflect (IsCurveWith.restrict h hsub' (by linarith)) (by linarith : -b < -a)
  simpa using this

/-- **Reflection of a future timelike curve for the reversed orientation.** -/
theorem IsFutureTimelikeCurve.reflect_open {γ : ℝ → M} {s : Set ℝ} (hso : IsOpen s)
    (hsc : s.OrdConnected) (h : IsFutureTimelikeCurve T.reverse γ s) :
    IsFutureTimelikeCurve T (fun t => γ (-t)) ((fun t : ℝ => -t) ⁻¹' s) := by
  refine isFutureTimelikeCurve_of_Icc T (hso.preimage continuous_neg) (ordConnected_neg_preimage hsc) ?_
  intro a b hab hsub
  have hsub' : Icc (-b) (-a) ⊆ s := fun x hx => by
    simpa using hsub (show -x ∈ Icc a b from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  obtain ⟨ε, hε, hm⟩ := h.2 (-b) (-a) (by linarith) hsub'
  have hr := (IsCurveWith.reflect hm (by linarith : -b < -a)).mono_velocity fun x v hv =>
    (T.isFutureTimelikeWith_reverse_neg v).1 hv
  have : IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelikeWith ε v) (fun t => γ (-t)) (Icc a b) := by
    simpa using hr
  exact isFutureTimelikeCurve_of_margin T hε this

omit [IsManifold I ∞ M] in
/-- A curve without endpoints stays so after reflecting the parameter. -/
theorem noEndpoints_reflect {γ : ℝ → M} {s : Set ℝ} (h : NoEndpoints γ s) :
    NoEndpoints (fun t => γ (-t)) ((fun t : ℝ => -t) ⁻¹' s) := by
  obtain ⟨⟨t, ht⟩, hf, hp⟩ := h
  refine ⟨⟨-t, by simpa using ht⟩, ?_, ?_⟩
  · intro p hpe
    refine hp p fun U hU => ?_
    obtain ⟨c, hc, hcU⟩ := hpe U hU
    refine ⟨-c, hc, fun x hx hxc => ?_⟩
    have := hcU (-x) (by simpa using hx) (by linarith)
    simpa using this
  · intro p hpe
    refine hf p fun U hU => ?_
    obtain ⟨c, hc, hcU⟩ := hpe U hU
    refine ⟨-c, hc, fun x hx hxc => ?_⟩
    have := hcU (-x) (by simpa using hx) (by linarith)
    simpa using this

/-- `I⁻` for the reversed orientation is `I⁺`. -/
theorem chronPast_reverse (x : M) : chronPast T.reverse x = chronFuture T x := by
  ext y
  show x ∈ chronFuture T.reverse y ↔ y ∈ chronFuture T x
  rw [chronFuture_reverse]
  rfl

section Main

variable [T2Space M] [SecondCountableTopology M] [BoundarylessManifold I M]

/-- **The past twin of `exists_timelike_missing`.** An inextendible future causal curve through a point of
`I⁻(S)` that misses `S` at the later parameters yields an inextendible future timelike curve that misses `S`.
The push-up of the second kind `I⁺ then J⁺ ⊆ I⁺` (the statement of `T-GE2-P5`) is the hypothesis `hpush`:
conditional library code, with no task file and no catalogue claim. -/
theorem exists_timelike_missing_past
    (hpush : ∀ x y z : M, y ∈ chronFuture T x → z ∈ causalFuture T y → z ∈ chronFuture T x)
    {S : Set M} (hA : IsAchronal T S)
    (hcov : ∀ p : M, p ∈ S ∨ p ∈ chronFutureSet T S ∨ p ∈ chronPastSet T S)
    {lam : ℝ → M} {s : Set ℝ}
    (hlam : IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) lam s)
    {t₁ : ℝ} (ht₁ : t₁ ∈ s) (hp : lam t₁ ∈ chronPastSet T S)
    (hmiss : ∀ t ∈ s, t₁ ≤ t → lam t ∉ S) :
    ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S := by
  have hF : chronFutureSet T.reverse S = chronPastSet T S := by
    ext p
    simp only [chronFutureSet, chronPastSet, chronFuture_reverse]
  have hP : chronPastSet T.reverse S = chronFutureSet T S := by
    ext p
    simp only [chronFutureSet, chronPastSet, chronPast_reverse]
  have hso : IsOpen s := isOpen_of_noEndpoints hlam.1.ordConnected hlam.2
  have hlam' : IsInextendibleWith (I := I) (fun _ v ↦ T.reverse.IsFutureCausal v)
      (fun t => lam (-t)) ((fun t : ℝ => -t) ⁻¹' s) :=
    ⟨(IsCurveWith.reflect_open hso hlam.1.ordConnected hlam.1).mono_velocity fun x v hv =>
        (T.isFutureCausal_reverse_iff v).2 hv, noEndpoints_reflect hlam.2⟩
  obtain ⟨Ĝ, ŝ, hĜ, hmissĜ⟩ := exists_timelike_missing T.reverse
    (fun x y z hy hz => by
      rw [causalFuture_reverse] at hy
      rw [chronFuture_reverse] at hz ⊢
      exact hpush z y x hz hy)
    (fun x hx y hy hxy => by
      rw [chronFuture_reverse] at hxy
      exact hA y hy x hx hxy)
    (fun p => by
      rw [hF, hP]
      rcases hcov p with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h))
    hlam' (t₁ := -t₁) (by simpa using ht₁) (by simpa [hF] using hp)
    (fun t ht hle => hmiss (-t) ht (by linarith))
  have hŝo : IsOpen ŝ := isOpen_of_noEndpoints hĜ.1.1.ordConnected hĜ.2
  refine ⟨fun t => Ĝ (-t), (fun t : ℝ => -t) ⁻¹' ŝ, ⟨?_, noEndpoints_reflect hĜ.2⟩, ?_⟩
  · exact IsFutureTimelikeCurve.reflect_open T hŝo hĜ.1.1.ordConnected hĜ.1
  · intro u hu
    exact hmissĜ (-u) hu

end Main

end Lightlike.Causal
