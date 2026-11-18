import Lightlike.Spacetime.Causal.TimelikeBelowCurve

/-!
# The perturbation step for a Cauchy surface

For an achronal Cauchy surface `S`, every point lies in `S`, `I⁺(S)` or `I⁻(S)` (`IsCauchySurface.cover`),
so `exists_timelike_missing` and its past twin apply to every inextendible future causal curve `c`
through a point of `S ∪ I⁺(S)` (resp. `S ∪ I⁻(S)`) that misses `S` in the past (resp. the future) of that
point: it yields an inextendible future timelike curve that misses `S`
(`perturb_future_of_cauchy`, `perturb_past_of_cauchy`). A Cauchy surface for `T` is one for `T.reverse`
(`IsCauchySurface.reverse`). The push-ups of `T-GE2-P5` and `T-GE2-P6` are hypotheses.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A Cauchy surface for `T` is a Cauchy surface for `T.reverse`.** -/
theorem IsCauchySurface.reverse {S : Set M} (h : IsCauchySurface T S) : IsCauchySurface T.reverse S := by
  intro γ s hγ
  have hso : IsOpen s := isOpen_of_noEndpoints hγ.1.1.ordConnected hγ.2
  have hrefl : IsInextendibleFutureTimelike T (fun t => γ (-t)) ((fun t : ℝ => -t) ⁻¹' s) :=
    ⟨IsFutureTimelikeCurve.reflect_open T hso hγ.1.1.ordConnected hγ.1, noEndpoints_reflect hγ.2⟩
  obtain ⟨t, ⟨hts, htS⟩, huniq⟩ := h _ _ hrefl
  refine ⟨-t, ⟨by simpa using hts, by simpa using htS⟩, fun u hu => ?_⟩
  have := huniq (-u) ⟨by simpa using hu.1, by simpa using hu.2⟩
  linarith

section Main

variable [T2Space M] [SecondCountableTopology M] [BoundarylessManifold I M]

/-- The covering of the manifold by a Cauchy surface, in the form used by the perturbation lemmas. -/
theorem IsCauchySurface.cover' {S : Set M} (h : IsCauchySurface T S) (p : M) :
    p ∈ S ∨ p ∈ chronFutureSet T S ∨ p ∈ chronPastSet T S := by
  rcases IsCauchySurface.cover T h p with h1 | ⟨x, hx, h2⟩ | ⟨x, hx, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl (Set.mem_iUnion₂.2 ⟨x, hx, h2⟩))
  · exact Or.inr (Or.inr (Set.mem_iUnion₂.2 ⟨x, hx, h3⟩))

/-- **Perturbation, future form.** -/
theorem perturb_future_of_cauchy
    (hpush : ∀ x y z : M, y ∈ causalFuture T x → z ∈ chronFuture T y → z ∈ chronFuture T x)
    {S : Set M} (hA : IsAchronal T S) (hC : IsCauchySurface T S) :
    ∀ p : M, (p ∈ S ∨ p ∈ chronFutureSet T S) → ∀ (c : ℝ → M) (s : Set ℝ),
      IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) c s → ∀ t ∈ s, c t = p →
      (∀ t' ∈ s, t' ≤ t → c t' ∉ S) →
      ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S := by
  intro p hp c s hc t ht hct hmiss
  rcases hp with hpS | hpF
  · exact absurd (hct ▸ hpS) (hmiss t ht le_rfl)
  · exact exists_timelike_missing T hpush hA (IsCauchySurface.cover' T hC) hc ht (hct ▸ hpF) hmiss

/-- **Perturbation, past form.** -/
theorem perturb_past_of_cauchy
    (hpush : ∀ x y z : M, y ∈ chronFuture T x → z ∈ causalFuture T y → z ∈ chronFuture T x)
    {S : Set M} (hA : IsAchronal T S) (hC : IsCauchySurface T S) :
    ∀ p : M, (p ∈ S ∨ p ∈ chronPastSet T S) → ∀ (c : ℝ → M) (s : Set ℝ),
      IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) c s → ∀ t ∈ s, c t = p →
      (∀ t' ∈ s, t ≤ t' → c t' ∉ S) →
      ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S := by
  intro p hp c s hc t ht hct hmiss
  rcases hp with hpS | hpP
  · exact absurd (hct ▸ hpS) (hmiss t ht le_rfl)
  · exact exists_timelike_missing_past T hpush hA (IsCauchySurface.cover' T hC) hc ht (hct ▸ hpP) hmiss

end Main

end Lightlike.Causal
