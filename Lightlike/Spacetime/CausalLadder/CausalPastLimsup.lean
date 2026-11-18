import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Upper semicontinuity of the volume of the causal past

If the causal futures `J⁺(a)` are closed, then for a finite Borel measure `μ` and points
`xₖ → x`, `limsup μ(J⁻(xₖ)) ≤ μ(J⁻(x))`. A point lying in `J⁻(xₖ)` for infinitely many `k` lies in
`J⁻(x)`, because `xₖ ∈ J⁺(a)` infinitely often and `J⁺(a)` is closed; the measure of the limsup set
bounds the limsup of the measures (continuity from above, finite measure).

This is the half of the continuity of Hawking's time function `x ↦ μ(J⁻(x))` that needs only causal
simplicity. Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology Set MeasureTheory
open scoped ContDiff Manifold

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A point in `J⁻(xₖ)` for infinitely many `k` lies in `J⁻(x)`, if the causal futures are closed
and `xₖ → x`. -/
theorem mem_causalPast_of_frequently {xs : ℕ → M} {x : M} (hclosed : ∀ a : M, IsClosed (causalFuture T a))
    (hx : Tendsto xs atTop (𝓝 x)) {a : M} (ha : ∃ᶠ k in atTop, a ∈ causalPast T (xs k)) :
    a ∈ causalPast T x :=
  (hclosed a).mem_of_frequently_of_tendsto ha hx

/-- **Upper semicontinuity of the volume of the causal past.** See the module docstring. -/
theorem limsup_measure_causalPast_le [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
    [IsFiniteMeasure μ] (hclosed : ∀ a : M, IsClosed (causalFuture T a))
    (hclosedP : ∀ a : M, IsClosed (causalPast T a)) {xs : ℕ → M} {x : M}
    (hx : Tendsto xs atTop (𝓝 x)) :
    limsup (fun k => μ (causalPast T (xs k))) atTop ≤ μ (causalPast T x) := by
  set B : ℕ → Set M := fun m => ⋃ k ≥ m, causalPast T (xs k) with hB
  have hBmeas : ∀ m, MeasurableSet (B m) := fun m =>
    MeasurableSet.biUnion (Set.to_countable _) fun k _ => (hclosedP (xs k)).measurableSet
  have hBanti : Antitone B := fun m m' h => by
    intro a ha
    simp only [hB, mem_iUnion] at ha ⊢
    obtain ⟨k, hk, hak⟩ := ha
    exact ⟨k, h.trans hk, hak⟩
  have hlim : Tendsto (fun m => μ (B m)) atTop (𝓝 (μ (⋂ m, B m))) :=
    tendsto_measure_iInter_atTop (fun m => (hBmeas m).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top μ _⟩
  have hsub : (⋂ m, B m) ⊆ causalPast T x := by
    intro a ha
    refine mem_causalPast_of_frequently T hclosed hx ?_
    rw [Nat.frequently_atTop_iff_infinite]
    refine Set.infinite_of_forall_exists_gt fun m => ?_
    have := mem_iInter.1 ha (m + 1)
    simp only [hB, mem_iUnion] at this
    obtain ⟨k, hk, hak⟩ := this
    exact ⟨k, hak, by omega⟩
  calc limsup (fun k => μ (causalPast T (xs k))) atTop
      ≤ limsup (fun m => μ (B m)) atTop := by
        refine limsup_le_limsup (Eventually.of_forall fun m => measure_mono ?_)
        intro a ha
        simp only [hB, mem_iUnion]
        exact ⟨m, le_rfl, ha⟩
    _ = μ (⋂ m, B m) := hlim.limsup_eq
    _ ≤ μ (causalPast T x) := measure_mono hsub

end Lightlike.Causal
