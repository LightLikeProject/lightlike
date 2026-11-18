import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Lower semicontinuity of the volume of the causal past, from the null horismos

Write `Ĩ⁻(x)` for the points `a` such that some neighbourhood of `x` lies in `J⁺(a)` (the interior
of `J⁺(a)` contains `x`). If `xₖ → x` then every `a ∈ Ĩ⁻(x)` lies in `J⁻(xₖ)` for all large `k`, so
`μ(Ĩ⁻(x)) ≤ liminf μ(J⁻(xₖ))` (Fatou for sets). If `J⁻(x) \ Ĩ⁻(x)` is `μ`-null this is the lower
semicontinuity `μ(J⁻(x)) ≤ liminf μ(J⁻(xₖ))` that Hawking's time function needs; the null
horismos is the remaining hard step of task `T-GE2-P11`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology Set MeasureTheory
open scoped ContDiff Manifold

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The points `a` with `x` in the interior of `J⁺(a)`: a neighbourhood of `x` lies in `J⁺(a)`. -/
def interiorCausalPast (x : M) : Set M := {a | causalFuture T a ∈ 𝓝 x}

/-- The interior part is contained in the causal past. -/
theorem interiorCausalPast_subset (x : M) : interiorCausalPast T x ⊆ causalPast T x :=
  fun a (ha : causalFuture T a ∈ 𝓝 x) =>
    show x ∈ causalFuture T a from mem_of_mem_nhds ha

/-- Points of `Ĩ⁻(x)` are in `J⁻(xₖ)` for all large `k` when `xₖ → x`. -/
theorem eventually_mem_causalPast_of_mem_interior {xs : ℕ → M} {x : M}
    (hx : Tendsto xs atTop (𝓝 x)) {a : M} (ha : a ∈ interiorCausalPast T x) :
    ∀ᶠ k in atTop, a ∈ causalPast T (xs k) :=
  hx.eventually ha

/-- **Lower bound by the interior part** (Fatou for sets): for a finite Borel measure with closed
causal pasts, `μ(Ĩ⁻(x)) ≤ liminf μ(J⁻(xₖ))` for `xₖ → x`. -/
theorem measure_interiorCausalPast_le_liminf [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
    [IsFiniteMeasure μ] (hclosedP : ∀ a : M, IsClosed (causalPast T a)) {xs : ℕ → M} {x : M}
    (hx : Tendsto xs atTop (𝓝 x)) :
    μ (interiorCausalPast T x) ≤ liminf (fun k => μ (causalPast T (xs k))) atTop := by
  set C : ℕ → Set M := fun m => ⋂ k ≥ m, causalPast T (xs k) with hC
  have hCmeas : ∀ m, MeasurableSet (C m) := fun m =>
    MeasurableSet.biInter (Set.to_countable _) fun k _ => (hclosedP (xs k)).measurableSet
  have hCmono : Monotone C := fun m m' h => by
    intro a ha
    simp only [hC, mem_iInter] at ha ⊢
    exact fun k hk => ha k (h.trans hk)
  have hsub : interiorCausalPast T x ⊆ ⋃ m, C m := by
    intro a ha
    obtain ⟨m, hm⟩ := (eventually_atTop.1 (eventually_mem_causalPast_of_mem_interior T hx ha))
    exact mem_iUnion.2 ⟨m, by simp only [hC, mem_iInter]; exact fun k hk => hm k hk⟩
  have hlim : Tendsto (fun m => μ (C m)) atTop (𝓝 (μ (⋃ m, C m))) :=
    tendsto_measure_iUnion_atTop hCmono
  refine (measure_mono hsub).trans (le_of_forall_lt fun c hc => ?_)
  obtain ⟨c', hcc', hc'a⟩ := exists_between hc
  obtain ⟨m, hm⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds hc'a))
  have hmm := hm m le_rfl
  have hev : ∀ᶠ k in atTop, c' ≤ μ (causalPast T (xs k)) := by
    filter_upwards [eventually_ge_atTop m] with k hk
    refine hmm.le.trans (measure_mono ?_)
    intro a ha
    simp only [hC, mem_iInter] at ha
    exact ha k hk
  exact lt_of_lt_of_le hcc' (le_liminf_of_le (by isBoundedDefault) hev)

/-- **Lower semicontinuity from the null horismos.** If `J⁻(x) \ Ĩ⁻(x)` is `μ`-null for every `x`,
then `μ(J⁻(x)) ≤ liminf μ(J⁻(xₖ))` for `xₖ → x`. -/
theorem measure_causalPast_le_liminf_of_null [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
    [IsFiniteMeasure μ] (hclosedP : ∀ a : M, IsClosed (causalPast T a))
    (hnull : ∀ x : M, μ (causalPast T x \ interiorCausalPast T x) = 0) {xs : ℕ → M} {x : M}
    (hx : Tendsto xs atTop (𝓝 x)) :
    μ (causalPast T x) ≤ liminf (fun k => μ (causalPast T (xs k))) atTop := by
  calc μ (causalPast T x)
      ≤ μ (interiorCausalPast T x ∪ (causalPast T x \ interiorCausalPast T x)) :=
        measure_mono fun a ha => by
          by_cases h : a ∈ interiorCausalPast T x
          · exact Or.inl h
          · exact Or.inr ⟨ha, h⟩
    _ ≤ μ (interiorCausalPast T x) + μ (causalPast T x \ interiorCausalPast T x) :=
        measure_union_le _ _
    _ = μ (interiorCausalPast T x) := by rw [hnull x, add_zero]
    _ ≤ _ := measure_interiorCausalPast_le_liminf T μ hclosedP hx

end Lightlike.Causal
