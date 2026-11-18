import Lightlike.Spacetime.CausalLadder.CausalOpen
import Lightlike.Spacetime.CausalLadder.CausalPastLimsup
import Lightlike.Spacetime.CausalLadder.CausalPastLiminf

/-!
# Assembly of Hawking's time function

If `x ↦ μ(J⁻(x))` is continuous (for a finite Borel measure `μ` that is positive on nonempty open
sets), then it is a time function: continuous, and strictly increasing along causal futures. The
strict increase is `measure_causalPast_lt`; the continuity is the remaining content of task
`T-GE2-P11` (lower semicontinuity from the null horismos, upper semicontinuity from
`limsup_measure_causalPast_le`).

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Hawking's time function from a continuous volume of the causal past.** -/
theorem isStablyCausal_of_continuous_measure [BoundarylessManifold I M] [MeasurableSpace M]
    [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O) (hcausal : IsCausal T)
    (hclosed : ∀ x : M, IsClosed (causalPast T x))
    (hcont : Continuous fun x => (μ (causalPast T x)).toReal) : IsStablyCausal T := by
  refine ⟨fun x => (μ (causalPast T x)).toReal, hcont, fun x y hxy hne => ?_⟩
  have h := measure_causalPast_lt T μ hμ hcausal hclosed hxy hne
  exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).2 h

/-- **Continuity from the two semicontinuities.** On a first countable space, if for every sequence
`xₖ → x` one has `limsup μ(J⁻(xₖ)) ≤ μ(J⁻(x)) ≤ liminf μ(J⁻(xₖ))`, then `x ↦ μ(J⁻(x)).toReal` is
continuous. -/
theorem continuous_measure_causalPast [FirstCountableTopology M] [MeasurableSpace M] (μ : Measure M)
    [IsFiniteMeasure μ]
    (hup : ∀ (xs : ℕ → M) (x : M), Tendsto xs atTop (𝓝 x) →
      limsup (fun k => μ (causalPast T (xs k))) atTop ≤ μ (causalPast T x))
    (hlow : ∀ (xs : ℕ → M) (x : M), Tendsto xs atTop (𝓝 x) →
      μ (causalPast T x) ≤ liminf (fun k => μ (causalPast T (xs k))) atTop) :
    Continuous fun x => (μ (causalPast T x)).toReal := by
  refine continuous_iff_seqContinuous.2 fun xs x hx => ?_
  have h := tendsto_of_le_liminf_of_limsup_le (hlow xs x hx) (hup xs x hx)
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp h

/-- **Causal simplicity gives a time function, given a full-support finite measure with null
horismos.** Let `μ` be a finite Borel measure on a second-countable manifold without boundary that is
positive on nonempty open sets, with `J⁻(x) \ Ĩ⁻(x)` `μ`-null for every `x`. If the space is causal
and the causal futures and pasts are closed, it is stably causal. -/
theorem isStablyCausal_of_null_horismos [BoundarylessManifold I M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] (μ : Measure M) [IsFiniteMeasure μ]
    (hμ : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O)
    (hnull : ∀ x : M, μ (causalPast T x \ interiorCausalPast T x) = 0)
    (hs : IsCausallySimple T) : IsStablyCausal T :=
  isStablyCausal_of_continuous_measure T μ hμ hs.1 (fun x => (hs.2 x).2)
    (continuous_measure_causalPast T μ
      (fun xs x hx => limsup_measure_causalPast_le T μ (fun a => (hs.2 a).1) (fun a => (hs.2 a).2) hx)
      (fun xs x hx => measure_causalPast_le_liminf_of_null T μ (fun a => (hs.2 a).2) hnull hx))

end Lightlike.Causal
