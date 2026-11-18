import Lightlike.Spacetime.CausalLadder.NullBoundaryManifold
import Lightlike.Spacetime.CausalLadder.FullSupportMeasure
import Lightlike.Spacetime.CausalLadder.TimeFunctionAssembly

/-!
# Causal simplicity implies stable causality

On a second-countable Hausdorff manifold modelled on `ℝⁿ` (`Fin n → ℝ`), a causally simple Lorentzian
manifold is stably causal (`isStablyCausal_of_isCausallySimple_euclid`). The time function is Hawking's
`x ↦ μ(J⁻(x))` for a finite measure `μ`, positive on nonempty open sets, with the null sets of the volume measure
(`exists_finite_fullSupport_measure`): `μ(J⁻(x))` is continuous
(`continuous_measure_causalPast`: upper semicontinuity from the closedness of `J⁺`, lower semicontinuity from
Fatou's lemma on the interior part `Ĩ⁻(x) = {a | J⁺(a) ∈ 𝓝 x}` of `J⁻(x)`), and the null horismos
`J⁻(x) \ Ĩ⁻(x)` lies in the frontier of the past set `J⁻(x)`, which is null (`volumeMeasure_horismos_eq_zero`: the
push-up lemmas give `a ∈ int J⁻(x) ⇒ x ∈ int J⁺(a)`; a cone argument in chart boxes gives a Lebesgue-null
frontier).

Source: Hawking–Ellis, *The Large Scale Structure of Space-Time*, ch. 6 (Hawking's time function from the
averaged volume of the past): not read at a location.
-/

open MeasureTheory Set Filter Topology Manifold
open scoped ContDiff ENNReal Manifold

namespace Lightlike.Causal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : TimeOrientation g)

/-- **Causal simplicity implies stable causality**, for manifolds modelled on `ℝⁿ` (with the Borel
`σ`-algebra). -/
theorem isStablyCausal_of_isCausallySimple_euclid (h : IsCausallySimple T) : IsStablyCausal T := by
  obtain ⟨ν, hfin, hpos, hνv, -⟩ := Lightlike.exists_finite_fullSupport_measure g
  exact isStablyCausal_of_null_horismos T ν hpos
    (fun x => hνv (volumeMeasure_horismos_eq_zero T x)) h

end Lightlike.Causal
